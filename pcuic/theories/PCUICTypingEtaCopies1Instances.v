(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of the typing copies over [typingE]

  Each instance below applies a lemma of the [typingE] copies of
  [Typing/PCUICWeakeningConfigTyp], [Typing/PCUICRenameTyp], [Typing/PCUICWeakeningTyp],
  [Typing/PCUICCasesWfTyp], [Typing/PCUICInstTyp] and [PCUICGuardClosure], or of the
  closedness lemmas added to [Typing/PCUICClosedTypEta], to a concrete case with
  every premise proved, so the premises are shown to be jointly satisfiable. The
  environments are [si_env] ([PCUICCumulativitySpecEtaClosureInstances]: one inductive
  [I (A : Prop) : Prop] with one constructor, well formed for [wf] and [wfE]), [sa_env]
  ([PCUICEtaA6Instances]: one constant, for [lift_declared_constantE]) and, for the
  guard, the environment [Σ] of [PCUICGuardCheckerRegress] with its guarded cofixpoint
  [zeros_block] and its structural fixpoint [fnat_block]. The last section types a
  [match] in [si_env] ([cp_match_typed]), so the case-analysis cases of the renaming and
  instantiation proofs and the case well-formedness lemmas are reached on a real
  [tCase]. Where a premise is a conversion or a context cumulativity, the instance
  relates an η-contraction ([cumulSpecE_eta_contract]) or a β-step. *)

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
From MetaRocq.PCUIC Require PCUICGuardCheckerRegress PCUICEtaA6Instances.
From MetaRocq.PCUIC Require Import PCUICClosed.

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

(** ** Further typing pieces in [si_Σ] *)

Lemma cp_vass_s (Γ : context) (na : aname) A s :
  si_Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typingE si_Σ Γ (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

(** [P] is a type, as an [on_type] judgement. *)
Lemma cp_P_onType (Γ : context) : wf_localE si_Σ Γ -> on_type (lift_typing typingE) si_Σ Γ si_P.
Proof.
  intros h. split; [exact tt|]. exists (Sort.super sProp).
  split; [exact (cp_P_typed Γ h)|]. split; exact I.
Qed.

(** A variable of type [P]. *)
Lemma cp_rel_P (Γ : context) n d :
  wf_localE si_Σ Γ -> nth_error Γ n = Some d -> decl_type d = si_P ->
  si_Σ ;;; Γ |-E tRel n : tSort sProp.
Proof. intros h hn hd. refine (meta_convE (typeE_Rel _ _ n d h hn) _). now rewrite hd. Qed.

Lemma cp_type1_typed : si_Σ ;;; [] |-E tSort Sort.type1 : tSort (Sort.super Sort.type1).
Proof.
  apply typeE_Sort; [constructor|].
  cbn. intros l hin%LevelExprSet.singleton_spec. subst l. cbn.
  apply global_ext_levels_InSet.
Qed.

(** [I : P -> P]. *)
Lemma cp_ind_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
Proof.
  intros h. refine (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive _).
  reflexivity.
Qed.

Lemma cp_arity_typedE (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod.
  - exact (cp_vass_s Γ si_na si_P _ (cp_P_typed Γ h) eq_refl).
  - apply typeE_Sort; [exact (cp_wf_P Γ h)|cbn; trivial].
Qed.

Definition cp_Ix (k : nat) : term := tApp (tInd si_ind []) (tRel k).

(** [I x : P] when [x : P]. *)
Lemma cp_Ix_typed (Γ : context) k : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tRel k : tSort sProp ->
  si_Σ ;;; Γ |-E cp_Ix k : tSort sProp.
Proof.
  intros h hk.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ (tRel k)
           (cp_arity_typedE Γ h) (cp_ind_typed Γ h) hk).
Qed.

(** The constructor [c : Π A : P. I A]. *)
Lemma cp_cstr_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] : tProd si_na si_P (cp_Ix 0).
Proof.
  intros h. refine (typeE_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl h si_declared_constructor _).
  reflexivity.
Qed.

Lemma cp_cstr_prod_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tProd si_na si_P (cp_Ix 0) : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. apply typeE_Prod.
  - exact (cp_vass_s Γ si_na si_P _ (cp_P_typed Γ h) eq_refl).
  - apply cp_Ix_typed; [exact (cp_wf_P Γ h)|].
    exact (cp_rel_P _ 0 (vass si_na si_P) (cp_wf_P Γ h) eq_refl eq_refl).
Qed.

(** ** Meta-conversion and renaming ([Typing/PCUICRenameTypEta]) *)

Definition meta_conv_termE_inst :=
  @meta_conv_termE _ si_Σ cp_Γ1 (tRel 0) (lift0 0 (tRel 0)) _ cp_rel0_typed eq_refl.

Definition meta_conv_allE_inst :=
  @meta_conv_allE _ si_Σ cp_Γ1 (tRel 0) (lift0 1 si_P) (cp_Γ1 ,,, []) (lift0 0 (tRel 0)) (lift0 1 si_P)
    cp_rel0_typed eq_refl eq_refl eq_refl.

(** The same renaming under another, pointwise equal, predicate. *)
Lemma cp_shiftnP_closedP : shiftnP 1 xpred0 =1 closedP 1 xpredT.
Proof. intros i. cbv [shiftnP closedP]. destruct (Nat.ltb i 1); reflexivity. Qed.

Definition renamingE_extP_inst :=
  renamingE_extP (shiftnP 1 xpred0) (closedP 1 xpredT) si_Σ cp_Γ1 cp_Γ2 (rshiftk 1)
    cp_shiftnP_closedP cp_renamingE.

Definition renaming_vassE_inst :=
  renaming_vassE (shiftnP 1 xpred0) si_Σ cp_Γ1 cp_Γ2 si_na si_P (rshiftk 1)
    (cp_wf_P cp_Γ2 cp_wf_Γ2) cp_renamingE.

(** [cp_Γ2] extended by a definition [z := y : P]. *)
Lemma cp_wf_vdef2 : wf_localE si_Σ (cp_Γ2 ,, vdef si_na (tRel 1) si_P).
Proof.
  apply localenv_cons_def; [exact cp_wf_Γ2|].
  split; [exact (cp_rel_P cp_Γ2 1 (vass si_na si_P) cp_wf_Γ2 eq_refl eq_refl)|].
  exists (Sort.super sProp). split; [exact (cp_P_typed cp_Γ2 cp_wf_Γ2)|].
  split; [exact I|reflexivity].
Qed.

Definition renaming_vdefE_inst :=
  renaming_vdefE (shiftnP 1 xpred0) si_Σ cp_Γ1 cp_Γ2 si_na (tRel 0) si_P (rshiftk 1)
    cp_wf_vdef2 cp_renamingE.

(** Renaming carries the typing of a declaration [_ : P] added after [cp_Γ1]. *)
Lemma wf_local_app_renamingE_inst :
  wf_localE si_Σ (cp_Γ2 ,,, rename_context (rshiftk 1) [vass si_na si_P]).
Proof.
  refine (wf_local_app_renamingE xpred0 si_Σ cp_Γ1 [vass si_na si_P] _ cp_Γ2 (rshiftk 1) cp_renamingE).
  apply localenv_cons_abs; [constructor|].
  intros P0 Δ0 f0 [hΔ0 _].
  split; [exact tt|]. exists (Sort.super sProp).
  split; [exact (cp_P_typed Δ0 hΔ0)|]. split; [exact I|reflexivity].
Qed.

(** ** Weakening ([Typing/PCUICWeakeningTypEta]) *)

Definition weakening_wf_local_eqE_inst :=
  weakening_wf_local_eqE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := cp_Γ1) (Γ' := [vass si_na si_P])
    (Γ'' := [vass si_na si_P]) (n := 1) cp_wf_Γ2 cp_wf_Γ2 eq_refl.

Definition weaken_wf_localE_inst :=
  PCUICWeakeningTypEta.weaken_wf_localE (Σ := si_Σ) (Δ := [vass si_na si_P]) cp_Γ1 si_wfE cp_wf_Γ1
    (cp_wf_P [] localenv_nil).

Definition weakening_lengthE_inst :=
  weakening_lengthE si_Σ cp_Γ1 [vass si_na si_P] (tRel 0) (lift0 1 si_P) 1 si_wfE eq_refl cp_wf_Γ2
    cp_rel0_typed.

Definition weaken_ctxE_inst :=
  weaken_ctxE (Σ := si_Σ) [vass si_na si_P] si_wfE (cp_wf_P [] localenv_nil) cp_rel0_typed.

Definition weakening_genE_inst :=
  weakening_genE _ si_Σ cp_Γ1 [vass si_na si_P] (tRel 0) (lift0 1 si_P) 1 eq_refl si_wfE cp_wf_Γ2
    cp_rel0_typed.

Definition shift_typingE_inst :=
  shift_typingE (Σ := si_Σ) (wfΣ := si_wfE) (Δ := [vass si_na si_P]) cp_rel0_typed cp_wf_Γ2 eq_refl.

Definition cp_P_vass1 := cp_vass cp_Γ1 si_na si_P _ (cp_P_typed cp_Γ1 cp_wf_Γ1) eq_refl.

Definition lift_typing_weakeningE_inst :=
  lift_typing_weakeningE si_Σ cp_Γ1 [vass si_na si_P] (j_vass si_na si_P) si_wfE cp_wf_Γ2 cp_P_vass1.

Definition lift_typing_weaken_ctxE_inst :=
  lift_typing_weaken_ctxE si_Σ cp_Γ1 [vass si_na si_P] (j_vass si_na si_P) si_wfE
    (cp_wf_P [] localenv_nil) cp_P_vass1.

Definition lift_typing_weakening_skipnE_inst :=
  lift_typing_weakening_skipnE (Σ := si_Σ) (n := 1) (Γ := cp_Γ2) (j := j_vass si_na si_P)
    (le_S 1 1 (le_n 1)) si_wfE cp_wf_Γ2 cp_P_vass1.

Definition All_local_env_nth_error_weakenE_inst :=
  All_local_env_nth_error_weakenE (Σ := si_Σ) (Γ := cp_Γ2) (n := 1) (decl := vass si_na si_P)
    si_wfE cp_wf_Γ2 eq_refl.

Definition isType_liftE_inst :=
  isType_liftE (Σ := si_Σ) (n := 1) (Γ := cp_Γ2) (ty := si_P) (le_S 1 1 (le_n 1)) si_wfE cp_wf_Γ2
    (cp_P_onType cp_Γ1 cp_wf_Γ1).

Definition isTypeRel_liftE_inst :=
  isTypeRel_liftE (Σ := si_Σ) (n := 1) (Γ := cp_Γ2) (ty := si_P) (r := Relevant) (le_S 1 1 (le_n 1))
    si_wfE cp_wf_Γ2 cp_P_vass1.

(** A one-function block [fix f : P := f]: its type is a type and its body is typed. *)
Definition cp_tblock : mfixpoint term :=
  [{| dname := si_na; dtype := si_P; dbody := tRel 0; rarg := 0 |}].

Definition cp_tblock_type := cp_vass [] si_na si_P _ (cp_P_typed [] localenv_nil) eq_refl.

Lemma cp_tblock_body :
  on_def_body (lift_typing typingE si_Σ) (fix_context cp_tblock) []
    {| dname := si_na; dtype := si_P; dbody := tRel 0; rarg := 0 |}.
Proof.
  split; [exact cp_rel0_typed|]. exists (Sort.super sProp).
  split; [exact (cp_P_typed cp_Γ1 cp_wf_Γ1)|]. split; [exact I|reflexivity].
Qed.

Lemma cp_tblock_types :
  All (fun d : def term => on_type_rel (lift_typing typingE) si_Σ [] (dtype d) (binder_relevance (dname d)))
    cp_tblock.
Proof. constructor; [exact cp_tblock_type|constructor]. Qed.

Lemma cp_tblock_ontypes : All (on_def_type (lift_typing typingE si_Σ) []) cp_tblock.
Proof. constructor; [exact cp_tblock_type|constructor]. Qed.

Lemma cp_tblock_onbodies : All (on_def_body (lift_typing typingE si_Σ) (fix_context cp_tblock) []) cp_tblock.
Proof. constructor; [exact cp_tblock_body|constructor]. Qed.

Definition All_mfix_wfE_inst :=
  All_mfix_wfE si_Σ [] cp_tblock si_wfE localenv_nil cp_tblock_types.

Lemma lift_declared_constantE_inst :
  PCUICEtaA6Instances.sa_cb = map_constant_body (lift 1 0) PCUICEtaA6Instances.sa_cb.
Proof.
  exact (lift_declared_constantE PCUICEtaA6Instances.sa_env PCUICEtaA6Instances.sa_kn
           PCUICEtaA6Instances.sa_cb 1 0 (wf_incl_E PCUICEtaA6Instances.sa_wf)
           PCUICEtaA6Instances.sa_declared).
Qed.

(** ** Case well-formedness ([Typing/PCUICCasesWfTypEta]) *)

Lemma typingE_closedn_mfix_inst : closedn_mfix #|@nil context_decl| cp_tblock.
Proof.
  exact (typingE_closedn_mfix (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (mfix := cp_tblock)
           cp_tblock_ontypes cp_tblock_onbodies).
Qed.

(** ** Well-typed substitutions ([Typing/PCUICInstTypEta]) *)

Definition well_subst_extE_inst :=
  well_subst_extE si_Σ [] cp_σ (fun n => cp_σ n) cp_sΔ (cp_well_substE si_Σ) (fun n => eq_refl).

Definition well_subst_usubstE_inst :=
  well_subst_usubstE si_Σ si_wfE cp_sΔ cp_σ [] eq_refl (cp_well_substE si_Σ).

Definition well_subst_closed_substE_inst :=
  well_subst_closed_substE si_Σ si_wfE cp_sΔ cp_σ [] eq_refl (cp_well_substE si_Σ).

(** The definition [z := P : Type₁], well formed in the empty context. *)
Lemma cp_wf_vdef0 : wf_localE si_Σ [vdef si_na si_P (tSort Sort.type1)].
Proof.
  apply localenv_cons_def; [constructor|].
  split; [exact (typeE_Prop si_Σ)|]. exists (Sort.super Sort.type1).
  split; [exact cp_type1_typed|]. split; [exact I|reflexivity].
Qed.

Definition well_subst_Up'E_inst :=
  well_subst_Up'E (Σ := si_Σ) (wfΣ := si_wfE) (Γ := cp_sΔ) (Δ := []) (σ := cp_σ) (na := si_na)
    (t := si_P) (A := tSort Sort.type1) cp_wf_vdef0 (cp_well_substE si_Σ).

Definition well_subst_appE_inst :=
  well_subst_appE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := cp_sΔ) (Δ := []) (σ := cp_σ)
    (Δ' := [vass si_na si_P]) cp_wf_Γ1 (cp_well_substE si_Σ).

Definition well_subst_app_upE_inst :=
  well_subst_app_upE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := cp_sΔ) (Δ := []) (σ := cp_σ)
    (Δ' := [vass si_na si_P]) cp_wf_Γ1 (cp_well_substE si_Σ).

(** Instantiation carries the typing of a declaration [_ : P] added after [cp_sΔ]. *)
Lemma wf_local_app_instE_inst : wf_localE si_Σ ([] ,,, inst_context cp_σ [vass si_na si_P]).
Proof.
  refine (wf_local_app_instE (wfΣ := si_wfE) si_Σ cp_sΔ [vass si_na si_P] _ [] cp_σ
            (cp_well_substE si_Σ) localenv_nil).
  apply localenv_cons_abs; [constructor|].
  intros Δ0 σ0 hΔ0 _.
  split; [exact tt|]. exists (Sort.super sProp).
  split; [exact (cp_P_typed Δ0 hΔ0)|]. split; [exact I|reflexivity].
Qed.

(** ** Closedness of types and declarations ([Typing/PCUICClosedTypEta]) *)

Lemma si_isType_closedE : closedn #|cp_Γ1| si_P.
Proof. exact (@isType_closedE _ si_Σ si_wfE _ _ (cp_P_onType cp_Γ1 cp_wf_Γ1)). Qed.

Lemma si_isType_is_open_termE : is_open_term cp_Γ1 si_P.
Proof. exact (@isType_is_open_termE _ si_Σ si_wfE _ _ (cp_P_onType cp_Γ1 cp_wf_Γ1)). Qed.

Lemma si_isTypeRel_is_open_termE : is_open_term cp_Γ1 si_P.
Proof. exact (@isTypeRel_is_open_termE _ si_Σ si_wfE _ _ _ cp_P_vass1). Qed.

Lemma si_declared_inductive_closed_constructorsE : All (closed_constructor_body si_mdecl) si_idecl.(ind_ctors).
Proof. exact (@declared_inductive_closed_constructorsE _ si_Σ _ _ _ si_wfE si_declared_inductive). Qed.

Lemma si_declared_constructor_closed_argsE :
  closedn_ctx (#|ind_bodies si_mdecl| + #|ind_params si_mdecl|) si_cdecl.(cstr_args).
Proof. exact (@declared_constructor_closed_argsE _ si_Σ _ _ _ _ si_wfE si_declared_constructor). Qed.

Lemma si_declared_constructor_closed_indicesE :
  forallb (closedn (#|ind_bodies si_mdecl| + #|ind_params si_mdecl| + #|cstr_args si_cdecl|))
    si_cdecl.(cstr_indices).
Proof. exact (@declared_constructor_closed_indicesE _ si_Σ _ _ _ _ si_wfE si_declared_constructor). Qed.

(** ** The guard of a fixpoint ([PCUICGuardClosureEta]) *)

(** [fix f (n : nat) : nat := match n with O => O | S k => f k end] passes the executable
    check in the empty context. *)
Definition cp_fnat : mfixpoint term := PCUICGuardCheckerRegress.fnat_block.

Lemma cp_fnat_check_ok : check_ok Fix cp_gΣ [] cp_fnat.
Proof. split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity. Qed.

Lemma cp_fnat_guarded : guard_cl Fix cp_gΣ cp_gΓ cp_fnat.
Proof. apply (guard_cl_context Fix cp_gΣ []). apply gc_check, cp_fnat_check_ok. Qed.

Lemma fix_guard_context_cumulativityE_inst : guard Fix cp_gΣ cp_gΓ' cp_fnat.
Proof. exact (fix_guard_context_cumulativityE cp_gΣ cp_gΓ cp_gΓ' cp_fnat cp_ctx_cumul cp_fnat_guarded). Qed.

Lemma fix_guard_instE_inst : guard Fix cp_gΣ [] (inst_mfix cp_fnat cp_σ).
Proof.
  eapply (fix_guard_instE cp_gΣ [] cp_sΔ cp_fnat cp_σ (cp_well_substE cp_gΣ)).
  - vm_compute. reflexivity.
  - intros x hx. destruct x as [|x]; [reflexivity|cbn in hx; lia].
  - apply (guard_cl_context Fix cp_gΣ []). apply gc_check, cp_fnat_check_ok.
Qed.

(** ** A typed [match] in [si_Σ]

  In the context [x : P], the term [match c x as z in I x return I x with c => c x end]:
  the parameter is [x], the predicate context is the inductive's own, the return type is
  [I x], and the single branch returns [c x] at the branch type [(λ z : I x. I x) (c x)],
  which a β-step relates to [I x]. *)

Definition cp_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant |}.
Definition cp_mp : predicate term :=
  {| pparams := [tRel 0]; puinst := []; pcontext := ind_predicate_context si_ind si_mdecl si_idecl;
     preturn := cp_Ix 1 |}.
Definition cp_disc : term := tApp (tConstruct si_ind 0 []) (tRel 0).
Definition cp_br : branch term := {| bcontext := []; bbody := cp_disc |}.
Definition cp_match : term := tCase cp_ci cp_mp cp_disc [cp_br].
Definition cp_zna : aname := {| binder_name := nNamed (ind_name si_idecl); binder_relevance := Relevant |}.

Lemma cp_wf_mp : wf_predicate si_mdecl si_idecl cp_mp.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma cp_wf_br : wf_branch si_cdecl cp_br.
Proof. constructor. Qed.

Lemma cp_Ix0_typed : si_Σ ;;; cp_Γ1 |-E cp_Ix 0 : tSort sProp.
Proof.
  apply cp_Ix_typed; [exact cp_wf_Γ1|].
  exact (cp_rel_P cp_Γ1 0 (vass si_na si_P) cp_wf_Γ1 eq_refl eq_refl).
Qed.

(** [cp_Γ1] extended by the predicate context [z : I x]. *)
Lemma cp_wf_pctx : wf_localE si_Σ (cp_Γ1 ,, vass cp_zna (cp_Ix 0)).
Proof.
  apply localenv_cons_abs; [exact cp_wf_Γ1|].
  exact (cp_vass cp_Γ1 cp_zna (cp_Ix 0) sProp cp_Ix0_typed eq_refl).
Qed.

Lemma cp_pret_typed : si_Σ ;;; cp_Γ1 ,, vass cp_zna (cp_Ix 0) |-E cp_Ix 1 : tSort sProp.
Proof.
  apply cp_Ix_typed; [exact cp_wf_pctx|].
  exact (cp_rel_P _ 1 (vass si_na si_P) cp_wf_pctx eq_refl eq_refl).
Qed.

Lemma cp_disc_typed : si_Σ ;;; cp_Γ1 |-E cp_disc : cp_Ix 0.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (cp_Ix 0) _ (tRel 0)
           (cp_cstr_prod_typed cp_Γ1 cp_wf_Γ1) (cp_cstr_typed cp_Γ1 cp_wf_Γ1)
           (cp_rel_P cp_Γ1 0 (vass si_na si_P) cp_wf_Γ1 eq_refl eq_refl)).
Qed.

Lemma cp_ctx_inst : ctx_inst (typingE si_Σ) cp_Γ1 [tRel 0] [vass si_na si_P].
Proof.
  econstructor; [|constructor].
  exact (cp_rel_P cp_Γ1 0 (vass si_na si_P) cp_wf_Γ1 eq_refl eq_refl).
Qed.

(** The branch type [(λ z : I x. I x) (c x)] is a proposition. *)
Lemma cp_bty_typed :
  si_Σ ;;; cp_Γ1 |-E tApp (tLambda cp_zna (cp_Ix 0) (cp_Ix 1)) cp_disc : tSort sProp.
Proof.
  refine (typeE_App _ _ (tLambda cp_zna (cp_Ix 0) (cp_Ix 1)) cp_zna (cp_Ix 0) (tSort sProp) _ cp_disc
            _ _ cp_disc_typed).
  - apply typeE_Prod.
    + exact (cp_vass_s cp_Γ1 cp_zna (cp_Ix 0) sProp cp_Ix0_typed eq_refl).
    + apply typeE_Sort; [exact cp_wf_pctx|cbn; trivial].
  - apply typeE_Lambda.
    + exact (cp_vass cp_Γ1 cp_zna (cp_Ix 0) sProp cp_Ix0_typed eq_refl).
    + exact cp_pret_typed.
Qed.

(** The branch body [c x] has the branch type, by a β-step. *)
Lemma cp_br_typed :
  si_Σ ;;; cp_Γ1 |-E cp_disc : tApp (tLambda cp_zna (cp_Ix 0) (cp_Ix 1)) cp_disc.
Proof.
  refine (typeE_Cumul _ _ cp_disc (cp_Ix 0) _ sProp cp_disc_typed cp_bty_typed _).
  apply cumulE_Sym. exact (cumulE_beta _ _ Conv cp_zna (cp_Ix 0) (cp_Ix 1) cp_disc).
Qed.

Lemma cp_case_side :
  case_side_conditions (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) si_Σ cp_Γ1 cp_ci cp_mp sProp
    si_mdecl si_idecl [] (case_predicate_context si_ind si_mdecl si_idecl cp_mp).
Proof.
  constructor.
  - reflexivity.
  - exact cp_wf_mp.
  - reflexivity.
  - exact cp_wf_pctx.
  - exact (alpha_eq_reflexive (pcontext cp_mp)).
  - reflexivity.
  - reflexivity.
  - exact cp_ctx_inst.
  - reflexivity.
Qed.

Lemma cp_case_brs :
  case_branch_typing (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) cp_Γ1 cp_ci cp_mp sProp si_mdecl si_idecl
    (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl cp_mp) (preturn cp_mp))
    [cp_br].
Proof.
  constructor.
  - constructor; [exact cp_wf_br|constructor].
  - constructor; [|constructor].
    split; [constructor|]. cbv zeta. split; [|split].
    + exact cp_wf_Γ1.
    + exact cp_br_typed.
    + exact cp_bty_typed.
Qed.

Definition cp_match_ty : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl cp_mp) (preturn cp_mp))
    ([] ++ [cp_disc]).

Lemma cp_match_typed : si_Σ ;;; cp_Γ1 |-E cp_match : cp_match_ty.
Proof.
  eapply (typeE_Case _ _ cp_ci cp_mp cp_disc [cp_br] [] sProp si_mdecl si_idecl).
  - exact si_declared_inductive.
  - exact cp_pret_typed.
  - exact cp_disc_typed.
  - exact cp_case_side.
  - exact cp_case_brs.
Qed.

(** [type_Case_wf_casesE]: the side conditions of the match give its node of [wf_cases]. *)
Lemma type_Case_wf_casesE_inst : wf_case_node si_env cp_ci cp_mp [cp_br].
Proof.
  exact (type_Case_wf_casesE (Σ := si_Σ) (wfΣ := si_wfE) (ci := cp_ci) si_declared_inductive
           cp_case_side cp_case_brs).
Qed.

(** [subject_wf_casesE] on the match: a real [tCase] node. *)
Lemma subject_wf_casesE_match_inst : wf_cases si_env cp_match.
Proof. exact (@subject_wf_casesE _ si_Σ si_wfE _ _ _ cp_match_typed). Qed.

(** The substitution [x ↦ x, z ↦ match …] from [x : P, z : (type of the match)] to
    [x : P]; [well_substE_wf_cases] then reads the match. *)
Definition cp_mσ : nat -> term := cp_match ⋅ ids.
Definition cp_mΓ : context := cp_Γ1 ,, vass cp_zna cp_match_ty.

Lemma cp_well_substE_match : well_substE si_Σ cp_mΓ cp_mσ cp_Γ1.
Proof.
  split.
  - intros x decl hx. destruct x as [|[|x]]; cbn in hx; [| |destruct x; discriminate].
    + injection hx as <-. exact cp_match_typed.
    + injection hx as <-. exact (cp_rel_P cp_Γ1 0 (vass si_na si_P) cp_wf_Γ1 eq_refl eq_refl).
  - intros x decl hx. destruct x as [|[|x]]; cbn in hx; [| |destruct x; discriminate];
      injection hx as <-; intros b hb; discriminate hb.
Qed.

Lemma well_substE_wf_cases_match_inst : wf_cases si_Σ.1 (cp_mσ 0).
Proof.
  exact (@well_substE_wf_cases _ si_Σ si_wfE _ _ _ cp_well_substE_match 0 ltac:(cbn; lia)).
Qed.

(** Renaming the match: reaches the case-analysis case of [typing_rename_propE], with
    [wf_local_app_renamingE] on the predicate and branch contexts. *)
Definition typing_renameE_match_inst :=
  typing_renameE (Σ := si_Σ) si_wfE cp_wf_Γ2 (urenaming_lift0 _ cp_Γ1 [vass si_na si_P]) cp_match_typed.

(** [∀ A : P. A], a proposition, substituted for [x]. *)
Definition cp_pσ : nat -> term := tProd si_na si_P (tRel 0) ⋅ ids.

Lemma cp_all_typed : si_Σ ;;; [] |-E tProd si_na si_P (tRel 0) : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  apply typeE_Prod.
  - exact (cp_vass_s [] si_na si_P _ (cp_P_typed [] localenv_nil) eq_refl).
  - exact (cp_rel_P _ 0 (vass si_na si_P) (cp_wf_P [] localenv_nil) eq_refl eq_refl).
Qed.

Lemma cp_well_substE_all : well_substE si_Σ cp_Γ1 cp_pσ [].
Proof.
  split.
  - intros x decl hx. destruct x as [|x]; cbn in hx; [|destruct x; discriminate].
    injection hx as <-. exact cp_all_typed.
  - intros x decl hx. destruct x as [|x]; cbn in hx; [|destruct x; discriminate].
    injection hx as <-. intros b hb. discriminate hb.
Qed.

(** Instantiating the match: reaches the case-analysis case of [type_instE], with
    [wf_local_app_instE] on the predicate and branch contexts. *)
Definition typing_instE_match_inst :=
  typing_instE si_Σ cp_Γ1 cp_match cp_match_ty [] cp_pσ (wfΣ := si_wfE) localenv_nil cp_well_substE_all
    cp_match_typed.

(** ** The lemmas of [Conversion/PCUICInstConv] and [Typing/PCUICRenameTyp] on the match's data *)

Definition rename_case_branch_typeE_inst :=
  rename_case_branch_typeE (Σ := si_Σ) (wfΣ := si_wfE) (rshiftk 1) cp_ci si_mdecl si_idecl cp_mp cp_br 0
    si_cdecl si_declared_inductive cp_wf_mp cp_wf_br.

Definition inst_case_predicate_contextE_inst :=
  inst_case_predicate_contextE (Σ := si_Σ) (wfΣ := si_wfE) (f := cp_pσ) si_declared_inductive cp_wf_mp.

Definition closedn_ctx_cstr_branch_contextE_inst :=
  closedn_ctx_cstr_branch_contextE (Σ := si_Σ) (wfΣ := si_wfE) si_declared_constructor.

Definition inst_case_branch_context_genE_inst :=
  inst_case_branch_context_genE (Σ := si_Σ) (wfΣ := si_wfE) (f := cp_pσ) (p := cp_mp) (bctx := [])
    si_declared_constructor eq_refl eq_refl.

Definition inst_case_branch_typeE_inst :=
  inst_case_branch_typeE (Σ := si_Σ) (wfΣ := si_wfE) cp_pσ cp_ci 0 si_mdecl si_idecl cp_mp cp_br si_cdecl
    si_declared_constructor cp_wf_mp cp_wf_br.
