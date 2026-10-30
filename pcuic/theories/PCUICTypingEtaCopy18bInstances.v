(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICInductiveInversionEtaB]

  Each of the 58 premise-carrying lemmas of [PCUICInductiveInversionEtaB] is applied here to a
  concrete instance with every premise proved. The file's refutation
  [ws_cumul_pb_terms_conflE_false] has no instance: it states that its premise is
  unsatisfiable, so no instance of it exists. The environments are the ones copy 18a uses:
  - [rf_Σ] of [PCUICWsCumulEtaCtx] (the empty environment) with the context
    [wc_Γ := [G : (Prop → Prop) → Prop; F : Prop → Prop]], in which [wc_T := G (λy:Prop. F y)]
    and [wc_U := G F] are related by one η step and by no reduction or syntactic comparison.
  - [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
    ([Inductive I (A : Prop) : Prop := c : ∀ A:Prop. I A], finite, one parameter), with the
    context [iv_Γk := [y : k g; k : (Prop → Prop) → Prop; g : Prop → Prop]] of
    [PCUICInversionEtaInstances], in which [y] is typed at [k (λx:Prop. g x)] only through
    one η step ([iv_rel_typed]). The [match] and the fixpoint of this file live there.
  - [iv_Σ] of [PCUICInversionEtaInstances] ([CoInductive R (A : Prop) : Prop := mkR { f : A }]),
    with the same context and copy 18a's telescope [c18_tel], whose last entry [w : h y] is
    typed only through that η step, so that EVERY typing in [c18_tel] carries an η step in
    the [wf_localE] it holds. The cofixpoint, the projection and the constructor applications
    live there.

  [if_Σ] of [PCUICConversionEtaCongrFinst] and [J@{i}] of [PCUICEtaIdxEnv] are NOT USED by this
  file: no instance here reaches a universe comparison, because every instance runs at the
  monomorphic instance [u = []] of a monomorphic declaration. The rows that a polymorphic
  environment would reach are tagged NOT BUILT (the universe part) below.

  Every instance that does not reach the whole of a lemma carries a mark. IMPOSSIBLE names a
  premise that cannot hold an η step, with the property of the head and the rule set that
  refutes it; a premise is IMPOSSIBLE only when the refutation rests on the premise's own rule
  set (a lookup, a universe statement, a Leibniz equality, an alpha equality on binder names).
  NOT BUILT names a premise that this file's environments do not reach, with the missing
  witness and its cost. Three costs recur:
  - the [wfE Σ] part: [wfE Σ] is [on_global_env cumulSpecE0 (lift_typing typingE)], so it holds
    the typing derivation of EVERY declaration of [Σ] and CAN carry an η step. The three
    environments of this file ([rf_Σ], [si_Σ], [iv_Σ]) are typed without one. Cost: a
    declaration whose type or body is typed through an η step, in a new environment, with its
    [wfE] proof;
  - the universe part: cost is a universe-polymorphic declaration, two instances of it, its
    environment and its [wfE] proof;
  - the substitution part: cost is a well-typed non-empty substitution whose terms are the two
    sides of an η step, with its [subsletE]. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICReduction
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICContextSubst PCUICSigmaCalculus PCUICClosedBodies
     PCUICWellScopedCumulativity PCUICConversion PCUICWeakeningEnv
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta
     PCUICTypingEtaNotions PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICConversionEtaCongr
     PCUICConversionEtaCongrFinst
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICEtaI5 PCUICEtaJoinSpec
     PCUICGuardClosure PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSpineEta PCUICInductivesEta PCUICInductiveInversionEta
     PCUICTypingEtaCopy18aInstances
     PCUICInductiveInversionEtaB.
(* [PCUICEtaIdxEnv] is not required: no name of it is used here. *)
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

Definition c18b_rf_cb : ClosedBodies rf_Σ := @wfE_ClosedBodies _ rf_Σ wc_wfE.
Definition c18b_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.
#[local] Existing Instance c18b_rf_cb.
#[local] Existing Instance c18b_iv_cb.
#[local] Existing Instance si_cb.

(** ** The η kit

  [k g] and [k (λx:Prop. g x)] in [iv_Γk], in any environment, and the two contexts whose
  well-formedness holds the η step. *)

(** One [cumul_eta_l] step under [k], in any environment and any context. *)
Lemma c18b_spec_eta (Σ : global_env_ext) (Γ : context) pb : Σ ;;; Γ ⊢ iv_kg ≤sE[pb] iv_keta.
Proof.
  apply convSpecE_cumulSpecE. unfold iv_kg, iv_keta, iv_eta_g.
  apply cumulE_App; [apply cumulE_Refl|]. apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
Qed.

Lemma c18b_closed_Γk : is_closed_context iv_Γk. Proof. reflexivity. Qed.
Lemma c18b_kg_open : is_open_term iv_Γk iv_kg. Proof. reflexivity. Qed.
Lemma c18b_keta_open : is_open_term iv_Γk iv_keta. Proof. reflexivity. Qed.

Lemma c18b_ws_eta (Σ : global_env_ext) {cb : ClosedBodies Σ} pb :
  ws_cumul_pbE pb Σ iv_Γk iv_kg iv_keta.
Proof.
  exact (into_ws_cumul_pbE_spec (c18b_spec_eta Σ iv_Γk pb) c18b_closed_Γk c18b_kg_open c18b_keta_open).
Qed.

Lemma c18b_join_conv : JoinE si_Σ iv_Γk Conv iv_kg iv_keta.
Proof. exact (wsE_join (c18b_ws_eta si_Σ Conv)). Qed.

(** *** The η context in [iv_Σ]: copy 18a's telescope

  [g; k; y : k g; h : (Π x : k (λx:Prop. g x). Prop); w : h y]. The last entry is typed only
  through the η step, so every typing in this context carries one. *)
Definition c18b_Γ : context := c18_tel.

Lemma c18b_wf : wf_localE iv_Σ c18b_Γ.
Proof. exact (c18_tel_wf [] localenv_nil). Qed.

(** *** The η context in [si_Σ]: a let whose body is typed only through the η step

  [g; k; y : k g; z := y : k (λx:Prop. g x)]. *)
Definition c18b_sΓ : context := iv_Γk ,, vdef si_na (tRel 0) iv_keta.

Lemma c18b_swf : wf_localE si_Σ c18b_sΓ.
Proof.
  apply localenv_cons_def; [exact iv_wf_Γk|].
  exact (iv_vdef si_Σ iv_Γk si_na (tRel 0) iv_keta sProp iv_rel_typed iv_keta_typed Logic.eq_refl).
Qed.

(** [∀P:Prop. P] and [R (∀P:Prop. P)] in the η context of [iv_Σ]. *)
Lemma c18b_False_typed : iv_Σ ;;; c18b_Γ |-E iv_False : si_P.
Proof. exact (iv_False_typed iv_Σ c18b_Γ c18b_wf). Qed.

Lemma c18b_isT_False : isTypeE iv_Σ c18b_Γ iv_False.
Proof. exact (has_sort_isTypeE _ c18b_False_typed). Qed.

Lemma c18b_RF_typed : iv_Σ ;;; c18b_Γ |-E iv_RF : si_P.
Proof. exact (iv_RF_typed c18b_Γ c18b_wf). Qed.

Lemma c18b_isT_RF : isTypeE iv_Σ c18b_Γ iv_RF.
Proof. exact (has_sort_isTypeE _ c18b_RF_typed). Qed.

Lemma c18b_isT_P : isTypeE iv_Σ c18b_Γ si_P.
Proof. exact (has_sort_isTypeE _ (iv_P_typed iv_Σ c18b_Γ c18b_wf)). Qed.

(** [R (k g)] and the η relation [R (k (λx:Prop. g x)) ≤ R (k g)] of copy 18a. *)
Lemma c18b_isT_Rkg : isTypeE iv_Σ iv_Γk (iv_R iv_kg).
Proof. exact (has_sort_isTypeE _ (iv_RX_typed iv_Γk iv_kg c18_wf_Γk c18_kg_typed)). Qed.

(** The parameter spine [[X]] of [R] over any well-formed context. *)
Definition c18b_sp (Γ : context) (X : term) (wfΓ : wf_localE iv_Σ Γ)
  (hX : iv_Σ ;;; Γ |-E X : si_P) :
  spine_substE iv_Σ Γ [X] [X] (subst_instance [] (ind_params iv_mdecl)).
Proof.
  constructor.
  - exact wfΓ.
  - exact (iv_wf_P iv_Σ Γ wfΓ).
  - exact (context_subst_ass [] [] [] si_na si_P X context_subst_nil).
  - exact (subslet_ass_tipE hX).
Defined.

(** ** The instances, in the order of the file *)

(* NOT BUILT (the universe part): the instance is at [u = []] of the monomorphic [R], so
   [consistent_instance_ext] holds by [reflexivity] and no instance comparison is reached.
   The context is the η telescope: the [wf_localE] premise holds the η step of [w : h y]. *)
Definition isType_of_constructorE_inst :=
  isType_of_constructorE iv_Σ iv_mdecl iv_idecl iv_cdecl (iv_ind, 0) [] c18b_Γ
    iv_wfE c18b_wf iv_declared_constructor c18_cu.

(** The join is the η step [k g ≡ k (λx:Prop. g x)]. *)
Definition conv_eq_ctxE_inst :=
  conv_eq_ctxE si_Σ iv_Γk iv_Γk iv_kg iv_keta c18b_join_conv Logic.eq_refl.

(* NOT BUILT (the universe part), as [isType_of_constructorE_inst]: the instance is at
   [u = []]. The context premise is the η telescope. *)
Definition declared_constructor_valid_tyE_inst :=
  declared_constructor_valid_tyE iv_Σ c18b_Γ iv_mdecl iv_idecl iv_ind 0 iv_cdecl []
    iv_wfE c18b_wf iv_declared_constructor c18_cu.

Lemma c18b_open_Rketa : is_open_term iv_Γk (iv_R iv_keta). Proof. reflexivity. Qed.
Lemma c18b_open_Rkg : is_open_term iv_Γk (iv_R iv_kg). Proof. reflexivity. Qed.

(** The spine is the empty one, and its conversion is the η step
    [R (k (λx:Prop. g x)) ≤ R (k g)]. *)
Definition typing_spine_it_mkProd_Ind_invE_inst :=
  typing_spine_it_mkProd_Ind_invE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk)
    (MetaRocq.PCUIC.PCUICAritiesEta.type_spine_nilE _ _ (iv_R iv_keta) (iv_R iv_kg) c18_isT_Rketa c18b_isT_Rkg c18_R_η)
    [] iv_ind [] [iv_keta] iv_ind [] [iv_kg]
    (ws_cumul_pbE_refl (Σ := iv_Σ) (pb := Cumul) c18b_closed_Γk c18b_open_Rketa) Logic.eq_refl.

(** ** The fixpoint of [PCUICInversionEtaInstances], in the η context of [si_Σ]

  [fix f (x : I (∀P:Prop. P)) : I (∀P:Prop. P) := x] in [g; k; y : k g; z := y], whose
  [wf_localE] premise holds the η step that types [y] at [k (λx:Prop. g x)]. *)

Lemma c18b_fix_guard : fix_guard si_Σ c18b_sΓ iv_mfix.
Proof.
  change (guard_cl Fix si_Σ c18b_sΓ iv_mfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma c18b_wf_fix : wf_fixpointE si_Σ c18b_sΓ iv_mfix.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_fix_ty. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma c18b_fix_body_typed :
  si_Σ ;;; (c18b_sΓ ,, vass si_na iv_fix_ty) |-E tLambda si_na iv_IF (tRel 0) : lift0 1 iv_fix_ty.
Proof.
  have w : wf_localE si_Σ (c18b_sΓ ,, vass si_na iv_fix_ty) :=
    iv_wf_vass si_Σ c18b_sΓ si_na iv_fix_ty _ c18b_swf (iv_fix_ty_typed c18b_sΓ c18b_swf) Logic.eq_refl.
  change (lift0 1 iv_fix_ty) with (tProd si_na iv_IF iv_IF).
  apply typeE_Lambda.
  - exact (iv_vass si_Σ _ si_na iv_IF sProp (iv_IF_typed _ w) Logic.eq_refl).
  - exact (typeE_Rel _ _ 0 (vass si_na iv_IF) (iv_wf_IF _ w) Logic.eq_refl).
Qed.

Lemma c18b_fix_typed : si_Σ ;;; c18b_sΓ |-E tFix iv_mfix 0 : iv_fix_ty.
Proof.
  have w : wf_localE si_Σ (c18b_sΓ ,, vass si_na iv_fix_ty) :=
    iv_wf_vass si_Σ c18b_sΓ si_na iv_fix_ty _ c18b_swf (iv_fix_ty_typed c18b_sΓ c18b_swf) Logic.eq_refl.
  refine (typeE_Fix _ _ iv_mfix 0 _ c18b_swf c18b_fix_guard Logic.eq_refl _ _ c18b_wf_fix).
  - constructor; [|constructor].
    exact (iv_vass si_Σ c18b_sΓ si_na iv_fix_ty _ (iv_fix_ty_typed c18b_sΓ c18b_swf) Logic.eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef si_Σ _ si_na _ (lift0 1 iv_fix_ty) _ c18b_fix_body_typed
             (iv_fix_ty_typed _ w) Logic.eq_refl).
Qed.

(** The typing of the fixpoint holds the η step through its [wf_localE] premise. *)
Definition type_tFix_invE_inst :=
  type_tFix_invE si_Σ c18b_sΓ iv_mfix 0 iv_fix_ty si_wfE c18b_fix_typed.

(** ** The cofixpoint of [PCUICInversionEtaInstances], in the η telescope of [iv_Σ]

  [cofix g : R (∀P:Prop. P) := mkR (∀P:Prop. P) p] over [c18_tel ,, p : ∀P:Prop. P]. *)

Definition c18b_Γc : context := c18b_Γ ,, vass si_na iv_False.
Definition c18b_Γcf : context := c18b_Γc ,, vass si_na iv_RF.

Lemma c18b_wf_Γc : wf_localE iv_Σ c18b_Γc.
Proof. exact (iv_wf_vass iv_Σ c18b_Γ si_na iv_False sProp c18b_wf c18b_False_typed Logic.eq_refl). Qed.

Lemma c18b_wf_Γcf : wf_localE iv_Σ c18b_Γcf.
Proof.
  exact (iv_wf_vass iv_Σ c18b_Γc si_na iv_RF sProp c18b_wf_Γc (iv_RF_typed c18b_Γc c18b_wf_Γc) Logic.eq_refl).
Qed.

Lemma c18b_cofix_body_typed : iv_Σ ;;; c18b_Γcf |-E iv_cofix_body : lift0 1 iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ c18b_Γcf c18b_wf_Γcf.
  have wF := iv_wf_vass iv_Σ c18b_Γcf iv_fna iv_False sProp c18b_wf_Γcf hF Logic.eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tRel 1) _ (iv_mkRF_typed c18b_Γcf c18b_wf_Γcf) _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ c18b_Γcf iv_fna iv_False sProp hF Logic.eq_refl)|].
    exact (iv_RF_typed _ wF).
  - exact (typeE_Rel _ _ 1 (vass si_na iv_False) c18b_wf_Γcf Logic.eq_refl).
Qed.

Lemma c18b_cofix_guard : cofix_guard iv_Σ c18b_Γc iv_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ c18b_Γc iv_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma c18b_wf_cofix : wf_cofixpointE iv_Σ c18b_Γc iv_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_RF. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma c18b_on_def_type_cofix :
  All (on_def_type (PCUICTyping.lift_typing typingE iv_Σ) c18b_Γc) iv_cmfix.
Proof.
  constructor; [|constructor].
  exact (iv_vass iv_Σ c18b_Γc si_na iv_RF sProp (iv_RF_typed c18b_Γc c18b_wf_Γc) Logic.eq_refl).
Qed.

Lemma c18b_on_def_body_cofix :
  All (on_def_body (PCUICTyping.lift_typing typingE iv_Σ) (fix_context iv_cmfix) c18b_Γc) iv_cmfix.
Proof.
  constructor; [|constructor].
  exact (iv_vdef iv_Σ c18b_Γcf si_na iv_cofix_body (lift0 1 iv_RF) sProp c18b_cofix_body_typed
           (iv_RF_typed c18b_Γcf c18b_wf_Γcf) Logic.eq_refl).
Qed.

Lemma c18b_cofix_typed : iv_Σ ;;; c18b_Γc |-E tCoFix iv_cmfix 0 : iv_RF.
Proof.
  refine (typeE_CoFix _ _ iv_cmfix 0 _ c18b_wf_Γc c18b_cofix_guard Logic.eq_refl
            c18b_on_def_type_cofix c18b_on_def_body_cofix c18b_wf_cofix).
Qed.

(** Every premise is taken in the η telescope: the [wf_localE] it holds is the η step. *)
Definition subslet_cofixE_inst :=
  subslet_cofixE iv_Σ c18b_Γc iv_cmfix c18b_wf_Γc c18b_cofix_guard c18b_on_def_type_cofix
    c18b_on_def_body_cofix c18b_wf_cofix.

Definition type_tCoFix_invE_inst :=
  type_tCoFix_invE iv_Σ c18b_Γc iv_cmfix 0 iv_RF iv_wfE c18b_cofix_typed.

(* WEAK. IMPOSSIBLE (the two named premises): the section's [declared_constructor], a lookup in
   the environment, and [consistent_instance_ext], a proposition about universe levels and
   constraints. Neither mentions a term, a typing or a term relation, so neither can hold an η
   step: [cumul_eta_l] is a constructor of [cumulSpecE0], which relates TERMS.
   NOT BUILT (the [wfE Σ] part): the lemma also carries [{_ : wfE Σ}], which holds the typing
   derivation of every declaration of [Σ] and CAN carry an η step; here the conclusion is read
   off that premise's constructor-argument typing, so η content in the environment reaches the
   conclusion. [iv_Σ] is typed without an η step. Cost: an environment with a declaration whose
   type or body is typed through an η step, and its [wfE] proof.
   NOT BUILT (the universe part): the instance is at [u = []] of the monomorphic [R]. *)
Definition on_constructor_inst_wf_argsE_inst :=
  on_constructor_inst_wf_argsE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_constructor [] c18_cu.

(* NOT BUILT (the universe part): the instance is at [u = []] of the monomorphic [R].
   The parameter spine is taken in the η telescope. *)
Definition on_constructor_inst_pars_indicesE_inst :=
  on_constructor_inst_pars_indicesE (Σ := iv_Σ) iv_wfE iv_declared_constructor c18_cu
    (c18b_sp c18b_Γ iv_False c18b_wf c18b_False_typed).

(** The spine's conversion is the η step [R (k (λx:Prop. g x)) ≤ R (k g)]. *)
Definition mkApps_ind_typing_spineE_inst :=
  mkApps_ind_typing_spineE iv_Σ iv_Γk [] iv_ind [] [] iv_ind [] [iv_keta] [iv_kg]
    iv_wfE c18_wf_Γk c18_isT_Rketa
    (MetaRocq.PCUIC.PCUICAritiesEta.type_spine_nilE _ _ (iv_R iv_keta) (iv_R iv_kg) c18_isT_Rketa c18b_isT_Rkg c18_R_η).

(** ** A cofixpoint declaration whose type is the η side [R (k (λx:Prop. g x))] *)

Definition c18b_emfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_R iv_keta; dbody := tRel 0; rarg := 0 |}].

Lemma c18b_wf_ecofix : wf_cofixpointE iv_Σ iv_Γk c18b_emfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists (iv_R iv_keta). split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

(** The spine ends at [R (k g)]: its only conversion is the η step. *)
Definition wf_cofixpoint_typing_spineE_inst :=
  wf_cofixpoint_typing_spineE iv_Σ iv_Γk iv_ind [] c18b_emfix 0
    {| dname := si_na; dtype := iv_R iv_keta; dbody := tRel 0; rarg := 0 |} [] [iv_kg]
    iv_wfE c18_wf_Γk c18b_wf_ecofix Logic.eq_refl c18_isT_Rketa
    (MetaRocq.PCUIC.PCUICAritiesEta.type_spine_nilE _ _ (iv_R iv_keta) (iv_R iv_kg) c18_isT_Rketa c18b_isT_Rkg c18_R_η).

(** ** The constructor application [mkR (k (λx:Prop. g x)) y]

  Its argument [y] is declared at [k g] and used at [k (λx:Prop. g x)]: the application is
  typed only through the η step. *)

Lemma c18b_mkR_keta_typed :
  iv_Σ ;;; iv_Γk |-E tApp (tConstruct iv_ind 0 []) iv_keta
    : tProd iv_fna iv_keta (iv_R (lift0 1 iv_keta)).
Proof.
  exact (typeE_App _ _ (tConstruct iv_ind 0 []) si_na si_P (tProd iv_fna (tRel 0) (iv_R (tRel 1)))
           _ iv_keta (iv_mkR_ty_typed iv_Γk c18_wf_Γk) (iv_mkR_typed iv_Γk c18_wf_Γk)
           c18_keta_typed).
Qed.

Lemma c18b_mkR_prod_typed :
  iv_Σ ;;; iv_Γk |-E tProd iv_fna iv_keta (iv_R (lift0 1 iv_keta))
    : tSort (Sort.sort_of_product sProp sProp).
Proof.
  have w : wf_localE iv_Σ (iv_Γk ,, vass iv_fna iv_keta) :=
    iv_wf_vass iv_Σ iv_Γk iv_fna iv_keta sProp c18_wf_Γk c18_keta_typed Logic.eq_refl.
  apply typeE_Prod; [exact (iv_vass_s iv_Σ iv_Γk iv_fna iv_keta sProp c18_keta_typed Logic.eq_refl)|].
  apply (iv_RX_typed _ (lift0 1 iv_keta) w).
  exact (weakeningE iv_Σ iv_Γk [vass iv_fna iv_keta] iv_keta si_P iv_wfE w c18_keta_typed).
Qed.

(** [y] is declared at [k g]; [mkR] asks for its argument at [k (λx:Prop. g x)]. *)
Lemma c18b_mkR_app_typed :
  iv_Σ ;;; iv_Γk |-E mkApps (tConstruct iv_ind 0 []) [iv_keta; tRel 0] : iv_R iv_keta.
Proof.
  exact (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_keta) iv_fna iv_keta
           (iv_R (lift0 1 iv_keta)) _ (tRel 0) c18b_mkR_prod_typed c18b_mkR_keta_typed
           (c18_tel_y_eta [] localenv_nil)).
Qed.

(** The application [h y] of the telescope: [y] is retyped through the η step. *)
Definition isTypeE_typingE_tApp_ctor_inst :=
  isTypeE_typingE_tApp_ctor (Σ := iv_Σ) (wfΣ := iv_wfE) (c18_tel_hy_typed [] localenv_nil).

Definition isTypeE_typingE_tConstruct_ctor_inst :=
  isTypeE_typingE_tConstruct_ctor (Σ := iv_Σ) (wfΣ := iv_wfE) (iv_mkR_typed c18b_Γ c18b_wf).

Definition isTypeE_typingE_mkApps_tConstruct_ctor_inst :=
  isTypeE_typingE_mkApps_tConstruct_ctor (Σ := iv_Σ) (wfΣ := iv_wfE) c18b_mkR_app_typed.

(* NOT BUILT (the universe part): the compared instance is [u' := []], the only instance of the
   monomorphic [R], so the universe comparison of the conclusion is [reflexivity]. The typing
   premise is the constructor application whose argument is typed through the η step. *)
Definition Construct_Ind_ind_eqE_inst :=
  Construct_Ind_ind_eqE (Σ := iv_Σ) iv_wfE (i' := iv_ind) (u' := []) (args' := [iv_keta])
    c18b_mkR_app_typed iv_declared_constructor.

(* NOT BUILT (the universe part), as [Construct_Ind_ind_eqE_inst]: [u' := []]. *)
Definition Construct_Ind_ind_eq'E_inst :=
  Construct_Ind_ind_eq'E (Σ := iv_Σ) iv_wfE (i' := iv_ind) (u' := []) (args' := [iv_keta])
    c18b_mkR_app_typed.

(** ** Two fixpoint declarations whose types are the two sides of the η step *)

Definition c18b_mfix_kg : mfixpoint term :=
  [{| dname := si_na; dtype := iv_kg; dbody := tRel 0; rarg := 0 |}].
Definition c18b_mfix_keta : mfixpoint term :=
  [{| dname := si_na; dtype := iv_keta; dbody := tRel 0; rarg := 0 |}].

(** The declared types of the two fixpoints are related by the η step alone. *)
Lemma c18b_all2_dtype :
  All2 (fun d d' => si_Σ ;;; iv_Γk ⊢E d.(dtype) = d'.(dtype) × eq_binder_annot d.(dname) d'.(dname))
    c18b_mfix_kg c18b_mfix_keta.
Proof. constructor; [|constructor]. split; [exact (c18b_ws_eta si_Σ Conv)|reflexivity]. Qed.

Lemma c18b_ctx_refl : ws_cumul_ctx_pbE Conv si_Σ iv_Γk iv_Γk.
Proof. apply ws_cumul_ctx_pbE_refl_pb. reflexivity. Qed.

Definition conv_decls_fix_context_genE_inst :=
  conv_decls_fix_context_genE si_Σ iv_Γk c18b_mfix_kg c18b_mfix_keta si_wfE c18b_all2_dtype
    [] [] c18b_ctx_refl.

Definition conv_decls_fix_contextE_inst :=
  conv_decls_fix_contextE (Σ := si_Σ) (wfΣ := si_wfE) iv_wf_Γk c18b_all2_dtype.

(** The two declarations of the compared contexts differ by the η step
    [G (λy:Prop. F y)] / [G F] alone, so the relation premise holds it. *)
Lemma c18b_ctx_rel_conv :
  ws_cumul_ctx_pbE_rel Conv rf_Σ wc_Γ [vass si_na wc_T] [vass si_na wc_U].
Proof.
  split; [reflexivity|].
  constructor; [constructor|].
  constructor; [reflexivity|]. exact (c18_wc_ws rf_Σ Conv).
Qed.

Definition ws_cumul_ctx_pb_rel_context_assumptionsE_inst :=
  MetaRocq.PCUIC.PCUICInductiveInversionEtaB.ws_cumul_ctx_pb_rel_context_assumptionsE
    rf_Σ wc_Γ [vass si_na wc_T] [vass si_na wc_U] c18b_ctx_rel_conv.

(** ** A [match] on [I] whose discriminee is typed through the η step

  In [iv_Γk], [c (k g) : I (k g)] is the discriminee of a [match] whose parameter is
  [k (λx:Prop. g x)]: the discriminee is accepted only through [I (k g) ≡ I (k (λx. g x))]. *)

Definition c18b_Ieta : term := tApp (tInd si_ind []) iv_keta.
Definition c18b_Ikg : term := tApp (tInd si_ind []) iv_kg.
Definition c18b_ceta : term := tApp (tConstruct si_ind 0 []) iv_keta.
Definition c18b_ckg : term := tApp (tConstruct si_ind 0 []) iv_kg.

Definition c18b_p : predicate term :=
  {| pparams := [iv_keta]; puinst := [];
     pcontext := ind_predicate_context si_ind si_mdecl si_idecl;
     preturn := lift0 1 c18b_Ieta |}.
Definition c18b_br : branch term := {| bcontext := []; bbody := c18b_ceta |}.
Definition c18b_match : term := tCase iv_ci c18b_p c18b_ckg [c18b_br].

Lemma c18b_kg_typed : si_Σ ;;; iv_Γk |-E iv_kg : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ (tRel 2) (iv_K_typed iv_Γk iv_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) iv_wf_Γk Logic.eq_refl)
           (typeE_Rel _ _ 2 (vass si_na iv_PP) iv_wf_Γk Logic.eq_refl)).
Qed.

Lemma c18b_Ieta_typed : si_Σ ;;; iv_Γk |-E c18b_Ieta : si_P.
Proof. exact (iv_IX_typed iv_Γk iv_keta iv_wf_Γk iv_keta_typed). Qed.

Lemma c18b_Ikg_typed : si_Σ ;;; iv_Γk |-E c18b_Ikg : si_P.
Proof. exact (iv_IX_typed iv_Γk iv_kg iv_wf_Γk c18b_kg_typed). Qed.

Lemma c18b_wf_pctx : wf_localE si_Σ (iv_Γk ,, vass iv_zna c18b_Ieta).
Proof. exact (iv_wf_vass si_Σ iv_Γk iv_zna c18b_Ieta sProp iv_wf_Γk c18b_Ieta_typed Logic.eq_refl). Qed.

Lemma c18b_pret_typed :
  si_Σ ;;; (iv_Γk ,, vass iv_zna c18b_Ieta) |-E lift0 1 c18b_Ieta : si_P.
Proof.
  exact (weakeningE si_Σ iv_Γk [vass iv_zna c18b_Ieta] c18b_Ieta si_P si_wfE c18b_wf_pctx
           c18b_Ieta_typed).
Qed.

Lemma c18b_ceta_typed : si_Σ ;;; iv_Γk |-E c18b_ceta : c18b_Ieta.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _
           iv_keta (iv_cstr_prod_typed iv_Γk iv_wf_Γk) (iv_cstr_typed iv_Γk iv_wf_Γk)
           iv_keta_typed).
Qed.

Lemma c18b_ckg_typed : si_Σ ;;; iv_Γk |-E c18b_ckg : c18b_Ikg.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _
           iv_kg (iv_cstr_prod_typed iv_Γk iv_wf_Γk) (iv_cstr_typed iv_Γk iv_wf_Γk)
           c18b_kg_typed).
Qed.

(** [I (k g) ≡ I (k (λx:Prop. g x))]: the congruence of the η step under [I]. *)
Lemma c18b_spec_I : cumulSpecE si_Σ iv_Γk c18b_Ikg c18b_Ieta.
Proof.
  unfold c18b_Ikg, c18b_Ieta. apply cumulE_App; [apply cumulE_Refl|].
  exact (c18b_spec_eta si_Σ iv_Γk Conv).
Qed.

(** The discriminee is typed at the predicate's parameter only through that step. *)
Lemma c18b_disc_typed : si_Σ ;;; iv_Γk |-E c18b_ckg : c18b_Ieta.
Proof.
  exact (typeE_Cumul _ _ c18b_ckg c18b_Ikg c18b_Ieta sProp c18b_ckg_typed c18b_Ieta_typed
           c18b_spec_I).
Qed.

Lemma c18b_wf_p : wf_predicate si_mdecl si_idecl c18b_p.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma c18b_wf_br : wf_branch si_cdecl c18b_br.
Proof. constructor. Qed.

Lemma c18b_ctx_inst : ctx_inst (typingE si_Σ) iv_Γk [iv_keta] [vass si_na si_P].
Proof. econstructor; [|constructor]. exact iv_keta_typed. Qed.

Lemma c18b_bty_typed :
  si_Σ ;;; iv_Γk |-E tApp (tLambda iv_zna c18b_Ieta (lift0 1 c18b_Ieta)) c18b_ceta : si_P.
Proof.
  refine (typeE_App _ _ (tLambda iv_zna c18b_Ieta (lift0 1 c18b_Ieta)) iv_zna c18b_Ieta si_P _
            c18b_ceta _ _ c18b_ceta_typed).
  - apply typeE_Prod.
    + exact (iv_vass_s si_Σ iv_Γk iv_zna c18b_Ieta sProp c18b_Ieta_typed Logic.eq_refl).
    + exact (iv_P_typed si_Σ _ c18b_wf_pctx).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ iv_Γk iv_zna c18b_Ieta sProp c18b_Ieta_typed Logic.eq_refl).
    + exact c18b_pret_typed.
Qed.

Lemma c18b_br_typed :
  si_Σ ;;; iv_Γk |-E c18b_ceta : tApp (tLambda iv_zna c18b_Ieta (lift0 1 c18b_Ieta)) c18b_ceta.
Proof.
  refine (typeE_Cumul _ _ c18b_ceta c18b_Ieta _ sProp c18b_ceta_typed c18b_bty_typed _).
  apply cumulE_Sym. exact (cumulE_beta _ _ Conv iv_zna c18b_Ieta (lift0 1 c18b_Ieta) c18b_ceta).
Qed.

Lemma c18b_case_side :
  case_side_conditions (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) si_Σ iv_Γk iv_ci c18b_p sProp
    si_mdecl si_idecl [] (case_predicate_context si_ind si_mdecl si_idecl c18b_p).
Proof.
  constructor.
  - reflexivity.
  - exact c18b_wf_p.
  - reflexivity.
  - exact c18b_wf_pctx.
  - exact (alpha_eq_reflexive (pcontext c18b_p)).
  - reflexivity.
  - reflexivity.
  - exact c18b_ctx_inst.
  - reflexivity.
Qed.

Lemma c18b_case_brs :
  case_branch_typing (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) iv_Γk iv_ci c18b_p sProp si_mdecl
    si_idecl
    (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl c18b_p) (preturn c18b_p))
    [c18b_br].
Proof.
  constructor.
  - constructor; [exact c18b_wf_br|constructor].
  - constructor; [|constructor].
    split; [constructor|]. cbv zeta. split; [|split].
    + exact iv_wf_Γk.
    + exact c18b_br_typed.
    + exact c18b_bty_typed.
Qed.

Lemma c18b_match_typed :
  si_Σ ;;; iv_Γk |-E c18b_match
    : mkApps (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl c18b_p)
               (preturn c18b_p)) ([] ++ [c18b_ckg]).
Proof.
  eapply (typeE_Case _ _ iv_ci c18b_p c18b_ckg [c18b_br] [] sProp si_mdecl si_idecl).
  - exact si_declared_inductive.
  - exact c18b_pret_typed.
  - exact c18b_disc_typed.
  - exact c18b_case_side.
  - exact c18b_case_brs.
Qed.

Lemma c18b_sq_wfE : ∥ wfE si_Σ.1 ∥.
Proof. constructor. exact si_wfE. Qed.

(** The discriminee [c (k g)] is accepted at the parameter [k (λx:Prop. g x)] through the
    η step alone. *)
Definition invert_Case_ConstructE_inst :=
  invert_Case_ConstructE si_Σ c18b_sq_wfE (ind' := si_ind) (i := 0) (u := []) (args := [iv_kg])
    c18b_match_typed.

(** ** The projection of the constructor application [mkR (k (λx. g x)) y] *)

Lemma c18b_proj_typed :
  iv_Σ ;;; iv_Γk |-E tProj iv_proj (mkApps (tConstruct iv_ind 0 []) [iv_keta; tRel 0]) : iv_keta.
Proof.
  exact (typeE_Proj _ _ iv_proj (mkApps (tConstruct iv_ind 0 []) [iv_keta; tRel 0]) []
           iv_mdecl iv_idecl iv_cdecl iv_pdecl [iv_keta] iv_declared_projection
           c18b_mkR_app_typed Logic.eq_refl).
Qed.

Lemma c18b_sq_iv_wfE : ∥ wfE iv_Σ.1 ∥.
Proof. constructor. exact iv_wfE. Qed.

Definition Proj_Construct_ind_eqE_inst :=
  Proj_Construct_ind_eqE iv_Σ c18b_sq_iv_wfE (i' := iv_ind) (c := 0) (u := [])
    (l := [iv_keta; tRel 0]) c18b_proj_typed.

Definition invert_Proj_ConstructE_inst :=
  invert_Proj_ConstructE iv_Σ c18b_sq_iv_wfE (i' := iv_ind) (c := 0) (u := [])
    (l := [iv_keta; tRel 0]) c18b_proj_typed.

(** ** Substitutions and projections *)

Definition isType_mkApps_Ind_smashE_inst :=
  isType_mkApps_Ind_smashE (Σ := iv_Σ) (Γ := c18b_Γ) (u := []) (params := [iv_False]) (args := [])
    (wfΣ := iv_wfE) iv_declared_inductive c18b_isT_RF Logic.eq_refl.

Lemma c18b_lookup : lookup_env iv_Σ.1 iv_kn = Some (InductiveDecl iv_mdecl).
Proof. reflexivity. Qed.

Lemma c18b_subslet_False : subsletE iv_Σ c18b_Γ [iv_False] [vass si_na si_P].
Proof. exact (subslet_ass_tipE c18b_False_typed). Qed.

Lemma c18b_wf_subslet_False : wf_subsletE iv_Σ c18b_Γ [iv_False] [vass si_na si_P].
Proof.
  split; [exact (iv_wf_P iv_Σ c18b_Γ c18b_wf)|exact c18b_subslet_False].
Qed.

(* NOT BUILT (the universe part): the instantiating instance is [u := []], so
   [consistent_instance_ext] and the instantiation of the substitution are degenerate. *)
Definition instantiate_subsletE_inst :=
  instantiate_subsletE (Σ := iv_Σ) (u := []) (wfΣ := iv_wfE) c18b_lookup c18b_subslet_False c18_cu.

(* NOT BUILT (the universe part), as [instantiate_subsletE_inst]: [u := []]. *)
Definition instantiate_wf_subsletE_inst :=
  instantiate_wf_subsletE (Σ := iv_Σ) (u := []) (wfΣ := iv_wfE) c18b_lookup
    c18b_wf_subslet_False c18_cu.

Lemma c18b_wf_subslet_nil : wf_subsletE iv_Σ (c18b_Γ ,,, [vass si_na si_P] ,,, []) [] [].
Proof. split; [exact (iv_wf_P iv_Σ c18b_Γ c18b_wf)|constructor]. Qed.

(* NOT BUILT (the substitution part): the second substitution is empty
   ([c18b_wf_subslet_nil]), so no substituted term carries an η step. Cost: a well-typed
   non-empty substitution whose terms are the two sides of an η step, with its [subsletE]. *)
Definition substitution_subsletE_inst :=
  substitution_subsletE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ' := []) c18b_subslet_False
    c18b_wf_subslet_nil.

Lemma c18b_wf_subslet_empty : wf_subsletE iv_Σ [] [] [].
Proof. split; [exact localenv_nil|constructor]. Qed.

Definition weaken_wf_subsletE_inst :=
  weaken_wf_subsletE (Σ := iv_Σ) (wfΣ := iv_wfE) [] [] c18b_Γ [] c18b_wf c18b_wf_subslet_empty.

(** The projected term is the constructor application whose argument is typed through the
    η step. *)
Definition subslet_projsE_inst :=
  subslet_projsE (Σ := iv_Σ) (wfΣ := iv_wfE) (args := [iv_keta]) iv_declared_inductive c18_onps
    iv_Γk (mkApps (tConstruct iv_ind 0 []) [iv_keta; tRel 0]) [] c18b_mkR_app_typed.

(* WEAK. IMPOSSIBLE (the named premise): the only named premise is [declared_constructor], a
   lookup in the environment; the conclusion is a closedness statement, and [cumul_eta_l]
   relates terms, so that premise can hold no η step.
   NOT BUILT (the [wfE Σ] part): the lemma also carries [{_ : wfE Σ}], which holds every
   declaration's typing derivation and can carry an η step; [iv_Σ] is typed without one. Cost:
   an environment with a declaration typed through an η step, and its [wfE] proof. *)
Definition positive_cstr_closed_indicesE_inst :=
  positive_cstr_closed_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_constructor.

(** ** The η pair [G (λy:Prop. F y)] / [G F] of [rf_Σ] *)

Lemma c18b_wc_closed : is_closed_context wc_Γ. Proof. reflexivity. Qed.

Lemma c18b_closed_T : closedn #|wc_Γ| wc_T. Proof. reflexivity. Qed.
Lemma c18b_closed_U : closedn #|wc_Γ| wc_U. Proof. reflexivity. Qed.

(* NOT BUILT (the substitution part): both substitutions are empty, so the substituted terms
   carry no η step. Cost: a well-typed non-empty substitution whose terms are the two sides of
   an η step, with its [subsletE]. The conversion premise IS the η step itself. *)
Definition subst_conv_closedE_inst :=
  subst_conv_closedE (Σ := rf_Σ) (wfΣ := wc_wfE) (le := Cumul) (Γ := []) (Γ0 := []) (Γ1 := [])
    (Δ := wc_Γ) (s := []) (s' := []) (emptysletE _ _) (emptysletE _ _) Logic.eq_refl
    c18b_closed_T c18b_closed_U (c18_wc_ws rf_Σ Cumul).

(** The two declarations differ by the η step alone. *)
Lemma c18b_cumul_ctx_join :
  cumul_ctx_rel (@JoinE _) rf_Σ wc_Γ [vass si_na wc_T] [vass si_na wc_U].
Proof.
  constructor; [constructor|].
  constructor; [reflexivity|]. exact (wsE_join (c18_wc_ws rf_Σ Cumul)).
Qed.

Definition into_ws_cumul_ctx_pb_relE_inst :=
  into_ws_cumul_ctx_pb_relE (Σ := rf_Σ) (wfΣ := wc_wfE) c18b_cumul_ctx_join Logic.eq_refl
    Logic.eq_refl.

Lemma c18b_all2_spec : All2 (convSpecE rf_Σ wc_Γ) [wc_T] [wc_U].
Proof. constructor; [|constructor]. exact (c18_wc_spec rf_Σ Conv wc_Γ). Qed.

Definition into_ws_cumul_pb_termsE_inst :=
  into_ws_cumul_pb_termsE (Σ := rf_Σ) (wfΣ := wc_wfE) c18b_all2_spec Logic.eq_refl
    Logic.eq_refl Logic.eq_refl.

(* WEAK. IMPOSSIBLE (the named premise), as [positive_cstr_closed_indicesE_inst]: the only
   named premise is the environment lookup [declared_constructor].
   NOT BUILT (the [wfE Σ] part), with the same cost as there. *)
Definition on_constructor_closed_indicesE_inst :=
  on_constructor_closed_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_constructor.

(* WEAK. IMPOSSIBLE (the named premise) and NOT BUILT (the [wfE Σ] part), as above. *)
Definition positive_cstr_closed_indices'E_inst :=
  positive_cstr_closed_indices'E (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_constructor.

(** ** The η telescope read as [Γ ,,, Δ] *)

Definition c18b_Δ : context := [vass si_na c18_tel_hy; vass si_na c18_tel_hty].

Lemma c18b_wf_app : wf_localE iv_Σ (iv_Γk ,,, c18b_Δ).
Proof. exact c18b_wf. Qed.

Lemma c18b_isT_P_app : isTypeE iv_Σ (iv_Γk ,,, c18b_Δ) si_P.
Proof. exact c18b_isT_P. Qed.

Lemma c18b_closed_Γ : is_closed_context c18b_Γ. Proof. reflexivity. Qed.
Lemma c18b_open_P : is_open_term c18b_Γ si_P. Proof. reflexivity. Qed.

Lemma c18b_ctx_refl_iv : ws_cumul_ctx_pbE Conv iv_Σ iv_Γk iv_Γk.
Proof. apply ws_cumul_ctx_pbE_refl_pb. reflexivity. Qed.

(** The [wf_localE] of the telescope holds the η step of [w : h y]. *)
Definition ws_cumul_ctx_pb_wf_localE_inst :=
  ws_cumul_ctx_pb_wf_localE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_Γk iv_Γk c18b_Δ c18b_wf_app
    c18_wf_Γk c18b_ctx_refl_iv.

(* NOT BUILT (the universe part): both compared instances are [[]] ([c18_cu] twice), so the
   universe comparison [c18_cmp_ind 1] is the monomorphic one. The compared parameters are the
   two sides of the η step. *)
Definition constructor_cumulative_indicesE_inst :=
  constructor_cumulative_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) (napp := 1)
    iv_declared_constructor c18_cu c18_cu (c18_cmp_ind 1) iv_Γk [iv_keta] [iv_kg] [iv_keta]
    [iv_kg] (c18_sp iv_keta c18_keta_typed) (c18_sp iv_kg c18_kg_typed) c18_terms.

(* WEAK. IMPOSSIBLE (the named premises): [declared_inductive], a lookup, and
   [consistent_instance_ext], a statement about universe levels; the conclusion is an equality
   of contexts, and no named premise relates two terms.
   NOT BUILT (the [wfE Σ] part): the lemma also carries [{_ : wfE Σ}], which can carry an η
   step. Cost: an environment with a declaration typed through an η step, and its [wfE] proof.
   NOT BUILT (the universe part): the instance is at [u = []]. *)
Definition subst_inds_smash_paramsE_inst :=
  subst_inds_smash_paramsE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_inductive c18_cu.

(** The type is taken in the η telescope, read as [Γ ,,, Δ]. *)
Definition isType_it_mkProd_or_LetInE_inst :=
  PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE (Σ := iv_Σ) (Γ := iv_Γk)
    (Δ := c18b_Δ) (T := si_P) iv_wfE c18b_isT_P_app.

Lemma c18b_nas : All2 (fun x y => eq_binder_annot x y.(decl_name)) [si_na; si_na] c18b_Δ.
Proof. constructor; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Definition wf_set_binder_nameE_inst :=
  wf_set_binder_nameE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) c18b_nas c18b_wf_app.

(** ** The case predicate of [R] over the η telescope *)

Definition c18b_ci : case_info :=
  {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.

Definition c18b_pF : predicate term :=
  {| pparams := [iv_False]; puinst := [];
     pcontext := ind_predicate_context iv_ind iv_mdecl iv_idecl; preturn := si_P |}.

Lemma c18b_wf_pF : wf_predicate iv_mdecl iv_idecl c18b_pF.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma c18b_wf_sort_P : wf_sort iv_Σ sProp. Proof. exact I. Qed.

Definition WfArity_build_case_predicate_typeE_inst :=
  WfArity_build_case_predicate_typeE (Σ := iv_Σ) (Γ := c18b_Γ) (ci := c18b_ci) (args := [])
    (p := c18b_pF) (ps := sProp) iv_wfE iv_declared_inductive c18b_isT_RF c18b_wf_sort_P
    c18b_wf_pF.

(* WEAK. IMPOSSIBLE (every premise). The only premise is [T = T'], Leibniz equality of terms,
   and the lemma carries NO environment premise ([wfE] is not among its binders), so there is
   no part that an η-typed environment could reach. An η step relates two DIFFERENT terms
   ([cumul_eta_l] rewrites [t] to [λx. t x]), so a premise that forces the two sides to be the
   same term admits none. *)
Definition arity_spine_eqE_inst :=
  MetaRocq.PCUIC.PCUICInductiveInversionEtaB.arity_spine_eqE (Σ := iv_Σ) (Γ := c18b_Γ) (T := si_P) (T' := si_P) Logic.eq_refl.

Definition arity_spine_to_extended_listE_inst :=
  arity_spine_to_extended_listE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) (Δ := c18b_Δ) si_P
    c18b_wf_app c18b_isT_P_app.

Definition isType_subst_all_relsE_inst :=
  isType_subst_all_relsE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) (Δ := c18b_Δ) (T := si_P)
    c18b_isT_P_app.

Definition isType_all_rels_subst_liftE_inst :=
  isType_all_rels_subst_liftE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) (Δ := c18b_Δ)
    (T := si_P) c18b_isT_P_app.

Definition arity_spine_to_extended_list_appE_inst :=
  arity_spine_to_extended_list_appE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) (Δ := c18b_Δ)
    (T := si_P) (s := []) (T' := si_P) c18b_wf_app c18b_isT_P_app (arity_spine_nilE _ _ si_P).

Lemma c18b_spine_P : PCUICAritiesEta.typing_spineE iv_Σ c18b_Γ si_P [] si_P.
Proof.
  exact (MetaRocq.PCUIC.PCUICAritiesEta.type_spine_nilE _ _ si_P si_P c18b_isT_P c18b_isT_P
           (ws_cumul_pbE_refl (Σ := iv_Σ) (pb := Cumul) c18b_closed_Γ c18b_open_P)).
Qed.

Definition typing_spine_to_extended_list_appE_inst :=
  typing_spine_to_extended_list_appE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) (Δ := c18b_Δ)
    (T := si_P) (s := []) (T' := si_P) c18b_spine_P.

Definition typing_spine_to_extended_list_k_appE_inst :=
  typing_spine_to_extended_list_k_appE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) (Δ := c18b_Δ)
    (Δ' := []) (T := si_P) (s := []) (T' := si_P) c18b_isT_P_app c18b_spine_P.

(** ** The case predicate and the case branches of [R] over the η telescope *)

Definition wf_case_predicate_contextE_inst :=
  wf_case_predicate_contextE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := c18b_Γ) (ci := c18b_ci)
    (p := c18b_pF) (args := []) iv_declared_inductive c18b_isT_RF c18b_wf_pF.

(* NOT BUILT (the universe part): the instance is at [u = []] of the monomorphic [R]. *)
Definition case_predicate_context_alphaE_inst :=
  case_predicate_context_alphaE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (p := c18b_pF)
    (Γ := c18b_Γ) iv_declared_inductive c18_cu
    (c18b_sp c18b_Γ iv_False c18b_wf c18b_False_typed)
    ltac:(constructor; [reflexivity|constructor]).

Lemma c18b_alpha_p :
  eq_context_upto_names (pcontext c18b_pF) (ind_predicate_context c18b_ci.(ci_ind) iv_mdecl iv_idecl).
Proof. exact (alpha_eq_reflexive (pcontext c18b_pF)). Qed.

(* WEAK. IMPOSSIBLE (the named premise): [eq_context_upto_names], the syntactic alpha equality
   of two contexts: it compares the declarations up to binder names only, so two declarations
   whose types differ by an η step do not satisfy it.
   NOT BUILT (the [wfE Σ] part): the lemma also carries [{_ : wfE Σ}], which holds every
   declaration's typing derivation and can carry an η step; [iv_Σ] is typed without one. Cost:
   an environment with a declaration typed through an η step, and its [wfE] proof. *)
Definition inst_case_predicate_context_alpha_eqE_inst :=
  inst_case_predicate_context_alpha_eqE (Σ := iv_Σ) (wfΣ := iv_wfE) (mdecl := iv_mdecl)
    (idecl := iv_idecl) (ci := c18b_ci) (p := c18b_pF) c18b_alpha_p.

Lemma c18b_si_cu : consistent_instance_ext si_Σ (ind_universes si_mdecl) [].
Proof. reflexivity. Qed.

(* WEAK. IMPOSSIBLE (the named premises): [declared_inductive] and [consistent_instance_ext], a
   lookup and a universe statement, and [wf_branch_gen], an [All2] on binder names. None of
   them relates two terms.
   NOT BUILT (the [wfE Σ] part): the lemma also carries [{_ : wfE Σ}], which can carry an η
   step; [si_Σ] is typed without one. Cost: an environment with a declaration typed through an
   η step, and its [wfE] proof.
   NOT BUILT (the universe part): the instance is at [puinst := []]. *)
Definition pre_case_branch_context_eqE_inst :=
  pre_case_branch_context_eqE (Σ := si_Σ) (wfΣ := si_wfE) (ind := si_ind) (mdecl := si_mdecl)
    (idecl := si_idecl) (params := [si_P]) (puinst := []) (bctx := []) (cdecl := si_cdecl)
    si_declared_inductive c18b_si_cu ltac:(constructor).

Definition c18b_br2 : branch term :=
  {| bcontext := cstr_args iv_cdecl; bbody := iv_False |}.

Lemma c18b_wf_branch2 : wf_branch iv_cdecl c18b_br2.
Proof. constructor; [reflexivity|constructor]. Qed.

Lemma c18b_wf_branches2 : wf_branches iv_idecl [c18b_br2].
Proof. constructor; [exact c18b_wf_branch2|constructor]. Qed.

Lemma c18b_predctx_wf :
  wf_localE iv_Σ (c18b_Γ ,,, case_predicate_context c18b_ci iv_mdecl iv_idecl c18b_pF).
Proof. exact wf_case_predicate_contextE_inst. Qed.

Lemma c18b_pret_typed2 :
  iv_Σ ;;; c18b_Γ ,,, case_predicate_context c18b_ci iv_mdecl iv_idecl c18b_pF
    |-E preturn c18b_pF : tSort (Sort.super sProp).
Proof. exact (iv_P_typed iv_Σ _ c18b_predctx_wf). Qed.

Lemma c18b_instpredctx_wf :
  wf_localE iv_Σ (c18b_Γ ,,, PCUICCases.inst_case_predicate_context c18b_pF).
Proof. exact c18b_predctx_wf. Qed.

Lemma c18b_pret_typed3 :
  iv_Σ ;;; c18b_Γ ,,, PCUICCases.inst_case_predicate_context c18b_pF
    |-E preturn c18b_pF : tSort (Sort.super sProp).
Proof. exact (iv_P_typed iv_Σ _ c18b_instpredctx_wf). Qed.

(** Every typing is taken in the η telescope. *)
Definition wf_case_branch_typeE_inst :=
  wf_case_branch_typeE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := c18b_Γ) (ci := c18b_ci)
    (p := c18b_pF) (Sort.super sProp) [] iv_declared_inductive c18b_isT_RF c18b_wf_pF
    c18b_pret_typed2 c18b_alpha_p 0 iv_cdecl c18b_br2 iv_declared_constructor c18b_wf_branch2.

Definition wf_case_branch_type'E_inst :=
  wf_case_branch_type'E (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := c18b_Γ) (ci := c18b_ci)
    (p := c18b_pF) (Sort.super sProp) [] iv_declared_inductive c18b_isT_RF c18b_wf_pF
    c18b_pret_typed3 c18b_alpha_p 0 iv_cdecl c18b_br2 iv_declared_constructor c18b_wf_branch2.

Definition wf_case_branches_typesE_inst :=
  wf_case_branches_typesE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := c18b_Γ) (ci := c18b_ci)
    (p := c18b_pF) (Sort.super sProp) [] [c18b_br2] iv_declared_inductive c18b_isT_RF
    c18b_wf_pF c18b_pret_typed3 c18b_wf_branches2 c18b_alpha_p.

Definition wf_case_branches_types'E_inst :=
  wf_case_branches_types'E (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := c18b_Γ) (ci := c18b_ci)
    (p := c18b_pF) (Sort.super sProp) [] [c18b_br2] iv_declared_inductive c18b_isT_RF
    c18b_wf_pF c18b_pret_typed2 c18b_wf_branches2 c18b_alpha_p.

(** ** The β redex over a telescope whose instance is typed through the η step *)

Lemma c18b_wf_Γy : wf_localE iv_Σ (iv_Γk ,, vass si_na iv_keta).
Proof.
  exact (iv_wf_vass iv_Σ iv_Γk si_na iv_keta sProp c18_wf_Γk c18_keta_typed Logic.eq_refl).
Qed.

Lemma c18b_isT_P_y : isTypeE iv_Σ (iv_Γk ,, vass si_na iv_keta) si_P.
Proof. exact (has_sort_isTypeE _ (iv_P_typed iv_Σ _ c18b_wf_Γy)). Qed.

(** The instance [y] of the telescope [[_ : k (λx:Prop. g x)]] is declared at [k g]. *)
Lemma c18b_ctx_inst_y : ctx_instE iv_Σ iv_Γk [tRel 0] (List.rev [vass si_na iv_keta]).
Proof. econstructor; [exact (c18_tel_y_eta [] localenv_nil)|constructor]. Qed.

Definition conv_betas_typedE_inst :=
  conv_betas_typedE iv_Σ iv_wfE iv_Γk [vass si_na iv_keta] [tRel 0] si_P c18b_isT_P_y
    c18b_ctx_inst_y.

(** ** Two declarations whose arity and constructor type hold the η telescope *)

Definition c18b_idecl : one_inductive_body :=
  {| ind_name := "A"; ind_indices := []; ind_sort := sProp; ind_type := tSort sProp;
     ind_kelim := IntoAny; ind_ctors := []; ind_projs := []; ind_relevance := Relevant |}.

Definition c18b_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 5; ind_params := c18_tel; ind_bodies := [c18b_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Lemma c18b_isT_sort : isTypeE iv_Σ c18b_Γ (tSort sProp).
Proof. exact c18b_isT_P. Qed.

(** The arity binds the telescope, so its typing holds the η step of [w : h y]. *)
Lemma c18b_isT_arity :
  isTypeE iv_Σ []
    (it_mkProd_or_LetIn (ind_params c18b_mdecl)
       (it_mkProd_or_LetIn (ind_indices c18b_idecl) (tSort (ind_sort c18b_idecl)))).
Proof.
  exact (PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE (Σ := iv_Σ) (Γ := [])
           (Δ := c18_tel) (T := tSort sProp) iv_wfE c18b_isT_sort).
Qed.

Definition ind_arity_relevantE_inst :=
  ind_arity_relevantE iv_Σ c18b_mdecl c18b_idecl iv_wfE c18b_isT_arity.

(** The constructor's arguments are the telescope: its type's typing holds the η step. *)
Definition c18b_mdecl2 : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 0; ind_params := []; ind_bodies := [c18b_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition c18b_cdecl : constructor_body :=
  {| cstr_name := "c"; cstr_args := c18_tel; cstr_indices := [];
     cstr_type := it_mkProd_or_LetIn c18_tel (tRel 5); cstr_arity := 5 |}.

Definition c18b_ar : context := arities_context (ind_bodies c18b_mdecl2).

Lemma c18b_wf_ar : wf_localE iv_Σ c18b_ar.
Proof.
  apply localenv_cons_abs; [exact localenv_nil|].
  apply (iv_vass iv_Σ [] _ (tSort sProp) (Sort.super sProp));
    [exact (iv_P_typed iv_Σ [] localenv_nil)|reflexivity].
Qed.

Lemma c18b_wf_ar_tel : wf_localE iv_Σ (c18b_ar ,,, c18_tel).
Proof. exact (c18_tel_wf c18b_ar c18b_wf_ar). Qed.

Lemma c18b_isT_rel5 : isTypeE iv_Σ (c18b_ar ,,, c18_tel) (tRel 5).
Proof.
  exact (has_sort_isTypeE _ (typeE_Rel _ _ 5 (vass (mkBindAnn (nNamed "A") Relevant) (tSort sProp))
                               c18b_wf_ar_tel Logic.eq_refl)).
Qed.

Lemma c18b_isT_cstr_type : isTypeE iv_Σ c18b_ar (cstr_type c18b_cdecl).
Proof.
  exact (PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE (Σ := iv_Σ) (Γ := c18b_ar)
           (Δ := c18_tel) (T := tRel 5) iv_wfE c18b_isT_rel5).
Qed.

Definition isTypeRel_cstr_typeE_inst :=
  isTypeRel_cstr_typeE iv_Σ c18b_mdecl2 c18b_idecl c18b_cdecl 0 iv_wfE Logic.eq_refl
    Logic.eq_refl (has_sort_isTypeE _ (iv_P_typed iv_Σ [] localenv_nil))
    ltac:(reflexivity) (has_sort_isTypeE _ (iv_P_typed iv_Σ [] localenv_nil)) Logic.eq_refl
    (ctx_inst_nil _ _) c18b_isT_cstr_type.
