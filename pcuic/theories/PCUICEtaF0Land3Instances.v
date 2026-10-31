(* Distributed under the terms of the MIT license. *)

(** * F0 forecast of LAND3: non-degenerate instances in the region BET-339 admits

  BET-339 (integ-all8) adds [ci_cofix_nondep] to [case_info]: [red_cofix_case] requires it,
  and the coinductive case side condition becomes
  [isCoFinite ==> (ci_cofix_nondep ==> on_free_vars (strengthenP 0 1 xpredT) preturn)].
  It admits a case on a coinductive whose flag is unset and whose return predicate mentions
  the scrutinee, and no cofixpoint unfolds under such a case. This file runs cases of that
  region through the LAND3 theorems. Environment: [iv_Σ] of [PCUICInversionEtaInstances]
  ([CoInductive R (A : Prop) : Prop := mkR { f : A }], well formed: [iv_wf], [iv_wfE]).
  The case [fo_case] of the region and its typing pieces ([fo_case_side], [fo_case_brs],
  [fo_pret_typed]) are [PCUICEtaFO4Instances]'s, in the context
  [fo_Γ := P : R F -> Prop, h : forall r : R F, P r, x : R F] ([F := forall P : Prop, P]).

  1. Subject reduction for a step INSIDE such a case ([PCUICSREta.subject_reductionE]).
     [f3_cofix := cofix c : R F := mkR F x.(f)] (no recursive call; guard by [gc_check]).
     [f3_t0 := match (fun y : R F => y) f3_cofix as z return P z with mkR _ b => h (mkR F b) end]
     (flag unset), [f3_t1] the same case on [f3_cofix]; [f3_step] is [case_red_discr] of
     [red_beta]. [f3_t0_typed] is a [typingE] derivation of [f3_t0]; [f3_sr] gives [f3_t1] the
     same type through [PCUICSREta.subject_reductionE].
     Non-degeneracy: the step is a real [red1] step ([f3_step]); the predicate mentions the
     scrutinee, so the side condition before BET-339 is false on it ([f3_old_premise_fails]),
     the new one holds ([f3_new_premise_holds]); the flag is unset ([f3_flag_unset]), so
     [red_cofix_case] cannot fire on [f3_t1], which is a weak-head neutral ([f3_t1_whne], base
     [whne_case_cofix_dep]). [f3_cofix] is a cofixpoint, so [f3_t1] is exactly the blocked
     shape [stuck_cofix_case_scrut].

  2. The rows of [PCUICClassificationEta] and [PCUICProgressEta] that BET-339 changed, on a
     CLOSED blocked case. [g_t := match g_cofix as z return R A with mkR _ b => mkR A b end],
     flag unset, [A := R F -> R F] (a closed proposition with the closed proof
     [fun y : R F => y]), [g_cofix := cofix c : R A := mkR A (fun y : R F => y)]. [g_t] is
     closed, typed at [R A] ([g_t_typed_RA]), a weak-head neutral ([g_whne]) and has no value
     ([g_no_eval], base [wcbv_stuck_no_eval]).
     - [wh_neutral_empty_genE], [wh_neutral_emptyE]: before BET-339 they concluded [False]
       (IMPOSSIBLE rows of [PCUICClassificationEtaInstances]); now they conclude
       [stuck_cofix_case t]. Their instances at [g_t] are tagged IMPOSSIBLE (root ruling,
       land6-review.md "Ship lineage (F0 + LAND12)"): on every instance whose premises hold, the
       conclusion is the instance's own [whne] derivation translated into [stuck_cofix_case].
     - [whnf_classification'E], [whnf_classificationE]: instances at [g_t]; the head of [g_t]
       is neither a constructor nor a cofixpoint ([g_head_not_discr]), so they land in the
       disjunct BET-339 added ([g_whnf_classification_stuck]). Tagged IMPOSSIBLE for the same
       reason: the conclusion is read off the instance's own [wh_normal] derivation.
     - [progressE] at [g_t]: [g_t] is [wcbv_stuck] ([g_wcbv_stuck]).
     - [red1_progressE] (new copy of base [red1_progress]): instance at [g_t].

  3. The T8 probe on a type-level case of the region ([PCUICEtaT8Probe.T8_Ind_r]).
     In [iv_Γr := x : R F], [t8_T := match mkR F x.(f) as z return t8_inner z with
     mkR _ b => R F end], flag unset, where [t8_inner z := match z return Type with
     mkR _ _ => Prop end] (flag set). The return predicate mentions the scrutinee (as the
     scrutinee of the inner case, stuck on a variable [z]); at [mkR F x.(f)] it computes to
     [Prop], so [t8_T : Prop] ([t8_T_sort]). [t8_T] reaches [R F] only by ι
     ([t8_T_conv]). [t8_Ind_r_inst] applies the proved [T8_Ind_r] to it. Tagged NOT-BUILT
     (root ruling): degenerate, [t8_T_conv] is one root ι step given as a cumulativity and
     [T8_Ind_r] returns that step; a conversion whose derivation contains an expansion (a peak),
     so that [T8_Ind_r] must use confluence, would make it run. [t8_old_premise_fails] and
     [t8_flag_unset] say only that [t8_T] is in the region.

  4. LAND4/5 under BET-339 (branch [wip/eta-meta-f0-land45-2026-10-30]): canonicity on the
     closed blocked case [g_t], the E twins of base's consistency helpers that BET-339 adds, and
     refutations of the pre-BET-339 forms of copy 20's [SN_to_WNE] and [wcbv_normalizationE]
     (each under base's normalization premise for [iv_Σ], which no one proves). Details in the
     section.

  5. The two induction principles BET-339 restated ([typing_ind_envE],
     [typing_ind_env_app_sizeE]), each run with predicates whose [tCase] hypothesis consumes the
     restated premise: a typed case on [R] with a predicate on the scrutinee has its flag unset.
     Details in the section.

  6. LAND6 under BET-339 (branch [wip/eta-meta-f0-land6-2026-10-30]): [l6_si_no_stuck] (no typed
     blocked case in [si_Σ], so [wh_neutral_empty(_gen)E] have no instance in
     [PCUICClassificationEtaInstances]), [l6_cF_not_stuck] and [l6_xx_redex_not_stuck] (the
     LAND6 instances on [c (∀P. P)] and [(λx:Prop. x → x) (∀P. P)] land in the old disjunct of
     the restated sums). In section 4.

  Tags: the instance grammar of [lanes/eta/meta/instance-gate.md] (one [INSTANCE NONDEGEN],
  [INSTANCE IMPOSSIBLE:] or [INSTANCE NOT-BUILT:] line directly above each instance, with
  [TARGET] lines). Declarations that are neither instances nor NONDEGEN lemmas:
  WITNESSES: f3_* g_* t8_* l45_* l6_* pgf_* g_ctx_inst t8_ctx_inst wh_neutral_emptyE_old_false whnf_classification'E_old_false progressE_old_false SN_to_WNE_old_false wcbv_normalizationE_old_false ws_wcbv_standardizationE_old_false wh_neutral_empty_genE_inst_nondeg wh_neutral_emptyE_inst_nondeg whnf_classification'E_stuck_inst_nondeg whnf_classificationE_stuck_inst_nondeg t8_Ind_r_inst_nondeg typing_tApp_invE_inst_nondeg typing_tCase_scrutE_inst_nondeg typing_tProj_argE_inst_nondeg typing_tCoFix_cofiniteE_inst_nondeg typing_mkApps_argE_inst_nondeg typing_mkApps_headE_inst_nondeg typing_stuck_cofix_case_cofiniteE_inst_nondeg pcuic_canonicityE_stuck_inst_nondeg no_closed_stuck_cofix_case_at_no_cofiniteE_inst_nondeg no_closed_stuck_cofix_case_at_Σ_FalseE_inst_nondeg

  Forecast evidence for the cutover F0 (it rests on the ship branch's
  [PCUICEtaFO4Instances], which is itself forecast-only). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICSafeLemmata PCUICSN PCUICConfluence PCUICWellScopedCumulativity
     PCUICEtaC1b.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICReduction PCUICViews PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICClosedBodies PCUICClosedTyp PCUICClosedTypEta PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICGuardClosure PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICEtaFO4Instances
     PCUICNormal PCUICWcbvEval PCUICClassification PCUICClassificationEta PCUICProgressEta
     PCUICSREta PCUICEtaT8Probe.
From MetaRocq.PCUIC Require PCUICWfUniverses.
From MetaRocq.PCUIC Require PCUICSNEta PCUICConsistency PCUICCanonicityEta PCUICConsistencyEta
     PCUICConsistencyEtaInstances PCUICEtaA6 PCUICSREtaInstances PCUICClassificationEtaInstances.
From MetaRocq.PCUIC Require Import PCUICTypingEtaInd.

#[local] Existing Instance default_checker_flags.
#[local] Instance f3_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.

(** ** 1. Subject reduction for a step inside a case of the region *)

Definition f3_cmfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_RF; dbody := fo_mkRF (tProj iv_proj (tRel 1)); rarg := 0 |}].
Definition f3_cofix : term := tCoFix f3_cmfix 0.
Definition f3_idRF : term := tLambda si_na iv_RF (tRel 0).
Definition f3_scrut : term := tApp f3_idRF f3_cofix.
Definition f3_t0 : term := tCase fo_ci fo_p f3_scrut [fo_br].
Definition f3_t1 : term := tCase fo_ci fo_p f3_cofix [fo_br].
Definition f3_T : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl fo_p) (preturn fo_p))
    ([] ++ [f3_scrut]).
Definition f3_Γc : context := fo_Γ ,, vass si_na iv_RF.

Lemma f3_wf_Γc : wf_localE iv_Σ f3_Γc.
Proof. exact (iv_wf_vass iv_Σ fo_Γ si_na iv_RF sProp fo_wf_Γ (iv_RF_typed fo_Γ fo_wf_Γ) eq_refl). Qed.

(** [x.(f) : F] under the cofixpoint's binder ([x] is variable 1). *)
Lemma f3_proj_typed : iv_Σ ;;; f3_Γc |-E tProj iv_proj (tRel 1) : iv_False.
Proof.
  exact (typeE_Proj _ _ iv_proj (tRel 1) [] iv_mdecl iv_idecl iv_cdecl iv_pdecl [iv_False]
           iv_declared_projection (typeE_Rel _ _ 1 (vass si_na iv_RF) f3_wf_Γc eq_refl) eq_refl).
Qed.

Lemma f3_cofix_body_typed : iv_Σ ;;; f3_Γc |-E fo_mkRF (tProj iv_proj (tRel 1)) : lift0 1 iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ f3_Γc f3_wf_Γc.
  have wF := iv_wf_vass iv_Σ f3_Γc iv_fna iv_False sProp f3_wf_Γc hF eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tProj iv_proj (tRel 1)) _ (iv_mkRF_typed f3_Γc f3_wf_Γc) _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ f3_Γc iv_fna iv_False sProp hF eq_refl)|].
    exact (iv_RF_typed _ wF).
  - exact f3_proj_typed.
Qed.

Lemma f3_cofix_guard : cofix_guard iv_Σ fo_Γ f3_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ fo_Γ f3_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma f3_wf_cofix : wf_cofixpointE iv_Σ fo_Γ f3_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_RF. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma f3_cofix_typed : iv_Σ ;;; fo_Γ |-E f3_cofix : iv_RF.
Proof.
  refine (typeE_CoFix _ _ f3_cmfix 0 _ fo_wf_Γ f3_cofix_guard eq_refl _ _ f3_wf_cofix).
  - constructor; [|constructor].
    exact (iv_vass iv_Σ fo_Γ si_na iv_RF sProp (iv_RF_typed fo_Γ fo_wf_Γ) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef iv_Σ f3_Γc si_na (fo_mkRF (tProj iv_proj (tRel 1))) (lift0 1 iv_RF) sProp
             f3_cofix_body_typed (iv_RF_typed f3_Γc f3_wf_Γc) eq_refl).
Qed.

(** [fun y : R F => y : R F -> R F], in any well-formed context. *)
Lemma f3_idRF_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E f3_idRF : tProd si_na iv_RF iv_RF.
Proof.
  intros h. apply typeE_Lambda.
  - exact (iv_vass iv_Σ Γ si_na iv_RF sProp (iv_RF_typed Γ h) eq_refl).
  - exact (typeE_Rel _ _ 0 (vass si_na iv_RF)
             (iv_wf_vass iv_Σ Γ si_na iv_RF sProp h (iv_RF_typed Γ h) eq_refl) eq_refl).
Qed.

(** [R F -> R F : Prop], in any well-formed context. *)
Lemma f3_RFRF_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tProd si_na iv_RF iv_RF : si_P.
Proof.
  intros h.
  have w := iv_wf_vass iv_Σ Γ si_na iv_RF sProp h (iv_RF_typed Γ h) eq_refl.
  exact (typeE_Prod _ _ si_na iv_RF iv_RF sProp sProp
           (iv_vass_s iv_Σ Γ si_na iv_RF sProp (iv_RF_typed Γ h) eq_refl) (iv_RF_typed _ w)).
Qed.

Lemma f3_scrut_typed : iv_Σ ;;; fo_Γ |-E f3_scrut : iv_RF.
Proof.
  exact (typeE_App _ _ f3_idRF si_na iv_RF iv_RF sProp f3_cofix (f3_RFRF_typed fo_Γ fo_wf_Γ)
           (f3_idRF_typed fo_Γ fo_wf_Γ) f3_cofix_typed).
Qed.

Lemma f3_t0_typed : iv_Σ ;;; fo_Γ |-E f3_t0 : f3_T.
Proof.
  eapply (typeE_Case _ _ fo_ci fo_p f3_scrut [fo_br] [] sProp iv_mdecl iv_idecl).
  - exact iv_declared_inductive.
  - exact fo_pret_typed.
  - exact f3_scrut_typed.
  - exact fo_case_side.
  - exact fo_case_brs.
Qed.

(** The step: β inside the scrutinee. *)
Lemma f3_step : red1 iv_Σ fo_Γ f3_t0 f3_t1.
Proof. apply case_red_discr. exact (red_beta _ _ si_na iv_RF (tRel 0) f3_cofix). Qed.

(* INSTANCE NONDEGEN PCUICEtaF0Land3Instances.f3_sr_nondeg
   TARGET PCUICSREta.subject_reductionE
   The landed T1 theorem on a β step inside a flag-unset case on a cofixpoint whose return
   predicate mentions the scrutinee. *)
Theorem f3_sr : iv_Σ ;;; fo_Γ |-E f3_t1 : f3_T.
Proof.
  apply (PCUICSREta.subject_reductionE iv_Σ fo_Γ f3_t0 f3_t1 f3_T iv_wfE f3_t0_typed).
  apply red1_red. exact f3_step.
Qed.

(** Non-degeneracy. *)
Lemma f3_flag_unset : fo_ci.(ci_cofix_nondep) = false.
Proof. reflexivity. Qed.

Lemma f3_old_premise_fails :
  (isCoFinite (ind_finite iv_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p)) = false.
Proof. reflexivity. Qed.

Lemma f3_new_premise_holds :
  (isCoFinite (ind_finite iv_mdecl) ==>
   (fo_ci.(ci_cofix_nondep) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p))) = true.
Proof. reflexivity. Qed.

Lemma f3_t1_whne : whne RedFlags.default iv_Σ fo_Γ f3_t1.
Proof.
  change f3_t1 with (tCase fo_ci fo_p (mkApps (tCoFix f3_cmfix 0) []) [fo_br]).
  now apply whne_case_cofix_dep.
Qed.

Lemma f3_t1_stuck : stuck_cofix_case f3_t1.
Proof.
  change f3_t1 with (tCase fo_ci fo_p (mkApps (tCoFix f3_cmfix 0) []) [fo_br]).
  now apply stuck_cofix_case_scrut.
Qed.

(** ** 2. A closed blocked case: the changed rows of [PCUICClassificationEta] and
    [PCUICProgressEta] *)

Definition g_A : term := tProd si_na iv_RF iv_RF.
Definition g_RA : term := iv_R g_A.
Definition g_mkRA (a : term) : term := tApp (tApp (tConstruct iv_ind 0 []) g_A) a.
Definition g_cmfix : mfixpoint term :=
  [{| dname := si_na; dtype := g_RA; dbody := g_mkRA f3_idRF; rarg := 0 |}].
Definition g_cofix : term := tCoFix g_cmfix 0.
Definition g_ci : case_info :=
  {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := false |}.
Definition g_p : predicate term :=
  {| pparams := [g_A]; puinst := []; pcontext := ind_predicate_context iv_ind iv_mdecl iv_idecl;
     preturn := g_RA |}.
Definition g_br : branch term :=
  {| bcontext := cstr_branch_context iv_ind iv_mdecl iv_cdecl; bbody := g_mkRA (tRel 0) |}.
Definition g_t : term := tCase g_ci g_p g_cofix [g_br].
Definition g_T : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl g_p) (preturn g_p))
    ([] ++ [g_cofix]).
Definition g_bty : term := tApp (tLambda fo_zna g_RA g_RA) (g_mkRA (tRel 0)).

Lemma g_A_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E g_A : si_P.
Proof. exact (f3_RFRF_typed Γ). Qed.

Lemma g_RA_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E g_RA : si_P.
Proof. intros h. exact (iv_RX_typed Γ g_A h (g_A_typed Γ h)). Qed.

(** [mkR A : A -> R A]. *)
Lemma g_mkR_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tApp (tConstruct iv_ind 0 []) g_A : tProd iv_fna g_A g_RA.
Proof.
  intros h.
  exact (typeE_App _ _ (tConstruct iv_ind 0 []) si_na si_P _ _ g_A (iv_mkR_ty_typed Γ h)
           (iv_mkR_typed Γ h) (g_A_typed Γ h)).
Qed.

Lemma g_mkR_ty_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tProd iv_fna g_A g_RA : tSort (Sort.sort_of_product sProp sProp).
Proof.
  intros h. apply typeE_Prod; [exact (iv_vass_s iv_Σ Γ iv_fna g_A sProp (g_A_typed Γ h) eq_refl)|].
  exact (g_RA_typed _ (iv_wf_vass iv_Σ Γ iv_fna g_A sProp h (g_A_typed Γ h) eq_refl)).
Qed.

(** [mkR A a : R A] for [a : A]. *)
Lemma g_mkRA_typed (Γ : context) a : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E a : g_A ->
  iv_Σ ;;; Γ |-E g_mkRA a : g_RA.
Proof.
  intros h ha.
  exact (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) g_A) iv_fna g_A g_RA _ a
           (g_mkR_ty_typed Γ h) (g_mkR_typed Γ h) ha).
Qed.

Definition g_Γc : context := [vass si_na g_RA].

Lemma g_wf_Γc : wf_localE iv_Σ g_Γc.
Proof. exact (iv_wf_vass iv_Σ [] si_na g_RA sProp localenv_nil (g_RA_typed [] localenv_nil) eq_refl). Qed.

Lemma g_cofix_body_typed : iv_Σ ;;; g_Γc |-E g_mkRA f3_idRF : lift0 1 g_RA.
Proof. exact (g_mkRA_typed g_Γc f3_idRF g_wf_Γc (f3_idRF_typed g_Γc g_wf_Γc)). Qed.

Lemma g_cofix_guard : cofix_guard iv_Σ [] g_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ [] g_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma g_wf_cofix : wf_cofixpointE iv_Σ [] g_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists g_RA. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma g_cofix_typed : iv_Σ ;;; [] |-E g_cofix : g_RA.
Proof.
  refine (typeE_CoFix _ _ g_cmfix 0 _ localenv_nil g_cofix_guard eq_refl _ _ g_wf_cofix).
  - constructor; [|constructor].
    exact (iv_vass iv_Σ [] si_na g_RA sProp (g_RA_typed [] localenv_nil) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef iv_Σ g_Γc si_na (g_mkRA f3_idRF) (lift0 1 g_RA) sProp g_cofix_body_typed
             (g_RA_typed g_Γc g_wf_Γc) eq_refl).
Qed.

Lemma g_wf_Γz : wf_localE iv_Σ ([] ,, vass fo_zna g_RA).
Proof. exact (iv_wf_vass iv_Σ [] fo_zna g_RA sProp localenv_nil (g_RA_typed [] localenv_nil) eq_refl). Qed.

Lemma g_wf_Γb : wf_localE iv_Σ ([] ,, vass iv_fna g_A).
Proof. exact (iv_wf_vass iv_Σ [] iv_fna g_A sProp localenv_nil (g_A_typed [] localenv_nil) eq_refl). Qed.

Lemma g_pret_typed : iv_Σ ;;; [] ,, vass fo_zna g_RA |-E g_RA : tSort sProp.
Proof. exact (g_RA_typed _ g_wf_Γz). Qed.

Lemma g_wf_p : wf_predicate iv_mdecl iv_idecl g_p.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma g_wf_br : wf_branch iv_cdecl g_br.
Proof. constructor; [reflexivity|constructor]. Qed.

Lemma g_ctx_inst : ctx_inst (typingE iv_Σ) [] [g_A] [vass si_na si_P].
Proof. econstructor; [|constructor]. exact (g_A_typed [] localenv_nil). Qed.

Lemma g_case_side :
  case_side_conditions (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) iv_Σ [] g_ci g_p sProp
    iv_mdecl iv_idecl [] (case_predicate_context iv_ind iv_mdecl iv_idecl g_p).
Proof.
  constructor.
  - reflexivity.
  - exact g_wf_p.
  - reflexivity.
  - exact g_wf_Γz.
  - exact (alpha_eq_reflexive (pcontext g_p)).
  - reflexivity.
  - reflexivity.
  - exact g_ctx_inst.
  - reflexivity.
Qed.

(** The branch type [(fun z : R A => R A) (mkR A b) : Prop] and the body [mkR A b] at it. *)
Lemma g_bty_typed : iv_Σ ;;; [] ,, vass iv_fna g_A |-E g_bty : tSort sProp.
Proof.
  have w := iv_wf_vass iv_Σ ([] ,, vass iv_fna g_A) fo_zna g_RA sProp g_wf_Γb (g_RA_typed _ g_wf_Γb) eq_refl.
  refine (typeE_App _ _ (tLambda fo_zna g_RA g_RA) fo_zna g_RA si_P
            (Sort.sort_of_product sProp (Sort.super sProp)) (g_mkRA (tRel 0)) _ _ _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ _ fo_zna g_RA sProp (g_RA_typed _ g_wf_Γb) eq_refl)|].
    exact (iv_P_typed iv_Σ _ w).
  - apply typeE_Lambda; [exact (iv_vass iv_Σ _ fo_zna g_RA sProp (g_RA_typed _ g_wf_Γb) eq_refl)|].
    exact (g_RA_typed _ w).
  - exact (g_mkRA_typed _ (tRel 0) g_wf_Γb (typeE_Rel _ _ 0 (vass iv_fna g_A) g_wf_Γb eq_refl)).
Qed.

Lemma g_br_typed : iv_Σ ;;; [] ,, vass iv_fna g_A |-E g_mkRA (tRel 0) : g_bty.
Proof.
  refine (typeE_Cumul _ _ _ g_RA _ sProp _ g_bty_typed _).
  - exact (g_mkRA_typed _ (tRel 0) g_wf_Γb (typeE_Rel _ _ 0 (vass iv_fna g_A) g_wf_Γb eq_refl)).
  - apply cumulE_Sym. exact (cumulE_beta _ _ Conv fo_zna g_RA g_RA (g_mkRA (tRel 0))).
Qed.

Lemma g_case_brs :
  case_branch_typing (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) [] g_ci g_p sProp iv_mdecl iv_idecl
    (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl g_p) (preturn g_p))
    [g_br].
Proof.
  constructor.
  - constructor; [exact g_wf_br|constructor].
  - constructor; [|constructor].
    split; [exact (alpha_eq_reflexive _)|]. cbv zeta. split; [|split].
    + exact g_wf_Γb.
    + exact g_br_typed.
    + exact g_bty_typed.
Qed.

Lemma g_t_typed : iv_Σ ;;; [] |-E g_t : g_T.
Proof.
  eapply (typeE_Case _ _ g_ci g_p g_cofix [g_br] [] sProp iv_mdecl iv_idecl).
  - exact iv_declared_inductive.
  - exact g_pret_typed.
  - exact g_cofix_typed.
  - exact g_case_side.
  - exact g_case_brs.
Qed.

Lemma g_t_typed_RA : iv_Σ ;;; [] |-E g_t : g_RA.
Proof.
  refine (typeE_Cumul _ _ g_t g_T g_RA sProp g_t_typed (g_RA_typed [] localenv_nil) _).
  exact (cumulE_beta _ _ Cumul fo_zna g_RA g_RA g_cofix).
Qed.

Lemma g_axiom_free : axiom_free iv_Σ.
Proof.
  intros c decl h. exfalso. red in h. cbn in h.
  destruct h as [h|h]; [discriminate h|exact h].
Qed.

Lemma g_afv : axiom_free_value iv_Σ [] g_t.
Proof. reflexivity. Qed.

Lemma g_whne : whne RedFlags.default iv_Σ [] g_t.
Proof.
  change g_t with (tCase g_ci g_p (mkApps (tCoFix g_cmfix 0) []) [g_br]).
  now apply whne_case_cofix_dep.
Qed.

Lemma g_whnf : whnf RedFlags.default iv_Σ [] g_t.
Proof. apply whnf_ne. exact g_whne. Qed.

Lemma g_wcbv_stuck : wcbv_stuck iv_Σ g_t.
Proof.
  change g_t with (tCase g_ci g_p (mkApps (tCoFix g_cmfix 0) []) [g_br]).
  now apply wcbv_stuck_cofix_case.
Qed.

Lemma g_no_eval u : eval iv_Σ g_t u -> False.
Proof. exact (wcbv_stuck_no_eval (Σ := iv_Σ) g_wcbv_stuck u). Qed.

Lemma g_stuck : stuck_cofix_case g_t.
Proof.
  change g_t with (tCase g_ci g_p (mkApps (tCoFix g_cmfix 0) []) [g_br]).
  now apply stuck_cofix_case_scrut.
Qed.

Lemma g_head_not_discr : construct_cofix_discr (head g_t) = false.
Proof. exact (stuck_cofix_case_head g_t g_stuck). Qed.

(** *** [g_t] is [red1]-normal, in [iv_Σ] and the empty context: no step at its root (the flag
    blocks [red_cofix_case], the scrutinee is no constructor application) and none inside its
    parameter, return predicate, scrutinee or branch. *)

Lemma l45_OnOne2_single {A} (P : A -> A -> Type) x l' : OnOne2 P [x] l' -> ∑ y, P x y.
Proof.
  intros h. inversion h; subst.
  - eexists; eassumption.
  - match goal with H : OnOne2 _ [] _ |- _ => inversion H end.
Qed.

Lemma l45_mkApps_construct_cofix i n u args m k :
  mkApps (tConstruct i n u) args = tCoFix m k -> False.
Proof.
  destruct args using rev_case; cbn; [discriminate|].
  rewrite mkApps_app; cbn; discriminate.
Qed.

Lemma l45_Ind_normal (S : global_env) Γ i u v : red1 S Γ (tInd i u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma l45_Construct_normal (S : global_env) Γ i n u v : red1 S Γ (tConstruct i n u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma l45_Rel0_normal (S : global_env) Γ v :
  option_map decl_body (nth_error Γ 0) = Some None -> red1 S Γ (tRel 0) v -> False.
Proof.
  intros hn H. inv_red H.
  match goal with e : option_map decl_body _ = _ |- _ => rewrite hn in e; discriminate e end.
Qed.

Lemma l45_False_normal (S : global_env) Γ v : red1 S Γ iv_False v -> False.
Proof.
  unfold iv_False. intros H. inv_red H.
  - eapply red_normal_Sort; eassumption.
  - eapply red_normal_Rel0; eassumption.
Qed.

Lemma l45_RF_normal (S : global_env) Γ v : red1 S Γ iv_RF v -> False.
Proof.
  unfold iv_RF, iv_R. intros H. inv_red H.
  - eapply l45_Ind_normal; eassumption.
  - eapply l45_False_normal; eassumption.
Qed.

Lemma l45_A_normal (S : global_env) Γ v : red1 S Γ g_A v -> False.
Proof. unfold g_A. intros H. inv_red H; eapply l45_RF_normal; eassumption. Qed.

Lemma l45_RA_normal (S : global_env) Γ v : red1 S Γ g_RA v -> False.
Proof.
  unfold g_RA, iv_R. intros H. inv_red H.
  - eapply l45_Ind_normal; eassumption.
  - eapply l45_A_normal; eassumption.
Qed.

Lemma l45_idRF_normal (S : global_env) Γ v : red1 S Γ f3_idRF v -> False.
Proof.
  unfold f3_idRF. revert v. apply red_normal_lam.
  - intros w. apply l45_RF_normal.
  - intros w. apply red_normal_Rel0.
Qed.

Lemma l45_mkRA_normal (S : global_env) Γ a :
  (forall v, red1 S Γ a v -> False) -> forall v, red1 S Γ (g_mkRA a) v -> False.
Proof.
  intros ha v. unfold g_mkRA. intros H. inv_red H.
  - match goal with h : red1 _ _ (tApp _ _) _ |- _ => inv_red h end.
    + eapply l45_Construct_normal; eassumption.
    + eapply l45_A_normal; eassumption.
  - eapply ha; eassumption.
Qed.

Lemma l45_cofix_normal (S : global_env) Γ v : red1 S Γ g_cofix v -> False.
Proof.
  unfold g_cofix. intros H. inv_red H.
  - match goal with h : OnOne2 _ _ _ |- _ =>
      unfold g_cmfix in h; apply l45_OnOne2_single in h as [y [hy _]] end.
    eapply l45_RA_normal; exact hy.
  - match goal with h : OnOne2 _ _ _ |- _ =>
      unfold g_cmfix in h; apply l45_OnOne2_single in h as [y [hy _]] end.
    eapply (l45_mkRA_normal _ _ f3_idRF (l45_idRF_normal _ _)); exact hy.
Qed.

Lemma l45_g_t_normal v : red1 iv_Σ [] g_t v -> False.
Proof.
  unfold g_t, g_cofix. intros H. inv_red H.
  all: first
    [ match goal with e : mkApps (tConstruct _ _ _) _ = tCoFix _ _ |- _ =>
        exact (l45_mkApps_construct_cofix _ _ _ _ _ _ e) end
    | match goal with h : is_true (ci_cofix_nondep _) |- _ => cbn in h; discriminate h end
    | match goal with h : OnOne2 (fun t u => red1 _ _ t u) _ _ |- _ =>
        cbn in h; apply l45_OnOne2_single in h as [y hy]; eapply l45_A_normal; exact hy end
    | match goal with h : red1 _ _ (preturn _) _ |- _ => eapply l45_RA_normal; exact h end
    | match goal with h : red1 _ _ (tCoFix _ _) _ |- _ => eapply l45_cofix_normal; exact h end
    | match goal with h : OnOne2 _ _ _ |- _ =>
        apply l45_OnOne2_single in h as [y [hy _]];
        eapply (l45_mkRA_normal _ _ (tRel 0)); [|exact hy];
        intros w; apply l45_Rel0_normal; reflexivity end ].
Qed.

Lemma l45_g_t_closed : on_free_vars (fun _ => false) g_t.
Proof. reflexivity. Qed.

(* INSTANCE IMPOSSIBLE: the proof is an induction on the whne derivation; every leaf but whne_case_cofix_dep is refuted from the typing and axiom_free_value premises, and each remaining step maps its whne constructor to the matching stuck_cofix_case constructor (app, case, proj, fixapp; case_cofix_dep to scrut), so the conclusion is the instance's own whne derivation translated; reaching a refuted leaf needs an uninhabited conclusion
   TARGET PCUICClassificationEta.wh_neutral_empty_genE *)
Definition wh_neutral_empty_genE_inst : stuck_cofix_case g_t :=
  wh_neutral_empty_genE (Σ := iv_Σ) (wfΣ := iv_wfE) [] [] g_t g_RA g_afv g_whne g_t_typed_RA eq_refl.

(* INSTANCE IMPOSSIBLE: the proof is an induction on the whne derivation; every leaf but whne_case_cofix_dep is refuted from the typing and axiom_free_value premises, and each remaining step maps its whne constructor to the matching stuck_cofix_case constructor (app, case, proj, fixapp; case_cofix_dep to scrut), so the conclusion is the instance's own whne derivation translated; reaching a refuted leaf needs an uninhabited conclusion
   TARGET PCUICClassificationEta.wh_neutral_emptyE *)
Definition wh_neutral_emptyE_inst : stuck_cofix_case g_t :=
  wh_neutral_emptyE (Σ := iv_Σ) (wfΣ := iv_wfE) g_t g_RA g_afv g_whne g_t_typed_RA.

(* INSTANCE IMPOSSIBLE: the proof splits on wh_normal; at whnf_cstrapp and whnf_cofixapp the left disjunct is computed from the head, and at whnf_ne the right disjunct stuck_cofix_case t is the instance's own whne derivation translated constructor by constructor (wh_neutral_emptyE); every other branch, and every neutral leaf but a case on a cofixpoint, is refuted from the typing and axiom_free premises, so reaching one needs an uninhabited conclusion
   TARGET PCUICClassificationEta.whnf_classification'E *)
Definition whnf_classification'E_stuck_inst :=
  whnf_classification'E (Σ := iv_Σ) (wfΣ := iv_wfE) g_t iv_ind [] [g_A] g_afv g_whnf g_t_typed_RA.

(* INSTANCE IMPOSSIBLE: the proof splits on wh_normal; at whnf_cstrapp and whnf_cofixapp the left disjunct is computed from the head, and at whnf_ne the right disjunct stuck_cofix_case t is the instance's own whne derivation translated constructor by constructor (wh_neutral_emptyE); every other branch, and every neutral leaf but a case on a cofixpoint, is refuted from the typing and axiom_free premises, so reaching one needs an uninhabited conclusion
   TARGET PCUICClassificationEta.whnf_classificationE *)
Definition whnf_classificationE_stuck_inst :=
  whnf_classificationE (Σ := iv_Σ) (wfΣ := iv_wfE) g_t iv_ind [] [g_A] g_axiom_free g_whnf g_t_typed_RA.

(** The instance lands in the disjunct BET-339 added. *)
Lemma g_whnf_classification_stuck : stuck_cofix_case g_t.
Proof.
  destruct whnf_classification'E_stuck_inst as [h|s]; [|exact s].
  exfalso. rewrite g_head_not_discr in h. discriminate h.
Qed.

(* INSTANCE NONDEGEN PCUICEtaF0Land3Instances.progressE_stuck_inst_nondeg
   TARGET PCUICProgressEta.progressE
   [g_t] takes no step and has no value; the instance lands in the disjunct [wcbv_stuck]. *)
Definition progressE_stuck_inst :=
  progressE iv_Σ g_t g_RA g_axiom_free iv_wfE g_t_typed_RA.

(* INSTANCE NONDEGEN PCUICEtaF0Land3Instances.red1_progressE_inst_nondeg
   TARGET PCUICProgressEta.red1_progressE *)
Definition red1_progressE_inst :=
  red1_progressE (Σ := iv_Σ) (wfΣ := iv_wfE) g_axiom_free g_t g_RA g_t_typed_RA.

(** The pre-BET-339 forms of the restated rows are FALSE on integ-all8: [g_t] refutes them.
    These are why [PCUICClassificationEta] and [PCUICProgressEta] restate them as base does. *)
Lemma wh_neutral_emptyE_old_false :
  (forall (Σ : global_env_ext) (wfΣ : wfE Σ) t ty,
     axiom_free_value Σ [] t -> whne RedFlags.default Σ [] t -> Σ ;;; [] |-E t : ty -> False) -> False.
Proof. intros h. exact (h iv_Σ iv_wfE g_t g_RA g_afv g_whne g_t_typed_RA). Qed.

Lemma whnf_classification'E_old_false :
  (forall (Σ : global_env_ext) (wfΣ : wfE Σ) t i u args,
     axiom_free_value Σ [] t -> whnf RedFlags.default Σ [] t ->
     Σ ;;; [] |-E t : mkApps (tInd i u) args -> construct_cofix_discr (head t)) -> False.
Proof.
  intros h. have e := h iv_Σ iv_wfE g_t iv_ind [] [g_A] g_afv g_whnf g_t_typed_RA.
  rewrite g_head_not_discr in e. discriminate e.
Qed.

(** [g_t] takes no weak call-by-value step: the flag blocks [wcbv_red_cofix_case], the
    scrutinee is not a constructor application, and a cofixpoint takes no step. *)
Lemma g_no_wcbv_step t' : iv_Σ ⊢ g_t ⇝ᵥ t' -> False.
Proof.
  unfold g_t, g_cofix. intros st. inversion st; subst.
  all: try solve [solve_discr].
  all: try solve [match goal with h : _ ⊢ tCoFix _ _ ⇝ᵥ _ |- _ => inversion h end].
  all: try solve [match goal with h : is_true (ci_cofix_nondep _) |- _ => cbn in h; discriminate h end].
Qed.

Lemma progressE_old_false :
  (forall (Σ : global_env_ext) t T, axiom_free Σ -> wfE Σ -> Σ ;;; [] |-E t : T ->
     {t' & Σ ⊢ t ⇝ᵥ t'} + PCUICWcbvEval.value Σ t) -> False.
Proof.
  intros h. destruct (h iv_Σ g_t g_RA g_axiom_free iv_wfE g_t_typed_RA) as [[t' st]|hv].
  - exact (g_no_wcbv_step t' st).
  - exact (g_no_eval g_t (value_final _ _ hv)).
Qed.

(** ** 3. The T8 probe on a type-level case of the region *)

Definition t8_ici : case_info :=
  {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition t8_ip : predicate term :=
  {| pparams := [iv_False]; puinst := []; pcontext := ind_predicate_context iv_ind iv_mdecl iv_idecl;
     preturn := tSort (Sort.super sProp) |}.
Definition t8_ibr : branch term :=
  {| bcontext := cstr_branch_context iv_ind iv_mdecl iv_cdecl; bbody := tSort sProp |}.
Definition t8_inner (s : term) : term := tCase t8_ici t8_ip s [t8_ibr].
Definition t8_oci : case_info :=
  {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := false |}.
Definition t8_op : predicate term :=
  {| pparams := [iv_False]; puinst := []; pcontext := ind_predicate_context iv_ind iv_mdecl iv_idecl;
     preturn := t8_inner (tRel 0) |}.
Definition t8_obr : branch term :=
  {| bcontext := cstr_branch_context iv_ind iv_mdecl iv_cdecl; bbody := iv_RF |}.
Definition t8_scrut : term := fo_mkRF (tProj iv_proj (tRel 0)).
Definition t8_T : term := tCase t8_oci t8_op t8_scrut [t8_obr].
Definition t8_ibty : term := tApp (tLambda fo_zna iv_RF (tSort (Sort.super sProp))) (fo_mkRF (tRel 0)).
Definition t8_obty : term := tApp (tLambda fo_zna iv_RF (t8_inner (tRel 0))) (fo_mkRF (tRel 0)).

Lemma t8_wf_super1 : wf_sort iv_Σ (Sort.super sProp).
Proof. apply/(PCUICWfUniverses.wf_sort_reflect iv_Σ). reflexivity. Qed.

Lemma t8_wf_super2 : wf_sort iv_Σ (Sort.super (Sort.super sProp)).
Proof. apply/(PCUICWfUniverses.wf_sort_reflect iv_Σ). reflexivity. Qed.

Lemma t8_wf_super3 : wf_sort iv_Σ (Sort.super (Sort.super (Sort.super sProp))).
Proof. apply/(PCUICWfUniverses.wf_sort_reflect iv_Σ). reflexivity. Qed.

Lemma t8_Type1_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)).
Proof. intros h. exact (typeE_Sort _ _ _ h t8_wf_super1). Qed.

Lemma t8_Type2_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tSort (Sort.super (Sort.super sProp)) : tSort (Sort.super (Sort.super (Sort.super sProp))).
Proof. intros h. exact (typeE_Sort _ _ _ h t8_wf_super2). Qed.

Lemma t8_wf_z (Γ : context) : wf_localE iv_Σ Γ -> wf_localE iv_Σ (Γ ,, vass fo_zna iv_RF).
Proof. intros h. exact (iv_wf_vass iv_Σ Γ fo_zna iv_RF sProp h (iv_RF_typed Γ h) eq_refl). Qed.

Lemma t8_wf_b (Γ : context) : wf_localE iv_Σ Γ -> wf_localE iv_Σ (Γ ,, vass iv_fna iv_False).
Proof. intros h. exact (iv_wf_vass iv_Σ Γ iv_fna iv_False sProp h (iv_False_typed iv_Σ Γ h) eq_refl). Qed.

(** [mkR F b : R F] for the branch variable [b : F]. *)
Lemma t8_mkRb_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ ,, vass iv_fna iv_False |-E fo_mkRF (tRel 0) : iv_RF.
Proof.
  intros h. have hb := t8_wf_b Γ h.
  have hF := iv_False_typed iv_Σ _ hb.
  have wF := iv_wf_vass iv_Σ _ iv_fna iv_False sProp hb hF eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tRel 0) _ (iv_mkRF_typed _ hb) _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ _ iv_fna iv_False sProp hF eq_refl)|].
    exact (iv_RF_typed _ wF).
  - exact (typeE_Rel _ _ 0 (vass iv_fna iv_False) hb eq_refl).
Qed.

Lemma t8_wf_ip : wf_predicate iv_mdecl iv_idecl t8_ip.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma t8_wf_op : wf_predicate iv_mdecl iv_idecl t8_op.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma t8_wf_ibr : wf_branch iv_cdecl t8_ibr.
Proof. constructor; [reflexivity|constructor]. Qed.

Lemma t8_wf_obr : wf_branch iv_cdecl t8_obr.
Proof. constructor; [reflexivity|constructor]. Qed.

Lemma t8_ctx_inst (Γ : context) : wf_localE iv_Σ Γ ->
  ctx_inst (typingE iv_Σ) Γ [iv_False] [vass si_na si_P].
Proof. intros h. econstructor; [|constructor]. exact (iv_False_typed iv_Σ Γ h). Qed.

(** The inner case, in any context [Δ, z : R F]. *)
Section Inner.
  Context (Δ : context) (wfΔ : wf_localE iv_Σ Δ).

  Let Δz := Δ ,, vass fo_zna iv_RF.
  Let wfΔz : wf_localE iv_Σ Δz := t8_wf_z Δ wfΔ.

  Lemma t8_ibty_typed : iv_Σ ;;; Δz ,, vass iv_fna iv_False |-E t8_ibty : tSort (Sort.super (Sort.super sProp)).
  Proof.
    have hb := t8_wf_b Δz wfΔz.
    have w := t8_wf_z _ hb.
    refine (typeE_App _ _ (tLambda fo_zna iv_RF (tSort (Sort.super sProp))) fo_zna iv_RF
              (tSort (Sort.super (Sort.super sProp)))
              (Sort.sort_of_product sProp (Sort.super (Sort.super (Sort.super sProp))))
              (fo_mkRF (tRel 0)) _ _ (t8_mkRb_typed Δz wfΔz)).
    - apply typeE_Prod; [exact (iv_vass_s iv_Σ _ fo_zna iv_RF sProp (iv_RF_typed _ hb) eq_refl)|].
      exact (t8_Type2_typed _ w).
    - apply typeE_Lambda; [exact (iv_vass iv_Σ _ fo_zna iv_RF sProp (iv_RF_typed _ hb) eq_refl)|].
      exact (t8_Type1_typed _ w).
  Qed.

  Lemma t8_ibr_typed : iv_Σ ;;; Δz ,, vass iv_fna iv_False |-E tSort sProp : t8_ibty.
  Proof.
    have hb := t8_wf_b Δz wfΔz.
    refine (typeE_Cumul _ _ _ (tSort (Sort.super sProp)) _ (Sort.super (Sort.super sProp))
              (iv_P_typed iv_Σ _ hb) t8_ibty_typed _).
    apply cumulE_Sym.
    exact (cumulE_beta _ _ Conv fo_zna iv_RF (tSort (Sort.super sProp)) (fo_mkRF (tRel 0))).
  Qed.

  Lemma t8_icase_side :
    case_side_conditions (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) iv_Σ Δz t8_ici t8_ip
      (Sort.super (Sort.super sProp)) iv_mdecl iv_idecl []
      (case_predicate_context iv_ind iv_mdecl iv_idecl t8_ip).
  Proof.
    constructor.
    - reflexivity.
    - exact t8_wf_ip.
    - reflexivity.
    - exact (t8_wf_z _ wfΔz).
    - exact (alpha_eq_reflexive (pcontext t8_ip)).
    - reflexivity.
    - reflexivity.
    - exact (t8_ctx_inst _ wfΔz).
    - reflexivity.
  Qed.

  Lemma t8_icase_brs :
    case_branch_typing (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) Δz t8_ici t8_ip
      (Sort.super (Sort.super sProp)) iv_mdecl iv_idecl
      (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl t8_ip) (preturn t8_ip))
      [t8_ibr].
  Proof.
    constructor.
    - constructor; [exact t8_wf_ibr|constructor].
    - constructor; [|constructor].
      split; [exact (alpha_eq_reflexive _)|]. cbv zeta. split; [|split].
      + exact (t8_wf_b _ wfΔz).
      + exact t8_ibr_typed.
      + exact t8_ibty_typed.
  Qed.

  Lemma t8_inner_typed :
    iv_Σ ;;; Δz |-E t8_inner (tRel 0) :
      mkApps (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl t8_ip) (preturn t8_ip))
        ([] ++ [tRel 0]).
  Proof.
    eapply (typeE_Case _ _ t8_ici t8_ip (tRel 0) [t8_ibr] [] (Sort.super (Sort.super sProp)) iv_mdecl iv_idecl).
    - exact iv_declared_inductive.
    - exact (t8_Type1_typed _ (t8_wf_z _ wfΔz)).
    - exact (typeE_Rel _ _ 0 (vass fo_zna iv_RF) wfΔz eq_refl).
    - exact t8_icase_side.
    - exact t8_icase_brs.
  Qed.

  Lemma t8_inner_sort : iv_Σ ;;; Δz |-E t8_inner (tRel 0) : tSort (Sort.super sProp).
  Proof.
    refine (typeE_Cumul _ _ _ _ (tSort (Sort.super sProp)) (Sort.super (Sort.super sProp))
              t8_inner_typed (t8_Type1_typed _ wfΔz) _).
    exact (cumulE_beta _ _ Cumul fo_zna iv_RF (tSort (Sort.super sProp)) (tRel 0)).
  Qed.

End Inner.

(** The outer case, in [iv_Γr := x : R F]. *)
Definition t8_Γb : context := iv_Γr ,, vass iv_fna iv_False.

Lemma t8_wf_Γb : wf_localE iv_Σ t8_Γb.
Proof. exact (t8_wf_b iv_Γr iv_wf_Γr). Qed.

Lemma t8_obty_typed : iv_Σ ;;; t8_Γb |-E t8_obty : tSort (Sort.super sProp).
Proof.
  have w := t8_wf_z _ t8_wf_Γb.
  refine (typeE_App _ _ (tLambda fo_zna iv_RF (t8_inner (tRel 0))) fo_zna iv_RF
            (tSort (Sort.super sProp)) (Sort.sort_of_product sProp (Sort.super (Sort.super sProp)))
            (fo_mkRF (tRel 0)) _ _ (t8_mkRb_typed iv_Γr iv_wf_Γr)).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ _ fo_zna iv_RF sProp (iv_RF_typed _ t8_wf_Γb) eq_refl)|].
    exact (t8_Type1_typed _ w).
  - apply typeE_Lambda; [exact (iv_vass iv_Σ _ fo_zna iv_RF sProp (iv_RF_typed _ t8_wf_Γb) eq_refl)|].
    exact (t8_inner_sort _ t8_wf_Γb).
Qed.

(** [t8_obty] β-reduces to the inner case on [mkR F b], which ι-reduces to [Prop]. *)
Lemma t8_obty_conv : cumulSpecE0 iv_Σ t8_Γb Conv t8_obty (tSort sProp).
Proof.
  refine (cumulE_Trans _ _ Conv _ (t8_inner (fo_mkRF (tRel 0))) _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - exact (cumulE_beta _ _ Conv fo_zna iv_RF (t8_inner (tRel 0)) (fo_mkRF (tRel 0))).
  - exact (cumulE_iota _ _ Conv t8_ici 0 [] [iv_False; tRel 0] t8_ip [t8_ibr] t8_ibr eq_refl eq_refl).
Qed.

Lemma t8_obr_typed : iv_Σ ;;; t8_Γb |-E iv_RF : t8_obty.
Proof.
  refine (typeE_Cumul _ _ _ si_P _ (Sort.super sProp) (iv_RF_typed _ t8_wf_Γb) t8_obty_typed _).
  apply cumulE_Sym. exact t8_obty_conv.
Qed.

Lemma t8_ocase_side :
  case_side_conditions (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) iv_Σ iv_Γr t8_oci t8_op
    (Sort.super sProp) iv_mdecl iv_idecl [] (case_predicate_context iv_ind iv_mdecl iv_idecl t8_op).
Proof.
  constructor.
  - reflexivity.
  - exact t8_wf_op.
  - reflexivity.
  - exact (t8_wf_z _ iv_wf_Γr).
  - exact (alpha_eq_reflexive (pcontext t8_op)).
  - reflexivity.
  - reflexivity.
  - exact (t8_ctx_inst _ iv_wf_Γr).
  - reflexivity.
Qed.

Lemma t8_ocase_brs :
  case_branch_typing (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) iv_Γr t8_oci t8_op (Sort.super sProp)
    iv_mdecl iv_idecl
    (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl t8_op) (preturn t8_op))
    [t8_obr].
Proof.
  constructor.
  - constructor; [exact t8_wf_obr|constructor].
  - constructor; [|constructor].
    split; [exact (alpha_eq_reflexive _)|]. cbv zeta. split; [|split].
    + exact t8_wf_Γb.
    + exact t8_obr_typed.
    + exact t8_obty_typed.
Qed.

Lemma t8_scrut_typed : iv_Σ ;;; iv_Γr |-E t8_scrut : iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ iv_Γr iv_wf_Γr.
  have wF := iv_wf_vass iv_Σ iv_Γr iv_fna iv_False sProp iv_wf_Γr hF eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tProj iv_proj (tRel 0)) _ (iv_mkRF_typed iv_Γr iv_wf_Γr)
            iv_proj_typed).
  apply typeE_Prod; [exact (iv_vass_s iv_Σ iv_Γr iv_fna iv_False sProp hF eq_refl)|].
  exact (iv_RF_typed _ wF).
Qed.

Lemma t8_T_typed :
  iv_Σ ;;; iv_Γr |-E t8_T :
    mkApps (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl t8_op) (preturn t8_op))
      ([] ++ [t8_scrut]).
Proof.
  eapply (typeE_Case _ _ t8_oci t8_op t8_scrut [t8_obr] [] (Sort.super sProp) iv_mdecl iv_idecl).
  - exact iv_declared_inductive.
  - exact (t8_inner_sort _ iv_wf_Γr).
  - exact t8_scrut_typed.
  - exact t8_ocase_side.
  - exact t8_ocase_brs.
Qed.

(** [t8_T : Prop]: its case type β-reduces to the inner case on [mkR F x.(f)], which
    ι-reduces to [Prop]. *)
Lemma t8_T_sort : iv_Σ ;;; iv_Γr |-E t8_T : tSort sProp.
Proof.
  refine (typeE_Cumul _ _ _ _ (tSort sProp) (Sort.super sProp) t8_T_typed (iv_P_typed iv_Σ _ iv_wf_Γr) _).
  refine (cumulE_Trans _ _ Cumul _ (t8_inner t8_scrut) _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - exact (cumulE_beta _ _ Cumul fo_zna iv_RF (t8_inner (tRel 0)) t8_scrut).
  - exact (cumulE_iota _ _ Cumul t8_ici 0 [] [iv_False; tProj iv_proj (tRel 0)] t8_ip [t8_ibr] t8_ibr
             eq_refl eq_refl).
Qed.

(** [t8_T] ι-reduces to [R F]. *)
Lemma t8_T_conv : ws_cumul_pbE Cumul iv_Σ iv_Γr t8_T (mkApps (tInd iv_ind []) [iv_False]).
Proof.
  apply (into_ws_cumul_pbE_spec (Σ := iv_Σ)); [|reflexivity|reflexivity|reflexivity].
  exact (cumulE_iota _ _ Cumul t8_oci 0 [] [iv_False; tProj iv_proj (tRel 0)] t8_op [t8_obr] t8_obr
           eq_refl eq_refl).
Qed.

(* INSTANCE NOT-BUILT: degenerate, a single step given as a cumulativity and returned: the input t8_T_conv is into_ws_cumul_pbE_spec of one root cumulE_iota step from t8_T to R F, and T8_Ind_r returns t8_T ⇝ R F, that step, with its universe and argument fields relating [] to [] and [iv_False] to [iv_False]; a cumulativity whose derivation contains an expansion, so that T8_Ind_r needs confluence, at an inductive application with a different argument (e.g. R ((λx. x) F)), would make it run; no non-degenerate witness built yet
   TARGET PCUICEtaT8Probe.T8_Ind_r *)
Definition t8_Ind_r_inst :=
  PCUICEtaT8Probe.T8_Ind_r (Σ := iv_Σ) iv_wfE iv_Γr Cumul t8_T iv_ind [] [iv_False] sProp iv_wfE
    t8_T_sort t8_T_conv.

(** Non-degeneracy. *)
Lemma t8_flag_unset : t8_oci.(ci_cofix_nondep) = false.
Proof. reflexivity. Qed.

Lemma t8_old_premise_fails :
  (isCoFinite (ind_finite iv_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn t8_op)) = false.
Proof. reflexivity. Qed.

Lemma t8_new_premise_holds :
  (isCoFinite (ind_finite iv_mdecl) ==>
   (t8_oci.(ci_cofix_nondep) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn t8_op))) = true.
Proof. reflexivity. Qed.

(** ** NONDEGEN lemmas of the instances of sections 1-3

  Each names the witness the instance passes and states why the run is in the region BET-339
  admits: a flag-unset case, a blocked shape, an empty old disjunct. Since the root ruling on the
  ship lineage (land6-review.md "Ship lineage (F0 + LAND12)"), no tag names
  [wh_neutral_empty_genE_inst_nondeg], [wh_neutral_emptyE_inst_nondeg],
  [whnf_classification'E_stuck_inst_nondeg], [whnf_classificationE_stuck_inst_nondeg] or
  [t8_Ind_r_inst_nondeg]: their instances are tagged IMPOSSIBLE or NOT-BUILT, and they stay as
  witnesses (WITNESSES line of the header). *)

Lemma f3_sr_nondeg :
  (red1 iv_Σ fo_Γ f3_t0 f3_t1 × stuck_cofix_case f3_t1 × (fo_ci.(ci_cofix_nondep) = false) ×
   ((isCoFinite (ind_finite iv_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p))
      = false))%type.
Proof. exact (f3_step, (f3_t1_stuck, (eq_refl, eq_refl))). Qed.

Lemma wh_neutral_empty_genE_inst_nondeg :
  (stuck_cofix_case g_t × (construct_cofix_discr (head g_t) = false) ×
   (g_ci.(ci_cofix_nondep) = false))%type.
Proof. exact (g_stuck, (g_head_not_discr, eq_refl)). Qed.

Lemma wh_neutral_emptyE_inst_nondeg :
  (stuck_cofix_case g_t × (construct_cofix_discr (head g_t) = false) ×
   (g_ci.(ci_cofix_nondep) = false))%type.
Proof. exact (g_stuck, (g_head_not_discr, eq_refl)). Qed.

Lemma whnf_classification'E_stuck_inst_nondeg :
  (stuck_cofix_case g_t × (construct_cofix_discr (head g_t) = false) ×
   (g_ci.(ci_cofix_nondep) = false))%type.
Proof. exact (g_stuck, (g_head_not_discr, eq_refl)). Qed.

Lemma whnf_classificationE_stuck_inst_nondeg :
  (stuck_cofix_case g_t × (construct_cofix_discr (head g_t) = false) ×
   (g_ci.(ci_cofix_nondep) = false))%type.
Proof. exact (g_stuck, (g_head_not_discr, eq_refl)). Qed.

Lemma progressE_stuck_inst_nondeg :
  (wcbv_stuck iv_Σ g_t × (forall t', iv_Σ ⊢ g_t ⇝ᵥ t' -> False) ×
   (forall v, eval iv_Σ g_t v -> False))%type.
Proof. exact (g_wcbv_stuck, (g_no_wcbv_step, g_no_eval)). Qed.

Lemma red1_progressE_inst_nondeg :
  (whne RedFlags.default iv_Σ [] g_t × (g_ci.(ci_cofix_nondep) = false))%type.
Proof. exact (g_whne, eq_refl). Qed.

Lemma t8_Ind_r_inst_nondeg :
  ((t8_oci.(ci_cofix_nondep) = false) ×
   ((isCoFinite (ind_finite iv_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn t8_op))
      = false) ×
   (t8_T = tCase t8_oci t8_op t8_scrut [t8_obr]))%type.
Proof. exact (eq_refl, (eq_refl, eq_refl)). Qed.

(** ** 4. LAND4/5 under BET-339

  *Canonicity.* [pcuic_canonicityE] (restated as base integ-all8: [+ stuck_cofix_case t']) on
  the closed blocked case [g_t : R A] of section 2, under base's normalization premise for [iv_Σ]
  (a section variable, never discharged, as in [PCUICCanonicityEtaInstances]). [g_t]'s own head
  is neither a constructor nor a cofixpoint, it is blocked, and it has no value
  ([pcuic_canonicityE_stuck_inst_nondeg], now a witness). Tagged NOT-BUILT (root ruling,
  land6-review.md "Ship lineage: the 9 remaining F0 rows", 05:59Z): an identical pair, since
  [g_t] is [red1]-normal; a closed term that reduces to a blocked case without being one would
  make the target run.

  Refutation of the pre-BET-339 [pcuic_canonicityE]: NOT BUILT. Obstacle, exactly: from the old
  conclusion at [g_t] one gets a [t'] whose head is a constructor or a cofixpoint with
  [convSpecE iv_Σ [] g_t t']; a contradiction needs a lemma that no E conversion relates a closed
  blocked case with such a term (the T8 probe's header records this only as an argument, "the
  chains from it keep the elimination"), and base's normalization premise for [iv_Σ] as a
  hypothesis. Neither is proved.

  *Consistency.* The instance of [pcuic_consistentE] stays in [PCUICConsistencyEtaInstances]
  ([cs_Σ], no coinductive block, where the new premise is proved by
  [no_closed_stuck_cofix_case_at_no_cofiniteE]: [cs_no_stuck]). The E twins of base's new helpers
  run here on the region's terms. The instances of the five typing inversions and of the two
  cofiniteness lemmas are tagged IMPOSSIBLE (root ruling): in every instance the conclusion is a
  piece or a field of the instance's own typing premise; their former NONDEGEN lemmas stay as
  witnesses. The two [no_closed_stuck_cofix_case_at] instances are tagged IMPOSSIBLE too (root
  ruling 05:59Z): each concludes [False] under a typing premise left as a hypothesis. *)

Section CanonicityStuck.

(* Base's normalization premise (by design, never discharged). *)
Context {nor : normalizing_flags} {nin_iv : PCUICSNEta.NormalizationInE iv_Σ}.

(* INSTANCE NOT-BUILT: degenerate, an identical pair: g_t is weak-head normal and red1-normal (l45_g_t_normal), so the target's normalization and its SR transport are the identity here and the conclusion is inhabited by (g_t, the input typing g_t_typed_RA, reflexivity, the stuck disjunct read off g_t); a closed term that reduces to a blocked case without being one (e.g. the case on a β-redex scrutinee) would make it run; no non-degenerate witness built yet
   TARGET PCUICCanonicityEta.pcuic_canonicityE *)
Definition pcuic_canonicityE_stuck_inst :=
  PCUICCanonicityEta.pcuic_canonicityE iv_Σ g_t iv_ind [] [g_A] g_axiom_free iv_wfE g_t_typed_RA.

End CanonicityStuck.

(** [g_t] is blocked, its head is neither a constructor nor a cofixpoint, it has no value, and
    it is [red1]-normal ([l45_g_t_normal]): the weak-head normal form the lemma's proof computes is
    [g_t] itself, which only the disjunct BET-339 added covers. *)
Lemma pcuic_canonicityE_stuck_inst_nondeg :
  (stuck_cofix_case g_t × (construct_cofix_discr (head g_t) = false) ×
   (forall v, eval iv_Σ g_t v -> False) × (forall v, red1 iv_Σ [] g_t v -> False))%type.
Proof. exact (g_stuck, (g_head_not_discr, (g_no_eval, l45_g_t_normal))). Qed.

(** The application [(λ y : R F. y) f3_cofix] is a real β-redex whose result is the cofixpoint. *)
Lemma l45_scrut_red : red1 iv_Σ fo_Γ f3_scrut f3_cofix.
Proof. exact (red_beta _ _ si_na iv_RF (tRel 0) f3_cofix). Qed.

(* INSTANCE IMPOSSIBLE: the proof inverts the typing derivation (dependent induction; a typeE_Cumul step passes the induction hypothesis through) and returns a sub-derivation of it, so in every environment and instance the conclusion is a piece of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_tApp_invE *)
Definition typing_tApp_invE_inst :=
  PCUICConsistencyEta.typing_tApp_invE (Σ := iv_Σ) (Γ := fo_Γ) (f := f3_idRF) (a := f3_cofix)
    f3_scrut_typed.

Lemma typing_tApp_invE_inst_nondeg : red1 iv_Σ fo_Γ (tApp f3_idRF f3_cofix) f3_cofix.
Proof. exact l45_scrut_red. Qed.

(* INSTANCE IMPOSSIBLE: the proof inverts the typing derivation (dependent induction; a typeE_Cumul step passes the induction hypothesis through) and returns a sub-derivation of it, so in every environment and instance the conclusion is a piece of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_tCase_scrutE *)
Definition typing_tCase_scrutE_inst :=
  PCUICConsistencyEta.typing_tCase_scrutE (Σ := iv_Σ) (Γ := []) (ci := g_ci) (p := g_p)
    (c := g_cofix) (brs := [g_br]) g_t_typed.

Lemma typing_tCase_scrutE_inst_nondeg : stuck_cofix_case (tCase g_ci g_p g_cofix [g_br]).
Proof. exact g_stuck. Qed.

(* INSTANCE IMPOSSIBLE: the proof inverts the typing derivation (dependent induction; a typeE_Cumul step passes the induction hypothesis through) and returns a sub-derivation of it, so in every environment and instance the conclusion is a piece of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_tProj_argE *)
Definition typing_tProj_argE_inst :=
  PCUICConsistencyEta.typing_tProj_argE (Σ := iv_Σ) (Γ := iv_Γr) (pr := iv_proj) (c := tRel 0)
    iv_proj_typed.

Lemma typing_tProj_argE_inst_nondeg :
  check_recursivity_kind (lookup_env iv_Σ) (inductive_mind iv_proj.(proj_ind)) CoFinite.
Proof. reflexivity. Qed.

(* INSTANCE IMPOSSIBLE: the proof inverts the typing derivation of tCoFix (a typeE_Cumul step passes the induction hypothesis through) down to its typeE_CoFix node and returns the ok field of its wf_cofixpointE premise, so in every instance the conclusion is a field of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_tCoFix_cofiniteE *)
Definition typing_tCoFix_cofiniteE_inst :=
  PCUICConsistencyEta.typing_tCoFix_cofiniteE (Σ := iv_Σ) (Γ := []) (mfix := g_cmfix) (idx := 0)
    g_cofix_typed.

Lemma typing_tCoFix_cofiniteE_inst_nondeg :
  ((option_map dtype (nth_error g_cmfix 0) = Some (mkApps (tInd iv_ind []) [g_A])) ×
   check_recursivity_kind (lookup_env iv_Σ) iv_kn CoFinite)%type.
Proof. split; reflexivity. Qed.

(* INSTANCE IMPOSSIBLE: the proof recurses on the argument list through typing_tApp_invE, which returns sub-derivations of the typing, so in every environment and instance the conclusion is a piece of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_mkApps_argE *)
Definition typing_mkApps_argE_inst :=
  PCUICConsistencyEta.typing_mkApps_argE (Σ := iv_Σ) (Γ := fo_Γ) (f := f3_idRF) (args := [f3_cofix])
    (n := 0) (arg := f3_cofix) f3_scrut_typed eq_refl.

Lemma typing_mkApps_argE_inst_nondeg : red1 iv_Σ fo_Γ (mkApps f3_idRF [f3_cofix]) f3_cofix.
Proof. exact l45_scrut_red. Qed.

(* INSTANCE IMPOSSIBLE: the proof recurses on the argument list through typing_tApp_invE, which returns sub-derivations of the typing, so in every environment and instance the conclusion is a piece of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_mkApps_headE *)
Definition typing_mkApps_headE_inst :=
  PCUICConsistencyEta.typing_mkApps_headE (Σ := iv_Σ) (Γ := fo_Γ) (f := f3_idRF) (args := [f3_cofix])
    f3_scrut_typed.

Lemma typing_mkApps_headE_inst_nondeg : red1 iv_Σ fo_Γ (mkApps f3_idRF [f3_cofix]) f3_cofix.
Proof. exact l45_scrut_red. Qed.

(* INSTANCE IMPOSSIBLE: the proof follows the stuck_cofix_case derivation through typing_tCase_scrutE, typing_tApp_invE, typing_tProj_argE, typing_mkApps_argE and typing_mkApps_headE to the cofixpoint's typing and returns the ok field of its wf_cofixpointE premise (typing_tCoFix_cofiniteE), so in every instance the conclusion is a field of the instance's own typing premise
   TARGET PCUICConsistencyEta.typing_stuck_cofix_case_cofiniteE *)
Definition typing_stuck_cofix_case_cofiniteE_inst :=
  PCUICConsistencyEta.typing_stuck_cofix_case_cofiniteE (Σ := iv_Σ) (Γ := []) (t := g_t) (T := g_RA)
    g_stuck g_t_typed_RA.

Lemma typing_stuck_cofix_case_cofiniteE_inst_nondeg :
  (stuck_cofix_case g_t × (g_ci.(ci_cofix_nondep) = false))%type.
Proof. exact (g_stuck, eq_refl). Qed.

(** [cs_Σ] has no coinductive block. *)
Lemma l45_cs_no_cofinite :
  forall mind, check_recursivity_kind (lookup_env PCUICConsistencyEtaInstances.cs_Σ) mind CoFinite
    = false.
Proof.
  intros mind. unfold check_recursivity_kind, lookup_env, PCUICConsistencyEtaInstances.cs_Σ,
    PCUICConsistencyEtaInstances.cs_env; cbn.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* INSTANCE IMPOSSIBLE: the conclusion no_closed_stuck_cofix_case_atE is False under a stuck and a typing premise left as hypotheses (as pcuic_consistentE_inst); the proof reads the CoFinite check off that typing (typing_stuck_cofix_case_cofiniteE) and rewrites it with the no-cofinite premise, so no instance can supply a typed stuck term
   TARGET PCUICConsistencyEta.no_closed_stuck_cofix_case_at_no_cofiniteE *)
Definition no_closed_stuck_cofix_case_at_no_cofiniteE_inst :=
  PCUICConsistencyEta.no_closed_stuck_cofix_case_at_no_cofiniteE PCUICConsistencyEtaInstances.cs_Σ
    PCUICConsistencyEtaInstances.cs_ind l45_cs_no_cofinite.

Lemma no_closed_stuck_cofix_case_at_no_cofiniteE_inst_nondeg :
  check_recursivity_kind (lookup_env PCUICConsistencyEtaInstances.cs_Σ)
    PCUICConsistencyEtaInstances.cs_kn BiFinite.
Proof. reflexivity. Qed.

(* INSTANCE IMPOSSIBLE: the target has no parameters (no_closed_stuck_cofix_case_at_no_cofiniteE at Σ_False, the lookup computed), and the instance's conclusion is False under its typing premise left as a hypothesis (as pcuic_consistentE_inst); g_t is not typable in Σ_False
   TARGET PCUICConsistencyEta.no_closed_stuck_cofix_case_at_Σ_FalseE *)
Definition no_closed_stuck_cofix_case_at_Σ_FalseE_inst :
  PCUICConsistency.Σ_False ;;; [] |-E g_t : tInd (mkInd PCUICConsistency.False_kn 0) [] -> False :=
  PCUICConsistencyEta.no_closed_stuck_cofix_case_at_Σ_FalseE g_t g_stuck.

Lemma no_closed_stuck_cofix_case_at_Σ_FalseE_inst_nondeg :
  (stuck_cofix_case g_t × (construct_cofix_discr (head g_t) = false))%type.
Proof. exact (g_stuck, g_head_not_discr). Qed.

(** No term of [si_Σ] (the inductive [I] only) is a typed case blocked on a cofixpoint: a blocked
    case needs a coinductive block. So [wh_neutral_empty_genE] / [wh_neutral_emptyE] have no
    non-degenerate instance in [si_Σ], and [PCUICClassificationEtaInstances] carries none since
    BET-339; their instances are the ones above, in [iv_Σ]. *)
Lemma l6_si_no_stuck Γ t T : stuck_cofix_case t -> si_Σ ;;; Γ |-E t : T -> False.
Proof.
  intros st h. destruct (PCUICConsistencyEta.typing_stuck_cofix_case_cofiniteE st h) as [mind hk].
  revert hk. unfold check_recursivity_kind, lookup_env, si_Σ, si_env; cbn.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; intros e; discriminate e.
Qed.

(** Evidence for the BET-339 lines of [PCUICClassificationEtaInstances] and
    [PCUICProgressEtaInstances] (LAND6): their instances on [c (∀P. P)] land in the
    constructor-head disjunct, since [c (∀P. P)] is no case blocked on a cofixpoint (a blocked term
    has no constructor head); their progress instances on [(λx:Prop. x → x) (∀P. P)] land in the
    step disjunct, since that term evaluates, so it is no [wcbv_stuck] term. *)
Lemma l6_cF_not_stuck : stuck_cofix_case PCUICSREtaInstances.sri_cF -> False.
Proof.
  intros st. pose proof (stuck_cofix_case_head _ st) as e. vm_compute in e. discriminate e.
Qed.

Lemma l6_xx_redex_not_stuck : wcbv_stuck si_Σ PCUICSREtaInstances.sri_xx_redex -> False.
Proof.
  intros st.
  exact (wcbv_stuck_no_eval st _ PCUICClassificationEtaInstances.cli_eval_xx).
Qed.

(* [pcuic_consistentE] in an environment with a coinductive block: not a separate case. The
   theorem concludes [False] in every environment, and its instance
   ([PCUICConsistencyEtaInstances.pcuic_consistentE_inst]) is tagged accordingly; a coinductive
   block would only change how the premise [no_closed_stuck_cofix_case_atE] is discharged (root
   ruling 05:59Z). No such environment is built: none of the lane's instance environments
   declares both base's [False_mib] and a coinductive, and a two-declaration environment needs
   its own [wf] proof, whose second declaration's [on_inductive] obligations are checked in the
   non-empty environment holding the first. *)

(** The pre-BET-339 forms of copy 20's [SN_to_WNE] and [wcbv_normalizationE] (ArityLane's
    statements before the forecast commit) are FALSE in [iv_Σ] under base's normalization premise
    for [iv_Σ]: [g_t] is closed, typed and accessible, and has no value. *)
Lemma wcbv_normalizationE_old_false {nor : normalizing_flags} :
  (forall (Σ : global_env_ext) (nin : PCUICSNEta.NormalizationInE Σ) A t,
     wfE Σ -> axiom_free Σ -> Σ ;;; [] |-E t : A -> { v & eval Σ t v }) ->
  PCUICSNEta.NormalizationInE iv_Σ -> False.
Proof.
  intros h nin. destruct (h iv_Σ nin g_RA g_t iv_wfE g_axiom_free g_t_typed_RA) as [v ev].
  exact (g_no_eval v ev).
Qed.

Lemma SN_to_WNE_old_false {nor : normalizing_flags} :
  (forall (Σ : global_env_ext) (nin : PCUICSNEta.NormalizationInE Σ) A t,
     wfE Σ -> axiom_free Σ -> Acc (cored Σ []) t -> Σ ;;; [] |-E t : A -> { v & eval Σ t v }) ->
  PCUICSNEta.NormalizationInE iv_Σ -> False.
Proof.
  intros h nin.
  have hacc : Acc (cored iv_Σ []) g_t.
  { eapply PCUICSNEta.normalization_inE. econstructor. exact g_t_typed_RA. }
  destruct (h iv_Σ nin g_RA g_t iv_wfE g_axiom_free hacc g_t_typed_RA) as [v ev].
  exact (g_no_eval v ev).
Qed.

(** The pre-BET-339 [ws_wcbv_standardizationE] (no value premise) is FALSE in [iv_Σ] under
    base's normalization premise for [iv_Σ]: [g_t] head-reduces to itself, is irreducible
    ([l45_g_t_normal]), and has no value. *)
Lemma ws_wcbv_standardizationE_old_false {nor : normalizing_flags} :
  (forall (Σ : global_env_ext) (nin : PCUICSNEta.NormalizationInE Σ) T
          (t v : ws_term (fun _ => false)),
     wfE Σ -> axiom_free Σ -> Σ ;;; [] |-E t : T -> closed_red Σ [] t v ->
     ((∑ t', red1 Σ [] v t') -> False) ->
     { v' & eval Σ t v' * closed_red Σ [] v' v }) ->
  PCUICSNEta.NormalizationInE iv_Σ -> False.
Proof.
  intros h nin.
  pose (w := @exist term (on_free_vars (fun _ => false)) g_t l45_g_t_closed : ws_term (fun _ => false)).
  have hred : closed_red iv_Σ [] w w.
  { exact (PCUICEtaA6.closed_red_of (Σ := iv_Σ) (Γ := []) (t := g_t) eq_refl eq_refl
             (Equations.Type.Relation.rt_refl _ _)). }
  have hirr : (∑ t', red1 iv_Σ [] w t') -> False.
  { intros [t' ht']. exact (l45_g_t_normal t' ht'). }
  destruct (h iv_Σ nin g_RA w w iv_wfE g_axiom_free g_t_typed_RA hred hirr) as [v' [ev _]].
  exact (g_no_eval v' ev).
Qed.

(** ** 5. The restated induction principles [typing_ind_envE] and [typing_ind_env_app_sizeE]

  BET-339 restates one premise of each principle: its [tCase] hypothesis receives
  [isCoFinite ==> (ci_cofix_nondep ==> on_free_vars (strengthenP 0 1 xpredT) preturn)]. The
  instances run each principle with predicates that CONSUME that premise:
  - [pgf_P Σ Γ t T]: if [t] is a case on [R] in [iv_Σ] whose return predicate mentions the
    scrutinee, its flag is unset. Only the [tCase] hypothesis has work to do
    ([pgf_case_root]): the inductive is [R] ([CoFinite]) and the predicate is dependent, so the
    restated premise forces the flag to [false]. Every other hypothesis concludes because its
    subject is not a case ([pgf_not_case]), is an application of one ([pgf_app]: the head's own
    hypothesis), or is retyped ([tCumul]).
  - [pgf_Pj Σ Γ j]: [pgf_P] on the judgment's term (if any) and type; [pgf_PΓ Σ Γ]: [pgf_Pj] on
    every declaration of [Γ] (the context hypothesis passes it straight on).
  Each instance is the principle's whole conclusion [env_propE pgf_P pgf_Pj pgf_PΓ], at
  [default_checker_flags]: every term typed under [typingE], in every environment, satisfies
  [pgf_P]. It needs an induction over typing derivations (here only to pass through cumulativity
  steps).
  Non-degeneracy ([pgf_nondeg]): each of the three predicates is false on some input (the case
  [pgf_bad], which is [f3_t0] with its flag SET); on the typed term [f3_t0] of section 1 (the region
  BET-339 admits: the old premise is false there) every premise of [pgf_P] holds, so the
  conclusion at [f3_t0] is the restated premise's own consequence, not a vacuous implication.
  Consequence ([pgf_bad_untypable], from the instance): [pgf_bad] has no type in [fo_Γ]. *)

Definition pgf_P : global_env_ext -> context -> term -> term -> Type :=
  fun Σ _ t _ => forall ci p c brs, t = tCase ci p c brs -> Σ = iv_Σ -> ci.(ci_ind) = iv_ind ->
    on_free_vars (strengthenP 0 1 xpredT) p.(preturn) = false -> ci.(ci_cofix_nondep) = false.

Definition pgf_Pj : global_env_ext -> context -> judgment -> Type :=
  fun Σ Γ j => (option_default (fun tm => pgf_P Σ Γ tm (j_typ j)) (j_term j) unit ×
                pgf_P Σ Γ (j_typ j) (j_typ j))%type.

Definition pgf_PΓ : global_env_ext -> context -> Type :=
  fun Σ Γ => All_local_env (pgf_Pj Σ) Γ.

Lemma pgf_not_case Σ Γ t T :
  (forall ci p c brs, t = tCase ci p c brs -> False) -> pgf_P Σ Γ t T.
Proof. intros h ci p c brs e. exfalso. exact (h ci p c brs e). Qed.

Lemma pgf_app Σ Γ t L T B : pgf_P Σ Γ t T -> pgf_P Σ Γ (mkApps t L) B.
Proof.
  intros pt ci p c brs e. destruct L using rev_case.
  - exact (pt ci p c brs e).
  - rewrite mkApps_app in e. cbn in e. discriminate e.
Qed.

(** The [tCase] hypothesis: the restated premise forces the flag. *)
Lemma pgf_case_root (Σ : global_env_ext) Γ ci p c brs T mdecl idecl :
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  implb (isCoFinite mdecl.(ind_finite))
    (implb ci.(ci_cofix_nondep) (on_free_vars (strengthenP 0 1 xpredT) p.(preturn))) = true ->
  pgf_P Σ Γ (tCase ci p c brs) T.
Proof.
  intros isd hc ci' p' c' brs' e -> eind hfv.
  injection e as <- <- <- <-.
  (* [iv_env] declares [R] only: the membership names [iv_mdecl]. *)
  destruct isd as [hm _]. unfold declared_minductive in hm. cbn in hm.
  destruct hm as [hm|[]]. injection hm; intros; subst.
  rewrite hfv in hc.
  destruct (ci_cofix_nondep ci) eqn:hf; [|reflexivity].
  try rewrite hf in hc. vm_compute in hc. discriminate hc.
Qed.

(** One hypothesis of either principle. The lemmas are arguments, so each instance's own proof
    names the steps it runs ([pgf_case_root] is the one that consumes the restated premise). *)
Ltac pgf_case root app notcase :=
  first
  [ (* the judgment hypothesis *)
    let Htm := fresh "Htm" in let Hty := fresh "Hty" in
    intros ? ? ? j (Htm & ? & (_ & Hty) & _); split;
    [ revert Htm; case: (j_term j) => [tm|] /= Htm; [exact (snd Htm)|exact tt]
    | exact Hty ]
  | (* the context hypothesis *)
    intros; match goal with h : All_local_env (pgf_Pj _) _ |- pgf_PΓ _ _ => exact h end
  | (* the case hypothesis *)
    intros; eapply root; eassumption
  | (* the application hypothesis (both principles) *)
    intros; match goal with
    | pt : pgf_P ?Σ ?Γ ?t _ |- pgf_P ?Σ ?Γ (mkApps ?t ?L) ?B => exact (app Σ Γ t L _ B pt)
    end
  | (* subjects that are not a case *)
    intros; apply notcase; intros ? ? ? ? e; discriminate e
  | (* the cumulativity hypothesis: same subject, another type *)
    intros; match goal with h : pgf_P ?Σ ?Γ ?t _ |- pgf_P ?Σ ?Γ ?t _ => exact h end ].

(* INSTANCE NONDEGEN PCUICEtaF0Land3Instances.pgf_nondeg
   TARGET PCUICProgressEta.typing_ind_envE
   Predicates that consume the restated [tCase] premise; every case proved in general. *)
Lemma typing_ind_envE_inst : env_propE pgf_P pgf_Pj pgf_PΓ.
Proof.
  apply (@typing_ind_envE _ pgf_P pgf_Pj pgf_PΓ); pgf_case pgf_case_root pgf_app pgf_not_case.
Qed.

(* INSTANCE NONDEGEN PCUICEtaF0Land3Instances.pgf_nondeg
   TARGET PCUICProgressEta.typing_ind_env_app_sizeE
   The same predicates; the application hypothesis also receives the sized induction
   hypothesis, which [pgf_app] does not need. *)
Lemma typing_ind_env_app_sizeE_inst : env_propE pgf_P pgf_Pj pgf_PΓ.
Proof.
  apply (@typing_ind_env_app_sizeE _ pgf_P pgf_Pj pgf_PΓ); pgf_case pgf_case_root pgf_app pgf_not_case.
Qed.

(** [f3_t0] with its flag SET: a case on [R] whose predicate [P z] mentions the scrutinee. *)
Definition pgf_ci_set : case_info :=
  {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition pgf_bad : term := tCase pgf_ci_set fo_p f3_scrut [fo_br].

Lemma pgf_fo_p_dep : on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p) = false.
Proof. reflexivity. Qed.

Lemma pgf_bad_false Γ T : pgf_P iv_Σ Γ pgf_bad T -> False.
Proof.
  intros h. specialize (h pgf_ci_set fo_p f3_scrut [fo_br] eq_refl eq_refl eq_refl pgf_fo_p_dep).
  discriminate h.
Qed.

(** Each of the three predicates is false on some input, and on the typed [f3_t0] (old premise
    false, new premise true) every premise of [pgf_P] holds. *)
Lemma pgf_nondeg :
  ((pgf_P iv_Σ fo_Γ pgf_bad f3_T -> False) ×
   (pgf_Pj iv_Σ fo_Γ (j_vass si_na pgf_bad) -> False) ×
   (pgf_PΓ iv_Σ (fo_Γ ,, vass si_na pgf_bad) -> False) ×
   (iv_Σ ;;; fo_Γ |-E f3_t0 : f3_T) ×
   (f3_t0 = tCase fo_ci fo_p f3_scrut [fo_br]) × (fo_ci.(ci_ind) = iv_ind) ×
   (on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p) = false) ×
   ((isCoFinite (ind_finite iv_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p))
      = false))%type.
Proof.
  refine (pgf_bad_false fo_Γ f3_T, (_, (_, (f3_t0_typed, (eq_refl, (eq_refl, (pgf_fo_p_dep, f3_old_premise_fails))))))).
  - intros [_ h]. exact (pgf_bad_false fo_Γ _ h).
  - intros h. unfold pgf_PΓ in h. inversion h; subst.
    match goal with hj : pgf_Pj _ _ _ |- _ => exact (pgf_bad_false fo_Γ _ (snd hj)) end.
Qed.

(** The instance's consequence: BET-339's rule rejects [pgf_bad] (flag set, predicate on the
    scrutinee, inductive [R] coinductive). *)
Lemma pgf_bad_untypable T : iv_Σ ;;; fo_Γ |-E pgf_bad : T -> False.
Proof.
  intros h. exact (pgf_bad_false fo_Γ T (snd (snd (typing_ind_envE_inst iv_Σ iv_wfE fo_Γ pgf_bad T h)))).
Qed.

(** ** Print Assumptions, per instance *)

Print Assumptions f3_sr.
Print Assumptions f3_t1_whne.
Print Assumptions wh_neutral_empty_genE_inst.
Print Assumptions wh_neutral_emptyE_inst.
Print Assumptions g_whnf_classification_stuck.
Print Assumptions whnf_classificationE_stuck_inst.
Print Assumptions progressE_stuck_inst.
Print Assumptions red1_progressE_inst.
Print Assumptions g_no_eval.
Print Assumptions t8_Ind_r_inst.
Print Assumptions pcuic_canonicityE_stuck_inst.
Print Assumptions typing_stuck_cofix_case_cofiniteE_inst.
Print Assumptions no_closed_stuck_cofix_case_at_Σ_FalseE_inst.
Print Assumptions wcbv_normalizationE_old_false.
Print Assumptions SN_to_WNE_old_false.
Print Assumptions ws_wcbv_standardizationE_old_false.
Print Assumptions typing_ind_envE_inst.
Print Assumptions typing_ind_env_app_sizeE_inst.
Print Assumptions pgf_nondeg.
Print Assumptions pgf_bad_untypable.
