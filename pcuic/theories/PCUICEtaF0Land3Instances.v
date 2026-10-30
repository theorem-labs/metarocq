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
       [stuck_cofix_case t] and [g_t] is a non-degenerate instance.
     - [whnf_classification'E], [whnf_classificationE]: instances at [g_t]; the head of [g_t]
       is neither a constructor nor a cofixpoint ([g_head_not_discr]), so they land in the
       disjunct BET-339 added ([g_whnf_classification_stuck]).
     - [progressE] at [g_t]: [g_t] is [wcbv_stuck] ([g_wcbv_stuck]).
     - [red1_progressE] (new copy of base [red1_progress]): instance at [g_t].

  3. The T8 probe on a type-level case of the region ([PCUICEtaT8Probe.T8_Ind_r]).
     In [iv_Γr := x : R F], [t8_T := match mkR F x.(f) as z return t8_inner z with
     mkR _ b => R F end], flag unset, where [t8_inner z := match z return Type with
     mkR _ _ => Prop end] (flag set). The return predicate mentions the scrutinee (as the
     scrutinee of the inner case, stuck on a variable [z]); at [mkR F x.(f)] it computes to
     [Prop], so [t8_T : Prop] ([t8_T_sort]). [t8_T] reaches [R F] only by ι
     ([t8_T_conv]). [t8_Ind_r_inst] applies the proved [T8_Ind_r] to it.
     Non-degeneracy: [t8_old_premise_fails], [t8_flag_unset]; [t8_T] is a case, not a head form.

  Forecast evidence for the cutover F0 (it rests on the ship branch's
  [PCUICEtaFO4Instances], which is itself forecast-only). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICReduction PCUICViews PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICClosedBodies PCUICClosedTyp PCUICClosedTypEta PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICGuardClosure PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICEtaFO4Instances
     PCUICNormal PCUICWcbvEval PCUICClassification PCUICClassificationEta PCUICProgressEta
     PCUICSREta PCUICEtaT8Probe.
From MetaRocq.PCUIC Require PCUICWfUniverses.

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

(** The landed T1 theorem on the step. *)
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

(** [wh_neutral_empty_genE] and [wh_neutral_emptyE]: IMPOSSIBLE before BET-339 (they concluded
    [False]); now non-degenerate. *)
Definition wh_neutral_empty_genE_inst : stuck_cofix_case g_t :=
  wh_neutral_empty_genE (Σ := iv_Σ) (wfΣ := iv_wfE) [] [] g_t g_RA g_afv g_whne g_t_typed_RA eq_refl.

Definition wh_neutral_emptyE_inst : stuck_cofix_case g_t :=
  wh_neutral_emptyE (Σ := iv_Σ) (wfΣ := iv_wfE) g_t g_RA g_afv g_whne g_t_typed_RA.

Definition whnf_classification'E_stuck_inst :=
  whnf_classification'E (Σ := iv_Σ) (wfΣ := iv_wfE) g_t iv_ind [] [g_A] g_afv g_whnf g_t_typed_RA.

Definition whnf_classificationE_stuck_inst :=
  whnf_classificationE (Σ := iv_Σ) (wfΣ := iv_wfE) g_t iv_ind [] [g_A] g_axiom_free g_whnf g_t_typed_RA.

(** The instance lands in the disjunct BET-339 added. *)
Lemma g_whnf_classification_stuck : stuck_cofix_case g_t.
Proof.
  destruct whnf_classification'E_stuck_inst as [h|s]; [|exact s].
  exfalso. rewrite g_head_not_discr in h. discriminate h.
Qed.

Definition progressE_stuck_inst :=
  progressE iv_Σ g_t g_RA g_axiom_free iv_wfE g_t_typed_RA.

Definition red1_progressE_inst :=
  red1_progressE (Σ := iv_Σ) (wfΣ := iv_wfE) g_axiom_free g_t g_RA g_t_typed_RA.

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

(** The proved T8 theorem on [t8_T]. *)
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
