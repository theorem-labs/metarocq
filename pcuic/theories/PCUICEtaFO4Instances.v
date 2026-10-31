(* Distributed under the terms of the MIT license. *)

(** * FORECAST-ONLY (FO4): a non-degenerate instance in the region FO4 admits

  FO4 mirrors BET-339's coinductive case side condition into the E copies: the premise of
  [BDTypingEta.inferE_Case] and [case_inversion_dataE]'s [nondep_cofinite] change from
  [isCoFinite ==> on_free_vars (strengthenP 0 1 xpredT) preturn] to
  [isCoFinite ==> (ci_cofix_nondep ==> on_free_vars (strengthenP 0 1 xpredT) preturn)].
  The newly admitted region is: a case on a coinductive with [ci_cofix_nondep = false] whose
  return predicate mentions the scrutinee.

  The instance, in [iv_Σ] of [PCUICInversionEtaInstances]
  ([CoInductive R (A : Prop) : Prop := mkR { f : A }], well formed: [iv_wf]):
  in the context [P : R F -> Prop, h : forall r : R F, P r, x : R F] (with [F := forall P : Prop, P]),
  [match x as z return P z with mkR _ a => h (mkR F a) end], flag [ci_cofix_nondep] unset.
  - [fo_case_typed]: a [typingE] derivation of it;
  - [fo_case_infer]: an [inferingE] derivation of it ([inferE_Case]);
  - [fo_old_premise_fails], [fo_old_bd_premise_fails]: the OLD side condition is false on it, so it
    lies exactly in the region FO4 admits; [fo_new_premise_holds]: the new one holds.
  The return predicate [P z] is not a β-redex: the dependency on the scrutinee is real.

  Forecast-only: in a tree whose [BDTypingEta.inferE_Case] still has the old side condition this file is a forecast; it is reconciled with the forecasts FO1 and FO4 when that premise takes BET-339's form. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICClosedBodies PCUICClosedTyp PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances BDTypingEta.

#[local] Existing Instance default_checker_flags.

(** ** The terms *)

Definition fo_PT : term := tProd si_na iv_RF si_P.                          (* R F -> Prop *)
Definition fo_HT : term := tProd si_na iv_RF (tApp (tRel 1) (tRel 0)).      (* forall r, P r (in [P]) *)
Definition fo_ΓP : context := [vass si_na fo_PT].
Definition fo_ΓH : context := [vass si_na fo_HT; vass si_na fo_PT].
Definition fo_Γ : context := [vass si_na iv_RF; vass si_na fo_HT; vass si_na fo_PT].

Definition fo_ci : case_info :=
  {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := false |}.
Definition fo_p : predicate term :=
  {| pparams := [iv_False]; puinst := []; pcontext := ind_predicate_context iv_ind iv_mdecl iv_idecl;
     preturn := tApp (tRel 3) (tRel 0) |}.
Definition fo_mkRF (a : term) : term := tApp (tApp (tConstruct iv_ind 0 []) iv_False) a.
Definition fo_br : branch term :=
  {| bcontext := cstr_branch_context iv_ind iv_mdecl iv_cdecl; bbody := tApp (tRel 2) (fo_mkRF (tRel 0)) |}.
Definition fo_case : term := tCase fo_ci fo_p (tRel 0) [fo_br].

(** The binder of the predicate context, and the computed contexts and types. *)
Definition fo_zna : aname := mkBindAnn (nNamed "R") Relevant.
Definition fo_ptm : term := tLambda fo_zna iv_RF (tApp (tRel 3) (tRel 0)).
Definition fo_Γz : context := fo_Γ ,, vass fo_zna iv_RF.
Definition fo_Γb : context := fo_Γ ,, vass iv_fna iv_False.
Definition fo_bty : term := tApp (tLambda fo_zna iv_RF (tApp (tRel 4) (tRel 0))) (fo_mkRF (tRel 0)).

Lemma fo_predctx : case_predicate_context iv_ind iv_mdecl iv_idecl fo_p = [vass fo_zna iv_RF].
Proof. reflexivity. Qed.

Lemma fo_brctx :
  case_branch_type iv_ind iv_mdecl iv_idecl fo_p fo_br
    (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl fo_p) (preturn fo_p)) 0 iv_cdecl
  = ([vass iv_fna iv_False], fo_bty).
Proof. reflexivity. Qed.

(** ** The region: the old side condition fails, the new one holds *)

Lemma fo_old_premise_fails :
  (isCoFinite (ind_finite iv_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p)) = false.
Proof. reflexivity. Qed.

Lemma fo_old_bd_premise_fails :
  implb (isCoFinite iv_mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) fo_p.(preturn))
  = false.
Proof. reflexivity. Qed.

Lemma fo_new_premise_holds :
  (isCoFinite (ind_finite iv_mdecl) ==>
   (fo_ci.(ci_cofix_nondep) ==> on_free_vars (strengthenP 0 1 xpredT) (preturn fo_p))) = true.
Proof. reflexivity. Qed.

(** ** The typingE derivation *)

Lemma fo_PT_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E fo_PT : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof.
  intros h. unfold fo_PT. apply typeE_Prod.
  - exact (iv_vass_s iv_Σ Γ si_na iv_RF sProp (iv_RF_typed Γ h) eq_refl).
  - exact (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ Γ si_na iv_RF sProp h (iv_RF_typed Γ h) eq_refl)).
Qed.

Lemma fo_wf_ΓP : wf_localE iv_Σ fo_ΓP.
Proof. exact (iv_wf_vass iv_Σ [] si_na fo_PT _ localenv_nil (fo_PT_typed [] localenv_nil) eq_refl). Qed.

Lemma fo_HT_typed : iv_Σ ;;; fo_ΓP |-E fo_HT : tSort (Sort.sort_of_product sProp sProp).
Proof.
  have hR := iv_RF_typed fo_ΓP fo_wf_ΓP.
  have w := iv_wf_vass iv_Σ fo_ΓP si_na iv_RF sProp fo_wf_ΓP hR eq_refl.
  unfold fo_HT. apply typeE_Prod.
  - exact (iv_vass_s iv_Σ fo_ΓP si_na iv_RF sProp hR eq_refl).
  - refine (typeE_App _ _ (tRel 1) si_na iv_RF si_P _ (tRel 0) (fo_PT_typed _ w) _ _).
    + exact (typeE_Rel _ _ 1 (vass si_na fo_PT) w eq_refl).
    + exact (typeE_Rel _ _ 0 (vass si_na iv_RF) w eq_refl).
Qed.

Lemma fo_wf_ΓH : wf_localE iv_Σ fo_ΓH.
Proof. exact (iv_wf_vass iv_Σ fo_ΓP si_na fo_HT _ fo_wf_ΓP fo_HT_typed eq_refl). Qed.

Lemma fo_wf_Γ : wf_localE iv_Σ fo_Γ.
Proof. exact (iv_wf_vass iv_Σ fo_ΓH si_na iv_RF sProp fo_wf_ΓH (iv_RF_typed fo_ΓH fo_wf_ΓH) eq_refl). Qed.

Lemma fo_wf_Γz : wf_localE iv_Σ fo_Γz.
Proof. exact (iv_wf_vass iv_Σ fo_Γ fo_zna iv_RF sProp fo_wf_Γ (iv_RF_typed fo_Γ fo_wf_Γ) eq_refl). Qed.

Lemma fo_wf_Γb : wf_localE iv_Σ fo_Γb.
Proof.
  exact (iv_wf_vass iv_Σ fo_Γ iv_fna iv_False sProp fo_wf_Γ (iv_False_typed iv_Σ fo_Γ fo_wf_Γ) eq_refl).
Qed.

(** [x : R F]. *)
Lemma fo_x_typed : iv_Σ ;;; fo_Γ |-E tRel 0 : iv_RF.
Proof. exact (typeE_Rel _ _ 0 (vass si_na iv_RF) fo_wf_Γ eq_refl). Qed.

(** [P z : Prop] in [Γ, z : R F]. *)
Lemma fo_pret_typed : iv_Σ ;;; fo_Γz |-E tApp (tRel 3) (tRel 0) : tSort sProp.
Proof.
  refine (typeE_App _ _ (tRel 3) si_na iv_RF si_P _ (tRel 0) (fo_PT_typed _ fo_wf_Γz) _ _).
  - exact (typeE_Rel _ _ 3 (vass si_na fo_PT) fo_wf_Γz eq_refl).
  - exact (typeE_Rel _ _ 0 (vass fo_zna iv_RF) fo_wf_Γz eq_refl).
Qed.

(** [mkR F a : R F] in [Γ, a : F]. *)
Lemma fo_mkRa_typed : iv_Σ ;;; fo_Γb |-E fo_mkRF (tRel 0) : iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ fo_Γb fo_wf_Γb.
  have wF := iv_wf_vass iv_Σ fo_Γb iv_fna iv_False sProp fo_wf_Γb hF eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tRel 0) _ (iv_mkRF_typed fo_Γb fo_wf_Γb) _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ fo_Γb iv_fna iv_False sProp hF eq_refl)|].
    exact (iv_RF_typed _ wF).
  - exact (typeE_Rel _ _ 0 (vass iv_fna iv_False) fo_wf_Γb eq_refl).
Qed.

(** The branch body [h (mkR F a) : P (mkR F a)]. *)
Lemma fo_body_typed : iv_Σ ;;; fo_Γb |-E tApp (tRel 2) (fo_mkRF (tRel 0)) : tApp (tRel 3) (fo_mkRF (tRel 0)).
Proof.
  have hR := iv_RF_typed fo_Γb fo_wf_Γb.
  have w := iv_wf_vass iv_Σ fo_Γb si_na iv_RF sProp fo_wf_Γb hR eq_refl.
  refine (typeE_App _ _ (tRel 2) si_na iv_RF (tApp (tRel 4) (tRel 0)) (Sort.sort_of_product sProp sProp)
            (fo_mkRF (tRel 0)) _ _ fo_mkRa_typed).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ fo_Γb si_na iv_RF sProp hR eq_refl)|].
    refine (typeE_App _ _ (tRel 4) si_na iv_RF si_P _ (tRel 0) (fo_PT_typed _ w) _ _).
    + exact (typeE_Rel _ _ 4 (vass si_na fo_PT) w eq_refl).
    + exact (typeE_Rel _ _ 0 (vass si_na iv_RF) w eq_refl).
  - exact (typeE_Rel _ _ 2 (vass si_na fo_HT) fo_wf_Γb eq_refl).
Qed.

(** The branch type [(fun z : R F => P z) (mkR F a) : Prop]. *)
Lemma fo_bty_typed : iv_Σ ;;; fo_Γb |-E fo_bty : tSort sProp.
Proof.
  have hR := iv_RF_typed fo_Γb fo_wf_Γb.
  have w := iv_wf_vass iv_Σ fo_Γb fo_zna iv_RF sProp fo_wf_Γb hR eq_refl.
  have happ : iv_Σ ;;; fo_Γb ,, vass fo_zna iv_RF |-E tApp (tRel 4) (tRel 0) : si_P.
  { refine (typeE_App _ _ (tRel 4) si_na iv_RF si_P _ (tRel 0) (fo_PT_typed _ w) _ _).
    - exact (typeE_Rel _ _ 4 (vass si_na fo_PT) w eq_refl).
    - exact (typeE_Rel _ _ 0 (vass fo_zna iv_RF) w eq_refl). }
  refine (typeE_App _ _ (tLambda fo_zna iv_RF (tApp (tRel 4) (tRel 0))) fo_zna iv_RF si_P
            (Sort.sort_of_product sProp (Sort.super sProp)) (fo_mkRF (tRel 0)) _ _ fo_mkRa_typed).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ fo_Γb fo_zna iv_RF sProp hR eq_refl)|].
    exact (iv_P_typed iv_Σ _ w).
  - apply typeE_Lambda; [exact (iv_vass iv_Σ fo_Γb fo_zna iv_RF sProp hR eq_refl)|exact happ].
Qed.

(** The body at the branch type, by a β-step. *)
Lemma fo_br_typed : iv_Σ ;;; fo_Γb |-E tApp (tRel 2) (fo_mkRF (tRel 0)) : fo_bty.
Proof.
  refine (typeE_Cumul _ _ _ (tApp (tRel 3) (fo_mkRF (tRel 0))) _ sProp fo_body_typed fo_bty_typed _).
  apply cumulE_Sym. exact (cumulE_beta _ _ Conv fo_zna iv_RF (tApp (tRel 4) (tRel 0)) (fo_mkRF (tRel 0))).
Qed.

Lemma fo_wf_p : wf_predicate iv_mdecl iv_idecl fo_p.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma fo_wf_br : wf_branch iv_cdecl fo_br.
Proof. constructor; [reflexivity|constructor]. Qed.

Lemma fo_ctx_inst : ctx_inst (typingE iv_Σ) fo_Γ [iv_False] [vass si_na si_P].
Proof. econstructor; [|constructor]. exact (iv_False_typed iv_Σ fo_Γ fo_wf_Γ). Qed.

Lemma fo_case_side :
  case_side_conditions (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) iv_Σ fo_Γ fo_ci fo_p sProp
    iv_mdecl iv_idecl [] (case_predicate_context iv_ind iv_mdecl iv_idecl fo_p).
Proof.
  constructor.
  - reflexivity.
  - exact fo_wf_p.
  - reflexivity.
  - exact fo_wf_Γz.
  - exact (alpha_eq_reflexive (pcontext fo_p)).
  - reflexivity.
  - reflexivity.
  - exact fo_ctx_inst.
  - reflexivity.
Qed.

Lemma fo_case_brs :
  case_branch_typing (fun Γ => wf_localE iv_Σ Γ) (typingE iv_Σ) fo_Γ fo_ci fo_p sProp iv_mdecl iv_idecl
    (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl fo_p) (preturn fo_p))
    [fo_br].
Proof.
  constructor.
  - constructor; [exact fo_wf_br|constructor].
  - constructor; [|constructor].
    split; [exact (alpha_eq_reflexive _)|]. cbv zeta. split; [|split].
    + exact fo_wf_Γb.
    + exact fo_br_typed.
    + exact fo_bty_typed.
Qed.

Definition fo_case_ty : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context iv_ind iv_mdecl iv_idecl fo_p) (preturn fo_p))
    ([] ++ [tRel 0]).

Lemma fo_case_typed : iv_Σ ;;; fo_Γ |-E fo_case : fo_case_ty.
Proof.
  eapply (typeE_Case _ _ fo_ci fo_p (tRel 0) [fo_br] [] sProp iv_mdecl iv_idecl).
  - exact iv_declared_inductive.
  - exact fo_pret_typed.
  - exact fo_x_typed.
  - exact fo_case_side.
  - exact fo_case_brs.
Qed.

(** The case's type is [(fun z : R F => P z) x]. *)
Lemma fo_case_ty_eq : fo_case_ty = tApp fo_ptm (tRel 0).
Proof. reflexivity. Qed.

(** ** The inferingE derivation ([inferE_Case]) *)

Lemma fo_J_refl Γ pb t : JoinE iv_Σ Γ pb t t.
Proof. apply JoinE_refl. Qed.

(** [Prop ▹□ Type1], [F ▹ Prop] (computed: [sort_of_product Type1 Prop = Prop]), [F ◃ Prop]. *)
Lemma fo_P_sort (Γ : context) : iv_Σ ;;; Γ |-E si_P ▹□ Sort.super sProp.
Proof. econstructor; [exact (inferE_Sort _ _ sProp I)|apply refl_red]. Qed.

Lemma fo_F_infer (Γ : context) : iv_Σ ;;; Γ |-E iv_False ▹ tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  unfold iv_False. apply inferE_Prod.
  - split; [exact tt|]. exists (Sort.super sProp). split; [exact (fo_P_sort Γ)|]. split; [reflexivity|reflexivity].
  - econstructor; [exact (inferE_Rel _ (Γ ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl)|apply refl_red].
Qed.

Lemma fo_F_check (Γ : context) : iv_Σ ;;; Γ |-E iv_False ◃ si_P.
Proof. econstructor; [exact (fo_F_infer Γ)|apply fo_J_refl]. Qed.

Lemma fo_F_sort (Γ : context) : iv_Σ ;;; Γ |-E iv_False ▹□ sProp.
Proof. econstructor; [exact (fo_F_infer Γ)|apply refl_red]. Qed.

(** [R F ▹ Prop] and [R F ▹□ Prop]. *)
Lemma fo_RF_infer (Γ : context) : iv_Σ ;;; Γ |-E iv_RF ▹ si_P.
Proof.
  refine (inferE_App _ _ (tInd iv_ind []) si_na si_P (tSort sProp) iv_False _ (fo_F_check Γ)).
  econstructor; [exact (inferE_Ind _ _ iv_ind [] iv_mdecl iv_idecl iv_declared_inductive eq_refl)|apply refl_red].
Qed.

Lemma fo_RF_sort (Γ : context) : iv_Σ ;;; Γ |-E iv_RF ▹□ sProp.
Proof. econstructor; [exact (fo_RF_infer Γ)|apply refl_red]. Qed.

Lemma fo_pret_sort : iv_Σ ;;; fo_Γz |-E tApp (tRel 3) (tRel 0) ▹□ sProp.
Proof.
  econstructor; [|apply refl_red].
  refine (inferE_App _ _ (tRel 3) si_na iv_RF si_P (tRel 0) _ _).
  - econstructor; [exact (inferE_Rel _ fo_Γz 3 (vass si_na fo_PT) eq_refl)|apply refl_red].
  - econstructor; [exact (inferE_Rel _ fo_Γz 0 (vass fo_zna iv_RF) eq_refl)|apply fo_J_refl].
Qed.

Lemma fo_mkRa_infer : iv_Σ ;;; fo_Γb |-E fo_mkRF (tRel 0) ▹ iv_RF.
Proof.
  refine (inferE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF (tRel 0) _ _).
  - econstructor; [|apply refl_red].
    refine (inferE_App _ _ (tConstruct iv_ind 0 []) si_na si_P (tProd iv_fna (tRel 0) (iv_R (tRel 1)))
              iv_False _ (fo_F_check _)).
    econstructor; [|apply refl_red].
    exact (inferE_Construct _ _ iv_ind 0 [] iv_mdecl iv_idecl iv_cdecl iv_declared_constructor eq_refl).
  - econstructor; [exact (inferE_Rel _ fo_Γb 0 (vass iv_fna iv_False) eq_refl)|apply fo_J_refl].
Qed.

Lemma fo_body_check : iv_Σ ;;; fo_Γb |-E tApp (tRel 2) (fo_mkRF (tRel 0)) ◃ fo_bty.
Proof.
  econstructor.
  - refine (inferE_App _ _ (tRel 2) si_na iv_RF (tApp (tRel 4) (tRel 0)) (fo_mkRF (tRel 0)) _ _).
    + econstructor; [exact (inferE_Rel _ fo_Γb 2 (vass si_na fo_HT) eq_refl)|apply refl_red].
    + econstructor; [exact fo_mkRa_infer|apply fo_J_refl].
  - apply JoinE_red_r. apply red1_red.
    exact (red_beta _ _ fo_zna iv_RF (tApp (tRel 4) (tRel 0)) (fo_mkRF (tRel 0))).
Qed.

Lemma fo_case_infer : iv_Σ ;;; fo_Γ |-E fo_case ▹ tApp fo_ptm (tRel 0).
Proof.
  refine (inferE_Case _ _ fo_ci fo_p (tRel 0) [fo_br] [iv_False] [] sProp iv_mdecl iv_idecl
            _ iv_declared_inductive _ eq_refl _ fo_wf_p eq_refl _ _ eq_refl _ eq_refl _ _ _ _).
  - econstructor; [exact (inferE_Rel _ fo_Γ 0 (vass si_na iv_RF) eq_refl)|apply refl_red].
  - exact fo_pret_sort.
  - exact (alpha_eq_reflexive _).
  - change (All_local_rel (lift_sorting1 (checkingE iv_Σ) (infering_sortE iv_Σ)) fo_Γ [vass fo_zna iv_RF]).
    constructor; [constructor|].
    split; [exact tt|]. exists sProp. split; [exact (fo_RF_sort _)|]. split; [exact I|reflexivity].
  - reflexivity.
  - econstructor; [|constructor]. exact (fo_F_check _).
  - cbn. constructor.
  - constructor; [apply fo_J_refl|constructor].
  - constructor; [exact fo_wf_br|constructor].
  - constructor; [|constructor].
    split; [exact (alpha_eq_reflexive _)|]. cbv zeta. split.
    + change (All_local_rel (lift_sorting1 (checkingE iv_Σ) (infering_sortE iv_Σ)) fo_Γ [vass iv_fna iv_False]).
      constructor; [constructor|].
      split; [exact tt|]. exists sProp. split; [exact (fo_F_sort _)|]. split; [exact I|reflexivity].
    + exact fo_body_check.
Qed.

(** ** Print Assumptions, per lemma *)

Print Assumptions fo_case_typed.
Print Assumptions fo_case_infer.
Print Assumptions fo_old_premise_fails.
Print Assumptions fo_old_bd_premise_fails.
Print Assumptions fo_new_premise_holds.
