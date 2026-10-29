(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDToPCUICEta] (row T6)

  **The forecast classes are section variables.** Every lemma of [BDToPCUICEta] that uses a
  forecast fact takes the forecast classes as premises: T2a's [ValForecastCopy15/16]
  ([PCUICValidityEta]), T1's [SRForecastCopy15/16/18] ([PCUICSREta]) and [BDForecastCopy18]
  ([BDToPCUICEta]); copies 10, 12 and 14 have landed and their classes are gone. No instance of
  a class exists before its copy lands, so the instances below live in section
  [BDToPCUICEtaInstances], whose [Context] holds the six classes, and APPLY the lemmas there.
  Everything else each instance needs (the environment, its [wfE], every typing and
  bidirectional derivation) is proved here, in [PCUICInversionEtaInstances] or in
  [BDTypingEtaInstances], with no class.

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]):
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]. The local contexts are those of
  [BDTypingEtaInstances]: [bd_ΓFG = [F : Prop → Prop; G : (Prop → Prop) → Prop]] and
  [bd_Γη = x : G (λ y : Prop. F y) :: bd_ΓFG]. Their [wf_localE] is built here over
  [typingE], without the lemmas under test ([bdi_wfFG], [bdi_wfη]).

  **Non-degeneracy.** Each instance applies a lemma to a derivation that is not empty and not
  reflexive where the lemma's content is a comparison:
  - [checking_typingE_eta_inst]: the check [x ◃ G F] of [checkingE_eta_inst], whose [JoinE]
    premise is one η step ([λ y. F y ⇝η F] under [G]); soundness turns it into a [typeE_Cumul]
    whose [cumulSpecE] premise comes from that η join by [into_ws_cumul_pbE] and
    [ws_cumul_pbE_forget_spec] (I5).
  - [infering_typingE_Case_inst]: the [match] of [inferingE_Case_inst], whose parameter
    comparison [All2 (JoinE si_Σ bd_ΓFG Conv) [G (λ y. F y)] [G F]] is an η step between
    syntactically different terms ([bd_case_pars_differ]). Soundness goes through its Case
    branch: the joins become [ws_cumul_pbE] ([into_ws_cumul_pbE]), [ws_cumul_pbE_Ind] relates
    the scrutinee's type to the match's, the forecast [ctx_inst_app_weakE] extends the
    parameters with the indices, and [typeE_Case] gets the scrutinee by a [typeE_Cumul].
  - the inferred sort, product and inductive ([bd_X_sort], [bd_G_prod], [bd_case_disc_ind]) are
    applications or variables of a non-empty context; [lift_sorting_lift_typingE_inst] and
    [isTypebd_isTypeE_inst] carry a let-judgment whose term [G F] is checked;
    [ctx_inst_bd_typingE_inst] and [ctx_inst_implE_inst] instantiate the parameter of [I] with
    [G F]; the context lemmas run on contexts with a let ([bd_wf_localE_inst],
    [bd_wf_local_relE_inst]), with three declarations ([wf_local_bd_typingE_inst]), or across a
    real weakening ([wf_rel_weakE_inst]); [wf_local_rel_subst1E_inst] substitutes the let-bound
    variable that the declaration above it mentions.

  **Assumptions.** The end of this file prints the assumptions of base's main theorems and of
  their E copies: the same set, and the forecast classes are arguments ([About]), not axioms. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICValidityEta PCUICSREta
     BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta.
From MetaRocq.PCUIC Require BDToPCUIC.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Pieces in [si_Σ], without any class *)

(** [G : (Prop → Prop) → Prop] and [F : Prop → Prop]: [bd_GP] is [iv_K], [bd_FP] is [iv_PP]. *)
Lemma bdi_wfGP : wf_localE si_Σ [vass si_na bd_GP].
Proof. exact (iv_wf_vass si_Σ [] si_na bd_GP _ localenv_nil (iv_K_typed [] localenv_nil) eq_refl). Qed.

Lemma bdi_wfFG : wf_localE si_Σ bd_ΓFG.
Proof. exact (iv_wf_vass si_Σ [vass si_na bd_GP] si_na bd_FP _ bdi_wfGP (iv_PP_typed si_Σ _ bdi_wfGP) eq_refl). Qed.

(** [G F : Prop] in [bd_ΓFG]. *)
Lemma bdi_GF_typed : si_Σ ;;; bd_ΓFG |-E bd_GF : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na bd_FP si_P _ (tRel 0) (iv_K_typed bd_ΓFG bdi_wfFG)
           (typeE_Rel _ _ 1 (vass si_na bd_GP) bdi_wfFG eq_refl)
           (typeE_Rel _ _ 0 (vass si_na bd_FP) bdi_wfFG eq_refl)).
Qed.

(** [λ y : Prop. F y : Prop → Prop] and [G (λ y : Prop. F y) : Prop] in [bd_ΓFG]. *)
Lemma bdi_Fy_typed : si_Σ ;;; bd_ΓFG ,, vass si_na si_P |-E tApp (tRel 1) (tRel 0) : si_P.
Proof.
  have w := iv_wf_P si_Σ bd_ΓFG bdi_wfFG.
  exact (typeE_App _ _ (tRel 1) si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w)
           (typeE_Rel _ _ 1 (vass si_na bd_FP) w eq_refl) (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma bdi_lam_typed : si_Σ ;;; bd_ΓFG |-E bd_lam : bd_FP.
Proof.
  exact (typeE_Lambda _ _ si_na si_P (tApp (tRel 1) (tRel 0)) si_P
           (iv_vass si_Σ bd_ΓFG si_na si_P _ (iv_P_typed si_Σ bd_ΓFG bdi_wfFG) eq_refl) bdi_Fy_typed).
Qed.

Lemma bdi_X_typed : si_Σ ;;; bd_ΓFG |-E bd_X : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na bd_FP si_P _ bd_lam (iv_K_typed bd_ΓFG bdi_wfFG)
           (typeE_Rel _ _ 1 (vass si_na bd_GP) bdi_wfFG eq_refl) bdi_lam_typed).
Qed.

Lemma bdi_wfη : wf_localE si_Σ bd_Γη.
Proof. exact (iv_wf_vass si_Σ bd_ΓFG si_na bd_X sProp bdi_wfFG bdi_X_typed eq_refl). Qed.

(** [G F : Prop] in [bd_Γη], so [G F] is a type there. *)
Lemma bdi_GF_eta_typed : si_Σ ;;; bd_Γη |-E tApp (tRel 2) (tRel 1) : si_P.
Proof.
  exact (typeE_App _ _ (tRel 2) si_na bd_FP si_P _ (tRel 1) (iv_K_typed bd_Γη bdi_wfη)
           (typeE_Rel _ _ 2 (vass si_na bd_GP) bdi_wfη eq_refl)
           (typeE_Rel _ _ 1 (vass si_na bd_FP) bdi_wfη eq_refl)).
Qed.

Lemma bdi_GF_eta_isType : isTypeE si_Σ bd_Γη (tApp (tRel 2) (tRel 1)).
Proof. exact (has_sort_isTypeE sProp bdi_GF_eta_typed). Qed.

(** The let-judgment [G F : Prop] in [bd_ΓFG], bidirectionally: [G F ◃ Prop], [Prop ▹□ Type]. *)
Lemma bdi_vdef_bd :
  lift_sorting (checkingE si_Σ bd_ΓFG) (infering_sortE si_Σ bd_ΓFG) (j_vdef si_na bd_GF si_P).
Proof.
  split; [exact bd_GF_check|]. exists (Sort.super sProp).
  split; [exact (bd_P_sort _)|]. split; [exact I|reflexivity].
Qed.

(** A context with a let: [A : Prop, x := A : Prop], bidirectionally, with transparent
    judgments so that [All_local_env_over_sorting] can read their sorts. *)
Definition bdi_Γd : context := [vdef si_na (tRel 0) si_P; vass si_na si_P].

Definition bdi_tu_A : lift_sorting1 (checkingE si_Σ) (infering_sortE si_Σ) [] (j_vass si_na si_P).
Proof.
  split; [exact tt|]. exists (Sort.super sProp).
  split; [exact (bd_P_sort [])|]. split; [exact I|reflexivity].
Defined.

Definition bdi_tu_x : lift_sorting1 (checkingE si_Σ) (infering_sortE si_Σ) bd_Γ1 (j_vdef si_na (tRel 0) si_P).
Proof.
  split; [exact (bd_rel0_check [])|]. exists (Sort.super sProp).
  split; [exact (bd_P_sort _)|]. split; [exact I|reflexivity].
Defined.

Definition bdi_wfbd_Γd : wf_local_bdE si_Σ bdi_Γd :=
  localenv_cons_def (localenv_cons_abs localenv_nil bdi_tu_A) bdi_tu_x.

Definition bdi_over_Γd :
  All_local_env_over_sorting (checkingE si_Σ) (infering_sortE si_Σ)
    (fun Γ _ t T _ => wf_localE si_Σ Γ -> isTypeE si_Σ Γ T -> si_Σ ;;; Γ |-E t : T)
    (fun Γ _ t s _ => wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E t : tSort s)
    bdi_Γd bdi_wfbd_Γd.
Proof.
  unfold bdi_wfbd_Γd, bdi_Γd. constructor.
  - constructor; [constructor|]. intros _. exact (bd_P_typedE [] localenv_nil).
  - intros wf _. exact (typeE_Rel _ _ 0 (vass si_na si_P) wf eq_refl).
  - intros wf. exact (bd_P_typedE _ wf).
Defined.

(** The same let, as an extension of [bd_Γ1 = [A : Prop]]. *)
Definition bdi_tu_rel :
  lift_sorting1 (fun Δ => checkingE si_Σ (bd_Γ1 ,,, Δ)) (fun Δ => infering_sortE si_Σ (bd_Γ1 ,,, Δ))
    [] (j_vdef si_na (tRel 0) si_P).
Proof.
  split; [exact (bd_rel0_check [])|]. exists (Sort.super sProp).
  split; [exact (bd_P_sort _)|]. split; [exact I|reflexivity].
Defined.

(* Built at the predicate [All_local_env_over_sorting] reads, so that its constructor unifies. *)
Definition bdi_wfbd_rel : wf_local_bd_relE si_Σ bd_Γ1 [vdef si_na (tRel 0) si_P] :=
  @localenv_cons_def
    (lift_sorting1 (fun Δ => checkingE si_Σ (bd_Γ1 ,,, Δ)) (fun Δ => infering_sortE si_Σ (bd_Γ1 ,,, Δ)))
    _ _ _ _ localenv_nil bdi_tu_rel.

Definition bdi_over_rel :
  All_local_env_over_sorting
    (fun Δ => checkingE si_Σ (bd_Γ1 ,,, Δ)) (fun Δ => infering_sortE si_Σ (bd_Γ1 ,,, Δ))
    (fun Δ _ t T _ => wf_localE si_Σ (bd_Γ1 ,,, Δ) -> isTypeE si_Σ (bd_Γ1 ,,, Δ) T ->
                      si_Σ ;;; bd_Γ1 ,,, Δ |-E t : T)
    (fun Δ _ t s _ => wf_localE si_Σ (bd_Γ1 ,,, Δ) -> si_Σ ;;; bd_Γ1 ,,, Δ |-E t : tSort s)
    [vdef si_na (tRel 0) si_P] bdi_wfbd_rel.
Proof.
  unfold bdi_wfbd_rel. constructor.
  - constructor.
  - intros wf _. exact (typeE_Rel _ _ 0 (vass si_na si_P) wf eq_refl).
  - intros wf. exact (bd_P_typedE _ wf).
Defined.

(** [x : z] in [z := ∀P:Prop. P : Prop]: the declaration mentions the let-bound variable. *)
Lemma bdi_wf_subst1_prem : wf_localE si_Σ [vass si_na (tRel 0); vdef si_na iv_False si_P].
Proof.
  have w := iv_wf_vdef si_Σ [] localenv_nil.
  exact (iv_wf_vass si_Σ [vdef si_na iv_False si_P] si_na (tRel 0) sProp w
           (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) w eq_refl) eq_refl).
Qed.

Section BDToPCUICEtaInstances.

(* FORECAST-ONLY: the six classes of [BDToPCUICEta]; delete each when its copy lands. *)
Context {V15 : ValForecastCopy15} {V16 : ValForecastCopy16}
  {F15 : SRForecastCopy15} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18} {B18 : BDForecastCopy18}.

(** ** The prelude lemmas *)

(** [x : z, z := ∀P:Prop. P] ⇒ [x : ∀P:Prop. P]. *)
Lemma wf_local_rel_subst1E_inst : wf_local_relE si_Σ [] [vass si_na iv_False].
Proof.
  exact (wf_local_rel_subst1E (Σ := si_Σ) (wfΣ := si_wfE) [] [] si_na iv_False si_P [vass si_na (tRel 0)]
           (wf_local_local_relE si_Σ [] ([] ,,, [] ,, vdef si_na iv_False si_P ,,, [vass si_na (tRel 0)])
              bdi_wf_subst1_prem)).
Qed.

Lemma wf_rel_weakE_inst : wf_local_relE si_Σ bd_ΓFG [vass si_na si_P].
Proof. exact (wf_rel_weakE si_Σ si_wfE bd_ΓFG bdi_wfFG [vass si_na si_P] (iv_wf_P si_Σ [] localenv_nil)). Qed.

Lemma wf_local_local_relE_inst : wf_local_relE si_Σ bd_ΓFG [vass si_na bd_X].
Proof. exact (wf_local_local_relE si_Σ bd_ΓFG [vass si_na bd_X] bdi_wfη). Qed.

(** ** The section lemmas *)

Lemma bd_wf_localE_inst : wf_localE si_Σ bdi_Γd.
Proof. exact (bd_wf_localE si_Σ bdi_Γd bdi_wfbd_Γd bdi_over_Γd). Qed.

Lemma bd_wf_local_relE_inst : wf_local_relE si_Σ bd_Γ1 [vdef si_na (tRel 0) si_P].
Proof. exact (bd_wf_local_relE si_Σ bd_Γ1 bd_wfE_Γ1 _ bdi_wfbd_rel bdi_over_rel). Qed.

(** The parameter of [I] instantiated with [G F]. *)
Lemma ctx_inst_implE_inst : ctx_instE si_Σ bd_ΓFG [bd_GF] [vass si_na si_P].
Proof.
  refine (ctx_inst_implE si_Σ si_wfE bd_ΓFG bdi_wfFG [vass si_na si_P] _ [bd_GF] _).
  - exact (wf_rel_weakE si_Σ si_wfE bd_ΓFG bdi_wfFG [vass si_na si_P] (iv_wf_P si_Σ [] localenv_nil)).
  - econstructor; [|constructor]. intros _ _. exact bdi_GF_typed.
Qed.

(** The judgment component of the main theorem, on the let-judgment [G F : Prop]. *)
Lemma bidirectional_to_pcuicE_inst : lift_typing typingE si_Σ bd_ΓFG (j_vdef si_na bd_GF si_P).
Proof. exact (fst (bidirectional_to_pcuicE si_Σ si_wfE) bd_ΓFG _ bdi_vdef_bd bdi_wfFG). Qed.

(** ** The user-facing theorems *)

(** The [match] whose parameter comparison is an η step. *)
Lemma infering_typingE_Case_inst : si_Σ ;;; bd_ΓFG |-E bd_case : tApp bd_case_ptm bd_case_disc.
Proof. exact (infering_typingE si_Σ bd_ΓFG bd_case _ si_wfE bdi_wfFG inferingE_Case_inst). Qed.

(** The check by an η step: [x : G (λ y. F y) ⊢ x : G F]. *)
Lemma checking_typingE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 : tApp (tRel 2) (tRel 1).
Proof.
  exact (checking_typingE si_Σ bd_Γη (tRel 0) (tApp (tRel 2) (tRel 1)) si_wfE bdi_wfη
           bdi_GF_eta_isType checkingE_eta_inst).
Qed.

(** [G (λ y. F y) ▹□ Prop]. *)
Lemma infering_sort_typingE_inst : si_Σ ;;; bd_ΓFG |-E bd_X : tSort sProp.
Proof. exact (infering_sort_typingE si_Σ bd_ΓFG bd_X sProp si_wfE bdi_wfFG bd_X_sort). Qed.

Lemma infering_sort_isTypeE_inst : isTypeE si_Σ bd_ΓFG bd_X.
Proof. exact (infering_sort_isTypeE si_Σ bd_ΓFG bd_X sProp si_wfE bdi_wfFG bd_X_sort). Qed.

(** [relevance_of_sort sProp] is [Relevant]. *)
Lemma infering_sort_isTypeRelE_inst : isTypeRelE si_Σ bd_ΓFG bd_X Relevant.
Proof. exact (infering_sort_isTypeRelE si_Σ bd_ΓFG bd_X sProp si_wfE bdi_wfFG bd_X_sort). Qed.

Lemma einfering_sort_isTypeE_inst : isTypeE si_Σ bd_ΓFG bd_X.
Proof. exact (einfering_sort_isTypeE si_Σ bd_ΓFG bd_X si_wfE bdi_wfFG (existT _ sProp bd_X_sort)). Qed.

Lemma isTypebd_isTypeE_inst : isTypeE si_Σ bd_ΓFG si_P.
Proof. exact (isTypebd_isTypeE si_Σ bd_ΓFG (j_vdef si_na bd_GF si_P) si_wfE bdi_wfFG bdi_vdef_bd). Qed.

Lemma lift_sorting_lift_typingE_inst : lift_typing typingE si_Σ bd_ΓFG (j_vdef si_na bd_GF si_P).
Proof. exact (lift_sorting_lift_typingE si_Σ bd_ΓFG _ si_wfE bdi_wfFG bdi_vdef_bd). Qed.

(** [G ▹Π (_ : Prop → Prop, Prop)]. *)
Lemma infering_prod_typingE_inst : si_Σ ;;; bd_ΓFG |-E tRel 1 : tProd si_na bd_FP si_P.
Proof. exact (infering_prod_typingE si_Σ bd_ΓFG (tRel 1) si_na bd_FP si_P si_wfE bdi_wfFG bd_G_prod). Qed.

(** [c (G (λ y. F y)) ▹{I} ([], [G (λ y. F y)])]. *)
Lemma infering_ind_typingE_inst : si_Σ ;;; bd_ΓFG |-E bd_case_disc : mkApps (tInd si_ind []) [bd_X].
Proof.
  exact (infering_ind_typingE si_Σ bd_ΓFG bd_case_disc si_ind [] [bd_X] si_wfE bdi_wfFG bd_case_disc_ind).
Qed.

Lemma wf_local_bd_typingE_inst : wf_localE si_Σ bd_Γη.
Proof. exact (wf_local_bd_typingE si_Σ bd_Γη si_wfE wf_local_bdE_eta_inst). Qed.

Lemma wf_local_bd_rel_typingE_inst :
  wf_local_relE si_Σ [vass si_na bd_GP] [vass si_na bd_X; vass si_na bd_FP].
Proof. exact (wf_local_bd_rel_typingE si_Σ _ _ si_wfE bdi_wfGP wf_local_bd_relE_inst). Qed.

Lemma ctx_inst_bd_typingE_inst :
  PCUICTyping.ctx_inst (typingE si_Σ) bd_ΓFG [bd_GF] (List.rev [vass si_na si_P]).
Proof.
  exact (ctx_inst_bd_typingE si_Σ bd_ΓFG [bd_GF] [vass si_na si_P] si_wfE
           (iv_wf_P si_Σ bd_ΓFG bdi_wfFG) bd_case_ctx_inst).
Qed.

End BDToPCUICEtaInstances.

(** ** Assumptions: base's main theorems, then their E copies *)

Print Assumptions BDToPCUIC.bidirectional_to_pcuic.
Print Assumptions bidirectional_to_pcuicE.
Print Assumptions BDToPCUIC.checking_typing.
Print Assumptions checking_typingE.
Print Assumptions BDToPCUIC.infering_typing.
Print Assumptions infering_typingE.
Print Assumptions BDToPCUIC.ctx_inst_bd_typing.
Print Assumptions ctx_inst_bd_typingE.
Print Assumptions T6BD_checking_typing_fit.
Print Assumptions infering_typingE_Case_inst.
Print Assumptions checking_typingE_eta_inst.
About checking_typingE.
About bidirectional_to_pcuicE.
