(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDToPCUICEta] (row T6)

  **No forecast class.** The lemmas of [BDToPCUICEta] that used a forecast fact took T1's
  [SRForecastCopy18] ([PCUICSREta], copy 18b) as a premise until copy 18b landed (frac/eta
  3e6b422d); the class is deleted (copies 10, 12, 14, 15, 16 and 18a landed earlier). The
  instances below, in section [BDToPCUICEtaInstances] (which held the class), apply the lemmas.
  Everything each instance needs (the environment, its [wfE], every typing and bidirectional
  derivation) is proved here, in [PCUICInversionEtaInstances] or in [BDTypingEtaInstances].

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]):
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]. The local contexts are those of
  [BDTypingEtaInstances]: [bd_ΓFG = [F : Prop → Prop; G : (Prop → Prop) → Prop]],
  [bd_Γη = x : G (λ y : Prop. F y) :: bd_ΓFG], and the contexts of its judgments by a real
  step, [bd_Γδ], [bd_Γβ] and [bd_Γβπ]. Their [wf_localE] is built here over [typingE], without
  the lemmas under test ([bdi_wfFG], [bdi_wfη], [bdi_wf_Γδ], [bdi_wf_Γβ], [bdi_wf_Γβπ]).

  **Non-degeneracy.** Each instance applies its lemma to concrete derivations. The comment above
  each instance carries its tag of the instance degeneracy gate, with the lemma that states its
  non-degeneracy; the declarations that are not instances are registered on the witness line
  after the imports.
  - [checking_typingE_eta_inst]: soundness on the check [x ◃ G F] of [checkingE_eta_inst].
    Every type inferred for [x] in [bd_Γη] is [G (λ y. F y)], which is not [G F] and
    η-contracts to it in one step ([bdi_eta_pair]).
  - [infering_typingE_Case_inst]: soundness on the [match] of [inferingE_Case_inst]. Its
    parameter [G F] is joined with [G (λ y. F y)] ([bd_case_pars_join]); [G F] is the one-step
    η-contraction of [G (λ y. F y)], and the two are not equal ([bdi_case_pars_eta]).
  - the [▹□], [▹Π] and [▹{}] instances run on the derivations of [BDTypingEtaInstances] in
    [bd_Γδ], [bd_Γβπ] and [bd_Γβ]. In each context, every type inferred for the variable is not
    the form the judgment reaches, and it reduces to that form in one step: [d], the
    let-variable of [d := Prop], reduces to [Prop] ([infering_sort_typingE_inst],
    [infering_sort_isTypeE_inst], [infering_sort_isTypeRelE_inst],
    [einfering_sort_isTypeE_inst], [isTypebd_isTypeE_inst]; [bdi_Γδ_delta]); the types with the
    β-redex [(λ B : Prop. I B) A] reduce to [Π _ : I A. Prop] and to [I A]
    ([infering_prod_typingE_inst], [infering_ind_typingE_inst]; [bdi_Γβπ_beta],
    [bdi_Γβ_beta]). Their contexts are typed here ([bdi_wf_Γδ], [bdi_wf_Γβπ], [bdi_wf_Γβ]).
  - [lift_sorting_lift_typingE_inst] and [bidirectional_to_pcuicE_inst] carry a let-judgment
    [G F : Prop] that has a term ([bdi_vdef_term]); [ctx_inst_bd_typingE_inst] and
    [ctx_inst_implE_inst] instantiate the parameter of [I] with the list [[G F]], which is not
    empty ([bdi_args_nonempty]); the context lemmas run on contexts that are not empty
    ([bdi_ctxs_nonempty], [bd_ctxs_nonempty]): with a let ([bd_wf_localE_inst],
    [bd_wf_local_relE_inst]), with three declarations ([wf_local_bd_typingE_inst]), or across a
    real weakening ([wf_rel_weakE_inst]); [wf_local_rel_subst1E_inst] substitutes [∀P:Prop. P]
    for the let-bound [z] in [x : z → z], where [z] is not the whole type; the result
    [(∀P:Prop. P) → ∀P:Prop. P] is not the substituted term ([wf_local_rel_subst1E_inst_nondeg]).

  **Assumptions.** The end of this file prints the assumptions of base's main theorems and of
  their E copies: the same set, and no forecast class is an argument ([About]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta.
From MetaRocq.PCUIC Require BDToPCUIC PCUICWfUniversesEta.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** The declarations that are not instances: the contexts, derivations and non-degeneracy
    facts the instances are built from or name.
    WITNESSES: bdi_* *)

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

(** [z → z] over [z := ∀P:Prop. P : Prop]: the let-bound [z] occurs in the domain and under the
    binder. *)
Definition bdi_z_to_z : term := tProd si_na (tRel 0) (tRel 1).

(** [x : z → z] in [z := ∀P:Prop. P : Prop]. *)
Lemma bdi_wf_z_to_z : wf_localE si_Σ [vass si_na bdi_z_to_z; vdef si_na iv_False si_P].
Proof.
  have w := iv_wf_vdef si_Σ [] localenv_nil.
  have hz : si_Σ ;;; [vdef si_na iv_False si_P] |-E tRel 0 : tSort sProp :=
    typeE_Rel _ _ 0 (vdef si_na iv_False si_P) w eq_refl.
  have w2 := iv_wf_vass si_Σ [vdef si_na iv_False si_P] si_na (tRel 0) sProp w hz eq_refl.
  have hz2 : si_Σ ;;; [vass si_na (tRel 0); vdef si_na iv_False si_P] |-E tRel 1 : tSort sProp :=
    typeE_Rel _ _ 1 (vdef si_na iv_False si_P) w2 eq_refl.
  exact (iv_wf_vass si_Σ [vdef si_na iv_False si_P] si_na bdi_z_to_z (Sort.sort_of_product sProp sProp) w
           (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
              (iv_vass_s si_Σ _ si_na (tRel 0) sProp hz eq_refl) hz2) eq_refl).
Qed.

(** [y : d, d := Prop : Type] ([bd_Γδ]), [x : (λ B : Prop. I B) A, A : Prop] ([bd_Γβ]) and
    [x : Π _ : (λ B : Prop. I B) A. Prop, A : Prop] ([bd_Γβπ]) are well formed. *)
Lemma bdi_wf_Γδ : wf_localE si_Σ bd_Γδ.
Proof.
  pose proof (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)) as ws.
  pose proof (@typeE_Sort default_checker_flags si_Σ [] (Sort.super sProp) localenv_nil ws) as hT.
  assert (w1 : wf_localE si_Σ [vdef si_na si_P (tSort (Sort.super sProp))]).
  { apply localenv_cons_def; [constructor|].
    exact (iv_vdef si_Σ [] si_na si_P _ _ (iv_P_typed si_Σ [] localenv_nil) hT eq_refl). }
  exact (iv_wf_vass si_Σ _ si_na (tRel 0) (Sort.super sProp) w1
           (typeE_Rel _ _ 0 (vdef si_na si_P (tSort (Sort.super sProp))) w1 eq_refl) eq_refl).
Qed.

Lemma bdi_wf_Γβ : wf_localE si_Σ bd_Γβ.
Proof.
  unfold bd_Γβ. apply localenv_cons_abs; [exact bd_wfE_Γ1|].
  split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; [exact I|reflexivity].
Qed.

Lemma bdi_wf_Γβπ : wf_localE si_Σ bd_Γβπ.
Proof.
  have hdom : lift_typing typingE si_Σ bd_Γ1 (j_vass si_na bd_fix_dom).
  { split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; [exact I|reflexivity]. }
  unfold bd_Γβπ. apply localenv_cons_abs; [exact bd_wfE_Γ1|].
  split; [exact tt|]. exists (Sort.sort_of_product sProp (Sort.super sProp)).
  split; [|split; [exact I|reflexivity]].
  apply typeE_Prod.
  - split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; reflexivity.
  - apply typeE_Sort; [|cbn; trivial].
    exact (localenv_cons_abs bd_wfE_Γ1 hdom).
Qed.

(** The substituted type [z → z] is not a bare variable; substituting [∀P:Prop. P] for [z] gives
    [x : (∀P:Prop. P) → ∀P:Prop. P], whose type is not the substituted term [∀P:Prop. P] and is
    not [z → z]. *)
Lemma wf_local_rel_subst1E_inst_nondeg :
  [/\ (forall k, bdi_z_to_z <> tRel k),
      subst_context [iv_False] 0 [vass si_na bdi_z_to_z] = [vass si_na (tProd si_na iv_False iv_False)],
      tProd si_na iv_False iv_False <> iv_False &
      tProd si_na iv_False iv_False <> bdi_z_to_z].
Proof. split; [intros k; discriminate|reflexivity|discriminate|discriminate]. Qed.

(** The contexts of the let instances are not empty. *)
Lemma bdi_ctxs_nonempty : bdi_Γd <> [] /\ [vdef si_na (tRel 0) si_P] <> [].
Proof. unfold bdi_Γd. split; discriminate. Qed.

(** The parameter list that instantiates the telescope [[A : Prop]] of [I] is not empty. *)
Lemma bdi_args_nonempty : [bd_GF] <> [].
Proof. discriminate. Qed.

(** The let-judgment [G F : Prop] has a term: its [j_term] is not [None]. *)
Lemma bdi_vdef_term : j_term (j_vdef si_na bd_GF si_P : judgment_ sort term) <> None.
Proof. discriminate. Qed.

(** [x]'s declaration in [bd_Γη] is [x : G (λ y. F y)]; every type inferred for [x] there is
    that type lifted over [x]; that type is not [G F], and it η-contracts to [G F] in one
    step. *)
Lemma bdi_eta_pair :
  [/\ nth_error bd_Γη 0 = Some (vass si_na bd_X),
      (forall T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' -> T' = lift0 1 bd_X),
      lift0 1 bd_X <> tApp (tRel 2) (tRel 1) &
      ∥ eta1 (lift0 1 bd_X) (tApp (tRel 2) (tRel 1)) ∥].
Proof.
  split; [reflexivity| |unfold bd_X, bd_lam; discriminate|exact (sq bd_eta_step)].
  intros T' h. inversion h; subst.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  reflexivity.
Qed.

(** [G (λ y. F y)] η-contracts in one step to [G F], the parameter of [bd_case], and the two
    are not equal. *)
Lemma bdi_case_pars_eta : ∥ eta1 bd_X bd_GF ∥ /\ bd_X <> bd_GF.
Proof. split; [exact (sq bd_case_eta_step)|unfold bd_X, bd_GF, bd_lam; discriminate]. Qed.

(** In [bd_Γδ = [y : d; d := Prop : Type]]: the declared type of [y], lifted, is not a sort;
    every type inferred for [y] is [d] ([tRel 1]); and [d], the let-variable of [d := Prop],
    reduces to [Prop] in one step. *)
Lemma bdi_Γδ_delta :
  [/\ (forall d u, nth_error bd_Γδ 0 = Some d -> lift0 1 (decl_type d) <> tSort u),
      (forall T', si_Σ ;;; bd_Γδ |-E tRel 0 ▹ T' -> T' = tRel 1) &
      ∥ red1 si_Σ bd_Γδ (tRel 1) si_P ∥].
Proof.
  split.
  - intros d u h. injection h as <-. discriminate.
  - intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity.
  - exact (sq (red_rel si_Σ bd_Γδ 1 si_P eq_refl)).
Qed.

(** In [bd_Γβπ = [x : Π _ : (λ B : Prop. I B) A. Prop; A : Prop]]: the declared type of [x],
    lifted, is not [Π _ : I A. Prop]; every type inferred for [x] is that declared type,
    lifted; and it reduces to [Π _ : I A. Prop] in one step (its domain
    [(λ B : Prop. I B) A] becomes [I A]). *)
Lemma bdi_Γβπ_beta :
  [/\ (forall d, nth_error bd_Γβπ 0 = Some d ->
        lift0 1 (decl_type d) <> tProd si_na (tApp (tInd si_ind []) (tRel 1)) si_P),
      (forall T', si_Σ ;;; bd_Γβπ |-E tRel 0 ▹ T' -> T' = lift0 1 bd_fix_dtype) &
      ∥ red1 si_Σ bd_Γβπ (lift0 1 bd_fix_dtype) (tProd si_na (tApp (tInd si_ind []) (tRel 1)) si_P) ∥].
Proof.
  split.
  - intros d h. injection h as <-. discriminate.
  - intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity.
  - constructor.
    change (red1 si_Σ bd_Γβπ
              (tProd si_na (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 1)) si_P)
              (tProd si_na ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 1}) si_P)).
    apply prod_red_l. apply red_beta.
Qed.

(** In [bd_Γβ = [x : (λ B : Prop. I B) A; A : Prop]]: the declared type of [x], lifted, is not
    [I A]; every type inferred for [x] is that declared type, lifted; and it reduces to [I A] in
    one step. *)
Lemma bdi_Γβ_beta :
  [/\ (forall d, nth_error bd_Γβ 0 = Some d -> lift0 1 (decl_type d) <> tApp (tInd si_ind []) (tRel 1)),
      (forall T', si_Σ ;;; bd_Γβ |-E tRel 0 ▹ T' -> T' = lift0 1 bd_fix_dom) &
      ∥ red1 si_Σ bd_Γβ (lift0 1 bd_fix_dom) (tApp (tInd si_ind []) (tRel 1)) ∥].
Proof.
  split.
  - intros d h. injection h as <-. discriminate.
  - intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity.
  - constructor.
    change (red1 si_Σ bd_Γβ (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 1))
              ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 1})).
    apply red_beta.
Qed.

Section BDToPCUICEtaInstances.

(** ** The prelude lemmas *)

(** [x : z → z, z := ∀P:Prop. P] ⇒ [x : (∀P:Prop. P) → ∀P:Prop. P]
    ([wf_local_rel_subst1E_inst_nondeg]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.wf_local_rel_subst1E_inst_nondeg *)
Lemma wf_local_rel_subst1E_inst : wf_local_relE si_Σ [] [vass si_na (tProd si_na iv_False iv_False)].
Proof.
  exact (wf_local_rel_subst1E (Σ := si_Σ) (wfΣ := si_wfE) [] [] si_na iv_False si_P [vass si_na bdi_z_to_z]
           (wf_local_local_relE si_Σ [] ([] ,,, [] ,, vdef si_na iv_False si_P ,,, [vass si_na bdi_z_to_z])
              bdi_wf_z_to_z)).
Qed.

(** A weakening from [[]] to [bd_ΓFG], which is not empty.
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty *)
Lemma wf_rel_weakE_inst : wf_local_relE si_Σ bd_ΓFG [vass si_na si_P].
Proof. exact (wf_rel_weakE si_Σ si_wfE bd_ΓFG bdi_wfFG [vass si_na si_P] (iv_wf_P si_Σ [] localenv_nil)). Qed.

(** [bd_Γη = bd_ΓFG ,,, [x : G (λ y. F y)]], both parts not empty.
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty *)
Lemma wf_local_local_relE_inst : wf_local_relE si_Σ bd_ΓFG [vass si_na bd_X].
Proof. exact (wf_local_local_relE si_Σ bd_ΓFG [vass si_na bd_X] bdi_wfη). Qed.

(** ** The section lemmas *)

(** The context [x := A : Prop, A : Prop], with a let.
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_ctxs_nonempty *)
Lemma bd_wf_localE_inst : wf_localE si_Σ bdi_Γd.
Proof. exact (bd_wf_localE si_Σ bdi_Γd bdi_wfbd_Γd bdi_over_Γd). Qed.

(** The extension [[x := A : Prop]] of [bd_Γ1], a let.
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_ctxs_nonempty *)
Lemma bd_wf_local_relE_inst : wf_local_relE si_Σ bd_Γ1 [vdef si_na (tRel 0) si_P].
Proof.
  exact (bd_wf_local_relE si_Σ bd_Γ1 bd_wfE_Γ1 [vdef si_na (tRel 0) si_P] bdi_wfbd_rel bdi_over_rel).
Qed.

(** The parameter of [I] instantiated with [G F] ([bdi_args_nonempty]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_args_nonempty *)
Lemma ctx_inst_implE_inst : ctx_instE si_Σ bd_ΓFG [bd_GF] [vass si_na si_P].
Proof.
  refine (ctx_inst_implE si_Σ si_wfE bd_ΓFG bdi_wfFG [vass si_na si_P] _ [bd_GF] _).
  - exact (wf_rel_weakE si_Σ si_wfE bd_ΓFG bdi_wfFG [vass si_na si_P] (iv_wf_P si_Σ [] localenv_nil)).
  - econstructor; [|constructor]. intros _ _. exact bdi_GF_typed.
Qed.

(** The judgment component of the main theorem, on the let-judgment [G F : Prop], which has a
    term ([bdi_vdef_term]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_vdef_term *)
Lemma bidirectional_to_pcuicE_inst : lift_typing typingE si_Σ bd_ΓFG (j_vdef si_na bd_GF si_P).
Proof.
  exact (fst (bidirectional_to_pcuicE si_Σ si_wfE) bd_ΓFG (j_vdef si_na bd_GF si_P) bdi_vdef_bd bdi_wfFG).
Qed.

(** ** The user-facing theorems *)

(** The [match] [bd_case] of [inferingE_Case_inst]: its parameter [G F] is the one-step
    η-contraction of [G (λ y. F y)], and the two are not equal ([bdi_case_pars_eta]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_case_pars_eta
    TARGET BDToPCUICEta.infering_typingE
    HELPER BDTypingEtaInstances.inferingE_Case_inst *)
Lemma infering_typingE_Case_inst : si_Σ ;;; bd_ΓFG |-E bd_case : tApp bd_case_ptm bd_case_disc.
Proof. exact (infering_typingE si_Σ bd_ΓFG bd_case _ si_wfE bdi_wfFG inferingE_Case_inst). Qed.

(** The check [x ◃ G F] in [bd_Γη] ([checkingE_eta_inst]): every type inferred for [x] there is
    [G (λ y. F y)], which is not [G F] and η-contracts to it in one step ([bdi_eta_pair]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_eta_pair
    TARGET BDToPCUICEta.checking_typingE *)
Lemma checking_typingE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 : tApp (tRel 2) (tRel 1).
Proof.
  exact (checking_typingE si_Σ bd_Γη (tRel 0) (tApp (tRel 2) (tRel 1)) si_wfE bdi_wfη
           bdi_GF_eta_isType checkingE_eta_inst).
Qed.

(** [y ▹□ Prop] in [bd_Γδ]: every type inferred for [y] is [d], which is not a sort and reduces
    to [Prop] in one step ([bdi_Γδ_delta]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γδ_delta *)
Lemma infering_sort_typingE_inst : si_Σ ;;; bd_Γδ |-E tRel 0 : tSort sProp.
Proof. exact (infering_sort_typingE si_Σ bd_Γδ (tRel 0) sProp si_wfE bdi_wf_Γδ infering_sortE_inst). Qed.

(** INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γδ_delta *)
Lemma infering_sort_isTypeE_inst : isTypeE si_Σ bd_Γδ (tRel 0).
Proof. exact (infering_sort_isTypeE si_Σ bd_Γδ (tRel 0) sProp si_wfE bdi_wf_Γδ infering_sortE_inst). Qed.

(** [relevance_of_sort sProp] is [Relevant].
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γδ_delta *)
Lemma infering_sort_isTypeRelE_inst : isTypeRelE si_Σ bd_Γδ (tRel 0) Relevant.
Proof. exact (infering_sort_isTypeRelE si_Σ bd_Γδ (tRel 0) sProp si_wfE bdi_wf_Γδ infering_sortE_inst). Qed.

(** INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γδ_delta *)
Lemma einfering_sort_isTypeE_inst : isTypeE si_Σ bd_Γδ (tRel 0).
Proof.
  exact (einfering_sort_isTypeE si_Σ bd_Γδ (tRel 0) si_wfE bdi_wf_Γδ (existT _ sProp infering_sortE_inst)).
Qed.

(** The assumption judgment [_ : y] in [bd_Γδ], sorted by [y ▹□ Prop]: every type inferred for
    [y] is [d], which is not a sort and reduces to [Prop] in one step ([bdi_Γδ_delta]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γδ_delta *)
Lemma isTypebd_isTypeE_inst : isTypeE si_Σ bd_Γδ (tRel 0).
Proof.
  exact (isTypebd_isTypeE si_Σ bd_Γδ (j_vass si_na (tRel 0)) si_wfE bdi_wf_Γδ
           (bd_vass bd_Γδ si_na (tRel 0) sProp infering_sortE_inst eq_refl)).
Qed.

(** The let-judgment [G F : Prop], which has a term ([bdi_vdef_term]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_vdef_term *)
Lemma lift_sorting_lift_typingE_inst : lift_typing typingE si_Σ bd_ΓFG (j_vdef si_na bd_GF si_P).
Proof. exact (lift_sorting_lift_typingE si_Σ bd_ΓFG (j_vdef si_na bd_GF si_P) si_wfE bdi_wfFG bdi_vdef_bd). Qed.

(** [x ▹Π (_ : I A, Prop)] in [bd_Γβπ]: every type inferred for [x] is
    [Π _ : (λ B : Prop. I B) A. Prop], which is not that product and reduces to it in one step
    ([bdi_Γβπ_beta]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γβπ_beta *)
Lemma infering_prod_typingE_inst :
  si_Σ ;;; bd_Γβπ |-E tRel 0 : tProd si_na (tApp (tInd si_ind []) (tRel 1)) si_P.
Proof.
  exact (infering_prod_typingE si_Σ bd_Γβπ (tRel 0) si_na (tApp (tInd si_ind []) (tRel 1)) si_P si_wfE
           bdi_wf_Γβπ infering_prodE_inst).
Qed.

(** [x ▹{I} ([], [A])] in [bd_Γβ]: every type inferred for [x] is [(λ B : Prop. I B) A], which is
    not [I A] and reduces to it in one step ([bdi_Γβ_beta]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_Γβ_beta *)
Lemma infering_ind_typingE_inst : si_Σ ;;; bd_Γβ |-E tRel 0 : mkApps (tInd si_ind []) [tRel 1].
Proof.
  exact (infering_ind_typingE si_Σ bd_Γβ (tRel 0) si_ind [] [tRel 1] si_wfE bdi_wf_Γβ infering_induE_inst).
Qed.

(** The three declarations of [bd_Γη].
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty *)
Lemma wf_local_bd_typingE_inst : wf_localE si_Σ bd_Γη.
Proof. exact (wf_local_bd_typingE si_Σ bd_Γη si_wfE wf_local_bdE_eta_inst). Qed.

(** [[x : G (λ y. F y); F : Prop → Prop]] over [[G : (Prop → Prop) → Prop]].
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty *)
Lemma wf_local_bd_rel_typingE_inst :
  wf_local_relE si_Σ [vass si_na bd_GP] [vass si_na bd_X; vass si_na bd_FP].
Proof.
  exact (wf_local_bd_rel_typingE si_Σ [vass si_na bd_GP] [vass si_na bd_X; vass si_na bd_FP] si_wfE
           bdi_wfGP wf_local_bd_relE_inst).
Qed.

(** The parameter of [I] instantiated with [G F] ([bdi_args_nonempty]).
    INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_args_nonempty *)
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
