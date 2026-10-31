(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate, a FLOOR (a ruling made after 2026-10-31T09:00Z can only raise it): at least 24 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (40.0%, 95% upper bound 51.4%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus seven further rows that both reviews had passed and root rulings made between 2026-10-31T01:29Z and 05:41Z reclassified under the same standard (S12, S13, S19, S31, S36, S51, S57), which raised the count from at least 17 to at least 24. 22 of the 24 are false NONDEGEN tags (22 of the 52 sampled NONDEGEN instances, 42.3%); 2 are false prose under a correct tag. All 24 are corrected at frac/eta 6978492e, but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta 6978492e: 313 lemmas with a base twin are accounted for: 208 have at least one NONDEGEN instance, 83 are undemonstrable by their own statements (IMPOSSIBLE-only), and 22 have no working instance (NOT-BUILT-only): BDStrengtheningEta.on_free_vars_typeE; BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.eval_whneE, fix_app_is_constructorE, invert_cumul_arity_lE, invert_cumul_arity_l_genE, invert_cumul_arity_rE, invert_cumul_arity_r_genE, isArity_typing_spineE, typing_cofix_coindE, value_whnfE, wf_cofixpoint_spineE, wf_fixpoint_spineE; PCUICInversionEta.into_ws_cumulE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. No NONDEGEN tag at frac/eta 6978492e is judged false by a root ruling made by 2026-10-31T09:00Z. The 208 is a CEILING, not a count of sound demonstrations: every root ruling made between 2026-10-31T01:29Z and 07:30Z that re-examined NONDEGEN tags in place found more false ones (the next, at 08:29Z, judged its one row weak, not false); retags from those rulings moved 25 targets out between frac/eta c825ec02 (229) and 6978492e, and rebuilt instances moved 4 in. The miss rate above (a floor) and this ceiling measure the same thing two ways. Combined at frac/eta 6978492e (the sample's false-tag rate, 22 of 52, applied to every NONDEGEN instance outside the sample, including the 36 that root rulings judged sound; the instances of one file counted as one cluster), they give an expected 131 of the 208 with at least one sound instance, 90% interval 89 to 170; about 77 of the 208 are expected to have none. Corrections pull in both directions (90% intervals with the rate fixed): counting the 36 root-judged instances as sound gives 147 (137 to 156); the 38 false instances found in the sampled frame outside the sample, between the sample's head 39ff4f31 and frac/eta 6978492e, lower the rate that remains, giving 143 (133 to 154); and sampled rows judged sound are not certain (S12, S13, S19, S31, S36, S51 and S57 were each passed by both reviews and judged false), which gives 127 (115 to 138). Context of the 208 (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 84 use a non-empty context (in 2 of them, typing_eq_termE and typing_leq_termE, it occurs but does no work); 23 have the context as their subject; 19 have a non-empty context that no term or type mentions; 4 undecided; 58 work only at the empty context (7 forced by the statement, 51 by the instance's choice; up to 77 under stricter readings); 20 have no context argument, which is not the same as the empty context. A mechanical detector run over all 413 instances at frac/eta 2e26fc93 (does an input sub-derivation inhabit the conclusion, at any depth and through squash, existential and pair packages; does the conclusion close by computation alone) finds 30 of the 56 blocks (53 instances) that root rulings had judged false, 11 of the 22 such tags in the sample; it finds none of the reflexive-step, identity-only or translation cases and 7 of 16 round trips (it cannot see a round trip inside the target lemma's own proof), and on closed equations it flags every row, sound or not; root rulings made by 2026-10-31T08:29Z judged its 20 flags on unruled NONDEGEN tags (8 false). A first mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the tag changes of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9), LAND11-A (6568a017), LAND12 (07786120, e2c9c6b2), LAND13-A (af1fa399), LAND10 (fc8627b8), GAMMA9 (1f0c66a6, 201d23cc) and LAND13-C (46b62a8a to 8c0b7bcd), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); all 31 were judged by 2026-10-31T08:29Z: its 9 non-equation flags 9 bad, with the kind-label correct in 6 of 9; its 22 closed-equation flags, which it cannot discriminate, 10 bad, 4 weak only, 8 not degenerate. Prose overclaims were not mechanically enumerated, because that detector failed its controls. The 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

(** * Satisfying instances of the lemmas of [PCUICInversionEta], and the checker's contract

  **The contract.** Five fields that the class [T6_facts] of the checker's
  [safechecker/theories/PCUICTypingEtaHyps.v] held, the ones that are rows of [PCUICInversion],
  are copied here verbatim, under the checker's notation
  [Σ ;;; Γ ⊢E t ≤ u] ([ws_cumul_pbE Cumul Σ Γ t u]), and each is inhabited by its E lemma:
  [T6_inversion_Const_fit], [T6_inversion_LetIn_fit], [T6_inversion_Prod_fit],
  [T6_inversion_Rel_fit], [T6_inversion_Sort_fit].

  **The instances.** Each lemma of [PCUICInversionEta] that has a premise is applied here to a
  concrete typing derivation in a well-formed environment, every premise proved.
  [inversion_VarE] and [inversion_EvarE] conclude [False]: their instances apply them with the
  typing premise, which no derivation satisfies, left as a hypothesis (tagged IMPOSSIBLE). The
  environments:
  - [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]): [Inductive I (A : Prop) : Prop := c : I A],
    with [si_wfE];
  - [Σ_po] ([PCUICEtaPrimOpInstance]): [int : Set], [land : int -> int -> int] and the primitive
    integers registered on [int]; [iv_po_wf_ext] re-proves its [wf_ext] unsquashed (the file has
    only [∥ wf_ext Σ_po ∥]), [iv_po_wfE] its [wfE];
  - [iv_Σ], declared here: [CoInductive R (A : Prop) : Prop := mkR { f : A }], a coinductive record
    with one projection, well formed ([iv_wf]) and so well formed for the η typing ([iv_wfE]).

  Each inversion instance runs on a derivation built here. For [inversion_RelE], in the context
  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g], the variable [y] is typed at
  [k (λx:Prop. g x)] ([iv_rel_typed]); the declared type of [y], lifted, is [k g], which is not
  [k (λx:Prop. g x)] ([iv_y_decl_kg]), so the lemma's conclusion relates two different types.
  [into_ws_cumulE] is applied to the same pair ([iv_kg_keta_differ]), but its instance is tagged
  NOT-BUILT: its JoinE premise [iv_join_eta] is projected from the [ws_cumul_pbE] it rebuilds.
  The instances of
  [inversion_SortE], [inversion_IndE], [inversion_ConstructE], [inversion_ConstE] and
  [inversion_PrimE] type their closed term at a type that reaches its canonical type only through
  a let of the context: [U := Type₁ : Type₂ ⊢ Prop : U], [Z := Prop : Type₁ ⊢ I : Z → Prop],
  [J := I : Prop → Prop ⊢ c : Π A : Prop. J A], [N := int : Set ⊢ land : N → int → int] and
  [N := int : Set ⊢ 1 : N]; each derivation ends in [typeE_Cumul] with the δ-step of the
  let-bound variable ([cumulE_rel]), and each NONDEGEN lemma states the let and that the type is
  not the canonical one. The instances of [inversion_AppE] and [inversion_App_sizeE] run on
  [c (z → z)] in [z := ∀P:Prop. P : Prop], typed at [I ((∀P:Prop. P) → z)]: the argument uses
  [z], the codomain [I A] moves to [I (z → z)], and the type is one δ-step of [z] away from it
  ([iv_czz_IFz_nondeg]). Every other inversion instance types its term [t] at [(λX : s. X) T],
  from [T : s] and [t : T] ([iv_retype]); its NONDEGEN lemma states that [(λX : s. X) T] is not
  [T] (for the fixpoint and the cofixpoint, also that [T] is the declared type). The derivation
  of the [match] of [inversion_CaseE] follows [cp_match_typed] of
  [PCUICTypingEtaCopies1Instances]. Each instance carries its tag (instance-gate grammar).

  WITNESSES: iv_* T6_* iv_ctx_inst iv_kg_keta_differ
  ([iv_*]: the typing pieces, environments and derivations the instances use; [T6_*]: the
  checker contract fits above, generic in [Σ], not instances; [iv_ctx_inst]: a [ctx_inst]
  derivation of the [match], not an instance) *)

From MetaRocq.PCUIC Require PCUICWfUniversesEta.

From Stdlib Require Import ssreflect ssrbool PrimInt63.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICArityRed PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICGuardClosure
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaPrimOpInstance PCUICInversionEta.

Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.

(** ** The checker's [T6_facts] fields, verbatim, inhabited by the E lemmas *)

Section ContractFit.

  Context {cf : checker_flags}.

  Definition T6_inversion_Const_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {c : kername} {u : Instance.t} {T : term}, Σ;;; Γ |-E tConst c u : T -> ∑ decl : constant_body, wf_localE Σ Γ × declared_constant Σ c decl × consistent_instance_ext Σ (cst_universes decl) u × Σ ;;; Γ ⊢E (cst_type decl)@[u] ≤ T
    := @inversion_ConstE cf.

  Definition T6_inversion_LetIn_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {b : term} {B : term} {t : term} {T : term}, Σ;;; Γ |-E tLetIn na b B t : T -> ∑ A : term, lift_typing typingE Σ Γ (j_vdef na b B) × Σ;;; Γ,, vdef na b B |-E t : A × Σ ;;; Γ ⊢E tLetIn na b B A ≤ T
    := @inversion_LetInE cf.

  Definition T6_inversion_Prod_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {A : term} {B : term} {T : term}, Σ;;; Γ |-E tProd na A B : T -> ∑ s1 s2 : sort, lift_typing typingE Σ Γ (j_vass_s na A s1) × Σ;;; Γ,, vass na A |-E B : tSort s2 × Σ ;;; Γ ⊢E tSort (Sort.sort_of_product s1 s2) ≤ T
    := @inversion_ProdE cf.

  Definition T6_inversion_Rel_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {n : nat} {T : term}, Σ;;; Γ |-E tRel n : T -> ∑ decl : context_decl, wf_localE Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢E lift0 (S n) (decl_type decl) ≤ T
    := @inversion_RelE cf.

  Definition T6_inversion_Sort_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {s : sort} {T : term}, Σ;;; Γ |-E tSort s : T -> wf_localE Σ Γ × wf_sort Σ s × Σ ;;; Γ ⊢E tSort (Sort.super s) ≤ T
    := @inversion_SortE cf.

End ContractFit.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Typing pieces, in any environment *)

(** [Prop → Prop], [∀P:Prop. P] and [λx:Prop. x]. *)
Definition iv_PP : term := tProd si_na si_P si_P.
Definition iv_sPP : sort := Sort.sort_of_product (Sort.super sProp) (Sort.super sProp).
Definition iv_False : term := tProd si_na si_P (tRel 0).
Definition iv_id : term := tLambda si_na si_P (tRel 0).

Section Generic.

  Context (Σ : global_env_ext).

  Lemma iv_P_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
  Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

  Lemma iv_vass (Γ : context) (na : aname) A s :
    Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) -> lift_typing typingE Σ Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma iv_vass_s (Γ : context) (na : aname) A s :
    Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typingE Σ Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma iv_vdef (Γ : context) (na : aname) b A s :
    Σ ;;; Γ |-E b : A -> Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typingE Σ Γ (j_vdef na b A).
  Proof. intros hb h r. split; [exact hb|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma iv_wf_vass (Γ : context) (na : aname) A s :
    wf_localE Σ Γ -> Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
    wf_localE Σ (Γ ,, vass na A).
  Proof. intros h hA r. apply localenv_cons_abs; [exact h|exact (iv_vass Γ na A s hA r)]. Qed.

  Lemma iv_wf_P (Γ : context) : wf_localE Σ Γ -> wf_localE Σ (Γ ,, vass si_na si_P).
  Proof. intros h. exact (iv_wf_vass Γ si_na si_P _ h (iv_P_typed Γ h) eq_refl). Qed.

  Lemma iv_PP_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E iv_PP : tSort iv_sPP.
  Proof.
    intros h. unfold iv_PP, iv_sPP. apply typeE_Prod.
    - exact (iv_vass_s Γ si_na si_P _ (iv_P_typed Γ h) eq_refl).
    - exact (iv_P_typed _ (iv_wf_P Γ h)).
  Qed.

  Lemma iv_False_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E iv_False : si_P.
  Proof.
    intros h. unfold iv_False.
    exact (typeE_Prod _ _ si_na si_P (tRel 0) (Sort.super sProp) sProp
             (iv_vass_s Γ si_na si_P _ (iv_P_typed Γ h) eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P Γ h) eq_refl)).
  Qed.

  Lemma iv_id_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E iv_id : iv_PP.
  Proof.
    intros h. unfold iv_id, iv_PP. apply typeE_Lambda.
    - exact (iv_vass Γ si_na si_P _ (iv_P_typed Γ h) eq_refl).
    - exact (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P Γ h) eq_refl).
  Qed.

  (** [(λx:Prop. x) (∀P:Prop. P) : Prop]. *)
  Lemma iv_app_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E tApp iv_id iv_False : si_P.
  Proof.
    intros h.
    exact (typeE_App _ _ iv_id si_na si_P si_P _ iv_False (iv_PP_typed Γ h) (iv_id_typed Γ h)
             (iv_False_typed Γ h)).
  Qed.

  (** [let z : Prop := ∀P:Prop. P in ...]. *)
  Lemma iv_vdef_False (Γ : context) : wf_localE Σ Γ -> lift_typing typingE Σ Γ (j_vdef si_na iv_False si_P).
  Proof. intros h. exact (iv_vdef Γ si_na iv_False si_P _ (iv_False_typed Γ h) (iv_P_typed Γ h) eq_refl). Qed.

  Lemma iv_wf_vdef (Γ : context) : wf_localE Σ Γ -> wf_localE Σ (Γ ,, vdef si_na iv_False si_P).
  Proof. intros h. apply localenv_cons_def; [exact h|exact (iv_vdef_False Γ h)]. Qed.

  (** [let z : Prop := ∀P:Prop. P in z]. *)
  Lemma iv_let_typed (Γ : context) : wf_localE Σ Γ ->
    Σ ;;; Γ |-E tLetIn si_na iv_False si_P (tRel 0) : tLetIn si_na iv_False si_P si_P.
  Proof.
    intros h. apply typeE_LetIn; [exact (iv_vdef_False Γ h)|].
    exact (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) (iv_wf_vdef Γ h) eq_refl).
  Qed.

  (** [let z : Prop := ∀P:Prop. P in λx:Prop. x]. *)
  Lemma iv_letlam_typed (Γ : context) : wf_localE Σ Γ ->
    Σ ;;; Γ |-E tLetIn si_na iv_False si_P iv_id : tLetIn si_na iv_False si_P iv_PP.
  Proof.
    intros h. apply typeE_LetIn; [exact (iv_vdef_False Γ h)|].
    exact (iv_id_typed _ (iv_wf_vdef Γ h)).
  Qed.

End Generic.

(** ** Retyping at [(λX : s. X) T]

  [iv_idS s] is [λX : s. X]. From [t : T] and [T : s], [iv_retype] types [t] at [(λX : s. X) T];
  its proof ends in [typeE_Cumul] with [cumulE_beta]. Which steps an inversion lemma takes on such
  a derivation is not stated here; each NONDEGEN lemma of an instance that uses it states that
  [(λX : s. X) T] is not [T], and two of them ([iv_fix_conv_differs], [iv_RF_conv_differs]) also
  state that [T] is the declared type of the term. The rule-coverage instances of
  [PCUICPrincipalityEtaInstances] also use the retyped derivations below. *)

Definition iv_idS (s : sort) : term := tLambda si_na (tSort s) (tRel 0).

Lemma iv_retype (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) t T s :
  Σ ;;; Γ |-E T : tSort s -> Σ ;;; Γ |-E t : T -> Σ ;;; Γ |-E t : tApp (iv_idS s) T.
Proof.
  intros hT ht.
  have h : wf_localE Σ Γ := typingE_wf_local ht.
  have hs : wf_sort Σ s := PCUICWfUniversesEta.typing_wf_sortE (Σ := Σ) wfΣ hT.
  have hr : isSortRel (Sort.super s) (binder_relevance si_na) by destruct s; reflexivity.
  have hS : forall Δ, wf_localE Σ Δ -> Σ ;;; Δ |-E tSort s : tSort (Sort.super s).
  { intros Δ hΔ. apply typeE_Sort; [exact hΔ|exact hs]. }
  have w : wf_localE Σ (Γ ,, vass si_na (tSort s)) :=
    iv_wf_vass Σ Γ si_na (tSort s) (Sort.super s) h (hS Γ h) hr.
  refine (typeE_Cumul _ _ t T (tApp (iv_idS s) T) s ht _ _).
  - refine (typeE_App _ _ (iv_idS s) si_na (tSort s) (tSort s) _ T _ _ hT).
    + apply typeE_Prod.
      * exact (iv_vass_s Σ Γ si_na (tSort s) (Sort.super s) (hS Γ h) hr).
      * exact (hS _ w).
    + unfold iv_idS. apply typeE_Lambda.
      * exact (iv_vass Σ Γ si_na (tSort s) (Sort.super s) (hS Γ h) hr).
      * exact (typeE_Rel _ _ 0 (vass si_na (tSort s)) w eq_refl).
  - apply cumulE_Sym.
    exact (@eq_rect term (lift0 0 T) (fun X => cumulSpecE0 Σ Γ Conv (tApp (iv_idS s) T) X)
             (cumulE_beta _ _ Conv si_na (tSort s) (tRel 0) T) T (lift0_p T)).
Qed.

(** [let z := ∀P:Prop. P : Prop in B] has the sort [s] of [B], by a ζ-step on its type. *)
Lemma iv_letty_typed (Σ : global_env_ext) (Γ : context) B s :
  wf_localE Σ Γ -> wf_sort Σ s ->
  Σ ;;; Γ ,, vdef si_na iv_False si_P |-E B : tSort s ->
  Σ ;;; Γ |-E tLetIn si_na iv_False si_P B : tSort s.
Proof.
  intros h hs hB.
  refine (typeE_Cumul _ _ _ (tLetIn si_na iv_False si_P (tSort s)) (tSort s) (Sort.super s) _ _ _).
  - apply typeE_LetIn; [exact (iv_vdef_False Σ Γ h)|exact hB].
  - apply typeE_Sort; [exact h|exact hs].
  - exact (cumulE_zeta _ _ Cumul si_na iv_False si_P (tSort s)).
Qed.

(** ** Instances in [si_Σ] *)

(** *** The η-typed variable

  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g ⊢ y : k (λx:Prop. g x)]. *)

Definition iv_K : term := tProd si_na iv_PP si_P.
Definition iv_Γg : context := [vass si_na iv_PP].
Definition iv_Γkg : context := [vass si_na iv_K; vass si_na iv_PP].
Definition iv_Γk : context := [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K; vass si_na iv_PP].
Definition iv_kg : term := tApp (tRel 1) (tRel 2).
Definition iv_eta_g : term := tLambda si_na si_P (tApp (tRel 3) (tRel 0)).
Definition iv_keta : term := tApp (tRel 1) iv_eta_g.

Lemma iv_K_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E iv_K : tSort (Sort.sort_of_product iv_sPP (Sort.super sProp)).
Proof.
  intros h. unfold iv_K. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na iv_PP _ (iv_PP_typed si_Σ Γ h) eq_refl).
  - exact (iv_P_typed si_Σ _ (iv_wf_vass si_Σ Γ si_na iv_PP _ h (iv_PP_typed si_Σ Γ h) eq_refl)).
Qed.

Lemma iv_wf_Γg : wf_localE si_Σ iv_Γg.
Proof. exact (iv_wf_vass si_Σ [] si_na iv_PP _ localenv_nil (iv_PP_typed si_Σ [] localenv_nil) eq_refl). Qed.

Lemma iv_wf_Γkg : wf_localE si_Σ iv_Γkg.
Proof. exact (iv_wf_vass si_Σ iv_Γg si_na iv_K _ iv_wf_Γg (iv_K_typed iv_Γg iv_wf_Γg) eq_refl). Qed.

Lemma iv_kg0_typed : si_Σ ;;; iv_Γkg |-E tApp (tRel 0) (tRel 1) : si_P.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na iv_PP si_P _ (tRel 1) (iv_K_typed iv_Γkg iv_wf_Γkg)
           (typeE_Rel _ _ 0 (vass si_na iv_K) iv_wf_Γkg eq_refl)
           (typeE_Rel _ _ 1 (vass si_na iv_PP) iv_wf_Γkg eq_refl)).
Qed.

Lemma iv_wf_Γk : wf_localE si_Σ iv_Γk.
Proof. exact (iv_wf_vass si_Σ iv_Γkg si_na (tApp (tRel 0) (tRel 1)) sProp iv_wf_Γkg iv_kg0_typed eq_refl). Qed.

Lemma iv_y_typed : si_Σ ;;; iv_Γk |-E tRel 0 : iv_kg.
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tApp (tRel 0) (tRel 1))) iv_wf_Γk eq_refl). Qed.

Lemma iv_eta_g_typed : si_Σ ;;; iv_Γk |-E iv_eta_g : iv_PP.
Proof.
  have w : wf_localE si_Σ (iv_Γk ,, vass si_na si_P) := iv_wf_P si_Σ iv_Γk iv_wf_Γk.
  unfold iv_eta_g, iv_PP. apply typeE_Lambda.
  - exact (iv_vass si_Σ iv_Γk si_na si_P _ (iv_P_typed si_Σ iv_Γk iv_wf_Γk) eq_refl).
  - exact (typeE_App _ _ (tRel 3) si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w)
             (typeE_Rel _ _ 3 (vass si_na iv_PP) w eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma iv_keta_typed : si_Σ ;;; iv_Γk |-E iv_keta : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ iv_eta_g (iv_K_typed iv_Γk iv_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) iv_wf_Γk eq_refl) iv_eta_g_typed).
Qed.

(** [k g ≤ k (λx:Prop. g x)]: congruence, and the symmetric of one [cumul_eta_l] step. *)
Lemma iv_spec_eta : cumulSpecE si_Σ iv_Γk iv_kg iv_keta.
Proof.
  unfold cumulSpecE, iv_kg, iv_keta, iv_eta_g.
  apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
Qed.

Lemma iv_rel_typed : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta.
Proof. exact (typeE_Cumul _ _ (tRel 0) iv_kg iv_keta sProp iv_y_typed iv_keta_typed iv_spec_eta). Qed.

Lemma iv_join_eta : JoinE si_Σ iv_Γk Cumul iv_kg iv_keta.
Proof. exact (wsE_join (into_ws_cumul_pbE_spec (Σ := si_Σ) iv_spec_eta eq_refl eq_refl eq_refl)). Qed.

(** [k g] and [k (λx:Prop. g x)] differ. *)
Lemma iv_kg_keta_differ : iv_kg <> iv_keta.
Proof. discriminate. Qed.

(* INSTANCE NOT-BUILT: degenerate, a round trip: the premise [iv_join_eta] is [wsE_join (into_ws_cumul_pbE_spec iv_spec_eta …)], the JoinE projection of a [ws_cumul_pbE] whose statement is the conclusion [iv_Γk ⊢E iv_kg ≤ iv_keta], and [into_ws_cumulE] rebuilds that [ws_cumul_pbE] from the projected JoinE; a JoinE built directly from a step (e.g. [JoinE_eta1_l]), not a forgotten [ws_cumul_pbE], would make the target's closedness from typing run; no non-degenerate witness built yet *)
Lemma into_ws_cumulE_inst : si_Σ ;;; iv_Γk ⊢E iv_kg ≤ iv_keta.
Proof. exact (into_ws_cumulE si_Σ si_wfE (T := iv_kg) (U := iv_keta) iv_y_typed iv_keta_typed iv_join_eta). Qed.

(** Not every type of [iv_Γk] is closed on its own: [k g] refers to the two entries before it, so
    the closedness of the context is checked against its dependencies. *)
Lemma typing_closed_ctxE_inst_nondeg : forallb (fun d => closedn 0 (decl_type d)) iv_Γk = false.
Proof. reflexivity. Qed.

(** [is_closed_context] is a boolean, so it computes on every concrete context.
    INSTANCE NONDEGEN PCUICInversionEtaInstances.typing_closed_ctxE_inst_nondeg *)
Lemma typing_closed_ctxE_inst : is_closed_context iv_Γk.
Proof. exact (typing_closed_ctxE si_Σ si_wfE iv_Γk (tRel 0) iv_keta iv_rel_typed). Qed.

(* INSTANCE IMPOSSIBLE: the conclusion relates the type T with itself, in every instance and environment *)
Lemma typing_ws_cumul_pbE_inst : si_Σ ;;; iv_Γk ⊢E iv_keta ≤ iv_keta.
Proof. exact (typing_ws_cumul_pbE si_Σ si_wfE Cumul iv_Γk (tRel 0) iv_keta iv_rel_typed). Qed.

(** The declared type of [y] in [iv_Γk], lifted over [y], is [k g], and [k g] is not
    [k (λx:Prop. g x)]. *)
Lemma iv_y_decl_kg :
  (forall decl, nth_error iv_Γk 0 = Some decl -> lift0 1 (decl_type decl) = iv_kg) /\ iv_kg <> iv_keta.
Proof. split; [intros decl h; injection h as <-; reflexivity|discriminate]. Qed.

(** The conclusion relates the declared type of [y], lifted, which is [k g], with
    [k (λx:Prop. g x)]; the two differ ([iv_y_decl_kg]).
    INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_y_decl_kg *)
Lemma inversion_RelE_inst :
  ∑ decl, wf_localE si_Σ iv_Γk × (nth_error iv_Γk 0 = Some decl) ×
    si_Σ ;;; iv_Γk ⊢E lift0 1 (decl_type decl) ≤ iv_keta.
Proof. exact (inversion_RelE si_Σ si_wfE (T := iv_keta) iv_rel_typed). Qed.

(* INSTANCE IMPOSSIBLE: the conclusion is False: no derivation types a variable tVar, in any context and environment *)
Definition inversion_VarE_inst : forall T, si_Σ ;;; [] |-E tVar "x" : T -> False :=
  fun T h => inversion_VarE si_Σ h.

(* INSTANCE IMPOSSIBLE: the conclusion is False: no derivation types an existential variable tEvar, in any context and environment *)
Definition inversion_EvarE_inst : forall T, si_Σ ;;; [] |-E tEvar 0 [] : T -> False :=
  fun T h => inversion_EvarE si_Σ h.

(** *** Sorts, products, abstractions, let-ins *)

(** [Prop : (λX : Type₂. X) Type₁]. *)
Lemma iv_P_typed_conv :
  si_Σ ;;; [] |-E si_P : tApp (iv_idS (Sort.super (Sort.super sProp))) (tSort (Sort.super sProp)).
Proof.
  apply (iv_retype si_Σ si_wfE); [|exact (iv_P_typed si_Σ [] localenv_nil)].
  apply typeE_Sort; [constructor|].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)).
Qed.

(** **** A sort typed at a let-bound variable of the context

  [U := Type₁ : Type₂ ⊢ Prop : U]: the derivation ends in [typeE_Cumul] whose conversion
  [Type₁ ≤ U] is the δ-step of [U] ([cumulE_rel]); the conclusion of the inversion relates
  [Type₁] with the context variable [U]. *)

Definition iv_sT1 : sort := Sort.super sProp.
Definition iv_sT2 : sort := Sort.super iv_sT1.

Lemma iv_T1_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tSort iv_sT1 : tSort iv_sT2.
Proof.
  intros h. apply typeE_Sort; [exact h|].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)).
Qed.

Lemma iv_T2_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tSort iv_sT2 : tSort (Sort.super iv_sT2).
Proof.
  intros h. apply typeE_Sort; [exact h|].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_T1_typed [] localenv_nil)).
Qed.

Definition iv_ΓU : context := [vdef si_na (tSort iv_sT1) (tSort iv_sT2)].

Lemma iv_wf_ΓU : wf_localE si_Σ iv_ΓU.
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na _ _ _ (iv_T1_typed [] localenv_nil) (iv_T2_typed [] localenv_nil) eq_refl).
Qed.

Lemma iv_P_typed_U : si_Σ ;;; iv_ΓU |-E si_P : tRel 0.
Proof.
  refine (typeE_Cumul _ _ si_P (tSort iv_sT1) (tRel 0) iv_sT2 (iv_P_typed si_Σ iv_ΓU iv_wf_ΓU) _ _).
  - exact (typeE_Rel _ _ 0 (vdef si_na (tSort iv_sT1) (tSort iv_sT2)) iv_wf_ΓU eq_refl).
  - apply cumulE_Sym. exact (cumulE_rel si_Σ iv_ΓU Conv 0 (tSort iv_sT1) eq_refl).
Qed.

(** The type [U] of [Prop] is the variable of [iv_ΓU], let-bound to [Type₁], and is not [Type₁]
    itself: the inversion relates [Type₁] with [U] only through the let of the context. *)
Lemma iv_U_delta_nondeg :
  nth_error iv_ΓU 0 = Some (vdef si_na (tSort (Sort.super sProp)) (tSort iv_sT2)) /\
  tRel 0 <> tSort (Sort.super sProp).
Proof. split; [reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_U_delta_nondeg *)
Lemma inversion_SortE_inst :
  wf_localE si_Σ iv_ΓU × wf_sort si_Σ sProp × si_Σ ;;; iv_ΓU ⊢E tSort (Sort.super sProp) ≤ tRel 0.
Proof. exact (inversion_SortE si_Σ si_wfE (Γ := iv_ΓU) (T := tRel 0) iv_P_typed_U). Qed.

(** [∀P:Prop. P : (λX : Type₁. X) Prop]. *)
Lemma iv_False_typed_conv : si_Σ ;;; [] |-E iv_False : tApp (iv_idS (Sort.super sProp)) si_P.
Proof.
  exact (iv_retype si_Σ si_wfE [] iv_False si_P (Sort.super sProp) (iv_P_typed si_Σ [] localenv_nil)
           (iv_False_typed si_Σ [] localenv_nil)).
Qed.

(** The type [(λX : Type₁. X) Prop] is not [Prop]. *)
Lemma iv_P_conv_differs : tApp (iv_idS (Sort.super sProp)) si_P <> si_P.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_P_conv_differs *)
Lemma inversion_ProdE_inst :
  ∑ s1 s2, lift_typing typingE si_Σ [] (j_vass_s si_na si_P s1) ×
    si_Σ ;;; [] ,, vass si_na si_P |-E tRel 0 : tSort s2 ×
    si_Σ ;;; [] ⊢E tSort (Sort.sort_of_product s1 s2) ≤ tApp (iv_idS (Sort.super sProp)) si_P.
Proof. exact (inversion_ProdE si_Σ si_wfE (T := tApp (iv_idS (Sort.super sProp)) si_P) iv_False_typed_conv). Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_P_conv_differs *)
Definition inversion_Prod_sizeE_inst :=
  inversion_Prod_sizeE si_Σ si_wfE (T := tApp (iv_idS (Sort.super sProp)) si_P) iv_False_typed_conv.

(** [λx:Prop. x : (λX : s. X) (Prop → Prop)]. *)
Lemma iv_id_typed_conv : si_Σ ;;; [] |-E iv_id : tApp (iv_idS iv_sPP) iv_PP.
Proof.
  exact (iv_retype si_Σ si_wfE [] iv_id iv_PP iv_sPP (iv_PP_typed si_Σ [] localenv_nil)
           (iv_id_typed si_Σ [] localenv_nil)).
Qed.

(** The type [(λX : s. X) (Prop → Prop)] is not [Prop → Prop]. *)
Lemma iv_PP_conv_differs : tApp (iv_idS iv_sPP) iv_PP <> iv_PP.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_PP_conv_differs *)
Lemma inversion_LambdaE_inst :
  ∑ B, lift_typing typingE si_Σ [] (j_vass si_na si_P) ×
    si_Σ ;;; [] ,, vass si_na si_P |-E tRel 0 : B ×
    si_Σ ;;; [] ⊢E tProd si_na si_P B ≤ tApp (iv_idS iv_sPP) iv_PP.
Proof. exact (inversion_LambdaE si_Σ si_wfE (T := tApp (iv_idS iv_sPP) iv_PP) iv_id_typed_conv). Qed.

(** [let z : Prop := ∀P:Prop. P in z : (λX : Type₁. X) (let z : Prop := ∀P:Prop. P in Prop)]. *)
Lemma iv_let_typed_conv :
  si_Σ ;;; [] |-E tLetIn si_na iv_False si_P (tRel 0)
    : tApp (iv_idS (Sort.super sProp)) (tLetIn si_na iv_False si_P si_P).
Proof.
  apply (iv_retype si_Σ si_wfE); [|exact (iv_let_typed si_Σ [] localenv_nil)].
  apply iv_letty_typed; [constructor| |exact (iv_P_typed si_Σ _ (iv_wf_vdef si_Σ [] localenv_nil))].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)).
Qed.

(** The type [(λX : Type₁. X) (let z := … in Prop)] is not [let z := … in Prop]. *)
Lemma iv_letP_conv_differs :
  tApp (iv_idS (Sort.super sProp)) (tLetIn si_na iv_False si_P si_P) <> tLetIn si_na iv_False si_P si_P.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_letP_conv_differs *)
Lemma inversion_LetInE_inst :
  ∑ A, lift_typing typingE si_Σ [] (j_vdef si_na iv_False si_P) ×
    si_Σ ;;; [] ,, vdef si_na iv_False si_P |-E tRel 0 : A ×
    si_Σ ;;; [] ⊢E tLetIn si_na iv_False si_P A
      ≤ tApp (iv_idS (Sort.super sProp)) (tLetIn si_na iv_False si_P si_P).
Proof.
  exact (inversion_LetInE si_Σ si_wfE (T := tApp (iv_idS (Sort.super sProp)) (tLetIn si_na iv_False si_P si_P))
           iv_let_typed_conv).
Qed.

(** [let z : Prop := ∀P:Prop. P in λx:Prop. x : (λX : s. X) (let z : Prop := ∀P:Prop. P in Prop → Prop)]. *)
Lemma iv_letlam_typed_conv :
  si_Σ ;;; [] |-E tLetIn si_na iv_False si_P iv_id : tApp (iv_idS iv_sPP) (tLetIn si_na iv_False si_P iv_PP).
Proof.
  apply (iv_retype si_Σ si_wfE); [|exact (iv_letlam_typed si_Σ [] localenv_nil)].
  apply iv_letty_typed; [constructor| |exact (iv_PP_typed si_Σ _ (iv_wf_vdef si_Σ [] localenv_nil))].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_PP_typed si_Σ [] localenv_nil)).
Qed.

(** The type [(λX : s. X) (let z := … in Prop → Prop)] is not [let z := … in Prop → Prop]. *)
Lemma iv_letPP_conv_differs :
  tApp (iv_idS iv_sPP) (tLetIn si_na iv_False si_P iv_PP) <> tLetIn si_na iv_False si_P iv_PP.
Proof. discriminate. Qed.

(** [let z : Prop := ∀P:Prop. P in λx:Prop. x] is [it_mkLambda_or_LetIn [x : Prop; z := ∀P:Prop. P] x].
    INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_letPP_conv_differs *)
Lemma inversion_it_mkLambda_or_LetInE_inst :
  ∑ A, si_Σ ;;; [] ,,, [vass si_na si_P; vdef si_na iv_False si_P] |-E tRel 0 : A ×
    si_Σ ;;; [] ⊢E it_mkProd_or_LetIn [vass si_na si_P; vdef si_na iv_False si_P] A
      ≤ tApp (iv_idS iv_sPP) (tLetIn si_na iv_False si_P iv_PP).
Proof.
  exact (@inversion_it_mkLambda_or_LetInE _ si_Σ si_wfE [] [vass si_na si_P; vdef si_na iv_False si_P]
           (tRel 0) (tApp (iv_idS iv_sPP) (tLetIn si_na iv_False si_P iv_PP)) iv_letlam_typed_conv).
Qed.

(** *** The inductive [I] and its constructor *)

Lemma iv_ind_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
Proof. intros h. exact (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive eq_refl). Qed.

Lemma iv_cstr_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] : tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof.
  intros h.
  exact (typeE_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl h si_declared_constructor eq_refl).
Qed.

(** [I X : Prop] when [X : Prop]. *)
Lemma iv_IX_typed (Γ : context) X : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E X : si_P ->
  si_Σ ;;; Γ |-E tApp (tInd si_ind []) X : si_P.
Proof.
  intros h hX.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P si_P _ X (iv_PP_typed si_Σ Γ h) (iv_ind_typed Γ h) hX).
Qed.

Lemma iv_cstr_prod_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))
    : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl).
  - exact (iv_IX_typed _ (tRel 0) (iv_wf_P si_Σ Γ h)
             (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P si_Σ Γ h) eq_refl)).
Qed.

(** [I : (λX : s. X) (Prop → Prop)]. *)
Lemma iv_ind_typed_conv : si_Σ ;;; [] |-E tInd si_ind [] : tApp (iv_idS iv_sPP) si_arity.
Proof.
  exact (iv_retype si_Σ si_wfE [] (tInd si_ind []) si_arity iv_sPP (iv_PP_typed si_Σ [] localenv_nil)
           (iv_ind_typed [] localenv_nil)).
Qed.

(** **** An inductive type typed through a let-bound variable of the context

  [Z := Prop : Type₁ ⊢ I : Z → Prop]: the conversion [Prop → Prop ≤ Z → Prop] is the δ-step of
  [Z] in the domain. *)

Definition iv_ΓZ : context := [vdef si_na si_P (tSort iv_sT1)].

Lemma iv_wf_ΓZ : wf_localE si_Σ iv_ΓZ.
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na _ _ _ (iv_P_typed si_Σ [] localenv_nil) (iv_T1_typed [] localenv_nil) eq_refl).
Qed.

Definition iv_ZP : term := tProd si_na (tRel 0) si_P.

Lemma iv_ZP_typed : si_Σ ;;; iv_ΓZ |-E iv_ZP : tSort (Sort.sort_of_product iv_sT1 iv_sT1).
Proof.
  have hZ : si_Σ ;;; iv_ΓZ |-E tRel 0 : tSort iv_sT1 :=
    typeE_Rel _ _ 0 (vdef si_na si_P (tSort iv_sT1)) iv_wf_ΓZ eq_refl.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ iv_ΓZ si_na (tRel 0) _ hZ eq_refl).
  - exact (iv_P_typed si_Σ _ (iv_wf_vass si_Σ iv_ΓZ si_na (tRel 0) _ iv_wf_ΓZ hZ eq_refl)).
Qed.

Lemma iv_ind_typed_Z : si_Σ ;;; iv_ΓZ |-E tInd si_ind [] : iv_ZP.
Proof.
  refine (typeE_Cumul _ _ _ si_arity iv_ZP _ (iv_ind_typed iv_ΓZ iv_wf_ΓZ) iv_ZP_typed _).
  unfold iv_ZP, si_arity. apply cumulE_Prod; [reflexivity| |apply cumulE_Refl].
  apply cumulE_Sym. exact (cumulE_rel si_Σ iv_ΓZ Conv 0 si_P eq_refl).
Qed.

(** The domain of the type [Z → Prop] of [I] is the variable of [iv_ΓZ], let-bound to [Prop], and
    [Z → Prop] is not the arity [Prop → Prop] of [I]. *)
Lemma iv_Z_delta_nondeg :
  nth_error iv_ΓZ 0 = Some (vdef si_na si_P (tSort iv_sT1)) /\ iv_ZP <> si_arity.
Proof. split; [reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_Z_delta_nondeg *)
Lemma inversion_IndE_inst :
  ∑ mdecl idecl, wf_localE si_Σ iv_ΓZ × declared_inductive si_Σ si_ind mdecl idecl ×
    consistent_instance_ext si_Σ (ind_universes mdecl) [] ×
    si_Σ ;;; iv_ΓZ ⊢E subst_instance [] idecl.(ind_type) ≤ iv_ZP.
Proof. exact (inversion_IndE si_Σ si_wfE (T := iv_ZP) iv_ind_typed_Z). Qed.

(** [c : (λX : Prop. X) (Π A : Prop. I A)]. *)
Lemma iv_cstr_typed_conv :
  si_Σ ;;; [] |-E tConstruct si_ind 0 []
    : tApp (iv_idS (Sort.sort_of_product (Sort.super sProp) sProp)) (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))).
Proof.
  exact (iv_retype si_Σ si_wfE [] (tConstruct si_ind 0 []) (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)))
           (Sort.sort_of_product (Sort.super sProp) sProp) (iv_cstr_prod_typed [] localenv_nil)
           (iv_cstr_typed [] localenv_nil)).
Qed.

(** **** A constructor typed through a let-bound variable of the context

  [J := I : Prop → Prop ⊢ c : Π A : Prop. J A]: the conversion [Π A. I A ≤ Π A. J A] is the
  δ-step of [J] in the head of the codomain. *)

Definition iv_ΓJ : context := [vdef si_na (tInd si_ind []) si_arity].

Lemma iv_wf_ΓJ : wf_localE si_Σ iv_ΓJ.
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na _ _ _ (iv_ind_typed [] localenv_nil) (iv_PP_typed si_Σ [] localenv_nil) eq_refl).
Qed.

Definition iv_PiJ : term := tProd si_na si_P (tApp (tRel 1) (tRel 0)).

Lemma iv_PiJ_typed : si_Σ ;;; iv_ΓJ |-E iv_PiJ : tSort (Sort.sort_of_product iv_sT1 sProp).
Proof.
  have w := iv_wf_P si_Σ iv_ΓJ iv_wf_ΓJ.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ iv_ΓJ si_na si_P _ (iv_P_typed si_Σ iv_ΓJ iv_wf_ΓJ) eq_refl).
  - exact (typeE_App _ _ (tRel 1) si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w)
             (typeE_Rel _ _ 1 (vdef si_na (tInd si_ind []) si_arity) w eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma iv_cstr_typed_J : si_Σ ;;; iv_ΓJ |-E tConstruct si_ind 0 [] : iv_PiJ.
Proof.
  refine (typeE_Cumul _ _ _ (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))) iv_PiJ _
            (iv_cstr_typed iv_ΓJ iv_wf_ΓJ) iv_PiJ_typed _).
  unfold iv_PiJ. apply cumulE_Prod; [reflexivity|apply cumulE_Refl|].
  apply cumulE_App; [|apply cumulE_Refl].
  apply cumulE_Sym. exact (cumulE_rel si_Σ (iv_ΓJ ,, vass si_na si_P) Conv 1 (tInd si_ind []) eq_refl).
Qed.

(** The head of the codomain of [Π A : Prop. J A] is the variable of [iv_ΓJ], let-bound to [I],
    and [Π A : Prop. J A] is not the constructor type [Π A : Prop. I A]. *)
Lemma iv_J_delta_nondeg :
  nth_error iv_ΓJ 0 = Some (vdef si_na (tInd si_ind []) si_arity) /\
  iv_PiJ <> tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof. split; [reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_J_delta_nondeg *)
Lemma inversion_ConstructE_inst :
  ∑ mdecl idecl cdecl, wf_localE si_Σ iv_ΓJ × declared_constructor si_Σ.1 (si_ind, 0) mdecl idecl cdecl ×
    consistent_instance_ext si_Σ (ind_universes mdecl) [] ×
    si_Σ ;;; iv_ΓJ ⊢E type_of_constructor mdecl cdecl (si_ind, 0) [] ≤ iv_PiJ.
Proof. exact (inversion_ConstructE si_Σ si_wfE (T := iv_PiJ) iv_cstr_typed_J). Qed.

(** *** A [match]

  In the context [x : Prop], [match c x as z in I x return I x with c => c x end]: the branch
  returns [c x] at the branch type [(λ z : I x. I x) (c x)], which a β-step relates to [I x]. *)

Definition iv_Ix (k : nat) : term := tApp (tInd si_ind []) (tRel k).
Definition iv_Γ1 : context := [vass si_na si_P].
Definition iv_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition iv_mp : predicate term :=
  {| pparams := [tRel 0]; puinst := []; pcontext := ind_predicate_context si_ind si_mdecl si_idecl;
     preturn := iv_Ix 1 |}.
Definition iv_disc : term := tApp (tConstruct si_ind 0 []) (tRel 0).
Definition iv_br : branch term := {| bcontext := []; bbody := iv_disc |}.
Definition iv_match : term := tCase iv_ci iv_mp iv_disc [iv_br].
Definition iv_zna : aname := {| binder_name := nNamed (ind_name si_idecl); binder_relevance := Relevant |}.

Lemma iv_wf_Γ1 : wf_localE si_Σ iv_Γ1.
Proof. exact (iv_wf_P si_Σ [] localenv_nil). Qed.

Lemma iv_x_typed : si_Σ ;;; iv_Γ1 |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vass si_na si_P) iv_wf_Γ1 eq_refl). Qed.

Lemma iv_wf_mp : wf_predicate si_mdecl si_idecl iv_mp.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma iv_wf_br : wf_branch si_cdecl iv_br.
Proof. constructor. Qed.

Lemma iv_Ix0_typed : si_Σ ;;; iv_Γ1 |-E iv_Ix 0 : si_P.
Proof. exact (iv_IX_typed iv_Γ1 (tRel 0) iv_wf_Γ1 iv_x_typed). Qed.

Lemma iv_wf_pctx : wf_localE si_Σ (iv_Γ1 ,, vass iv_zna (iv_Ix 0)).
Proof. exact (iv_wf_vass si_Σ iv_Γ1 iv_zna (iv_Ix 0) sProp iv_wf_Γ1 iv_Ix0_typed eq_refl). Qed.

Lemma iv_pret_typed : si_Σ ;;; iv_Γ1 ,, vass iv_zna (iv_Ix 0) |-E iv_Ix 1 : si_P.
Proof.
  exact (iv_IX_typed _ (tRel 1) iv_wf_pctx (typeE_Rel _ _ 1 (vass si_na si_P) iv_wf_pctx eq_refl)).
Qed.

Lemma iv_disc_typed : si_Σ ;;; iv_Γ1 |-E iv_disc : iv_Ix 0.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ (tRel 0)
           (iv_cstr_prod_typed iv_Γ1 iv_wf_Γ1) (iv_cstr_typed iv_Γ1 iv_wf_Γ1) iv_x_typed).
Qed.

Lemma iv_ctx_inst : ctx_inst (typingE si_Σ) iv_Γ1 [tRel 0] [vass si_na si_P].
Proof. econstructor; [|constructor]. exact iv_x_typed. Qed.

Lemma iv_bty_typed :
  si_Σ ;;; iv_Γ1 |-E tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc : si_P.
Proof.
  refine (typeE_App _ _ (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_zna (iv_Ix 0) si_P _ iv_disc
            _ _ iv_disc_typed).
  - apply typeE_Prod.
    + exact (iv_vass_s si_Σ iv_Γ1 iv_zna (iv_Ix 0) sProp iv_Ix0_typed eq_refl).
    + exact (iv_P_typed si_Σ _ iv_wf_pctx).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ iv_Γ1 iv_zna (iv_Ix 0) sProp iv_Ix0_typed eq_refl).
    + exact iv_pret_typed.
Qed.

Lemma iv_br_typed :
  si_Σ ;;; iv_Γ1 |-E iv_disc : tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc.
Proof.
  refine (typeE_Cumul _ _ iv_disc (iv_Ix 0) _ sProp iv_disc_typed iv_bty_typed _).
  apply cumulE_Sym. exact (cumulE_beta _ _ Conv iv_zna (iv_Ix 0) (iv_Ix 1) iv_disc).
Qed.

Lemma iv_case_side :
  case_side_conditions (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) si_Σ iv_Γ1 iv_ci iv_mp sProp
    si_mdecl si_idecl [] (case_predicate_context si_ind si_mdecl si_idecl iv_mp).
Proof.
  constructor.
  - reflexivity.
  - exact iv_wf_mp.
  - reflexivity.
  - exact iv_wf_pctx.
  - exact (alpha_eq_reflexive (pcontext iv_mp)).
  - reflexivity.
  - reflexivity.
  - exact iv_ctx_inst.
  - reflexivity.
Qed.

Lemma iv_case_brs :
  case_branch_typing (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) iv_Γ1 iv_ci iv_mp sProp si_mdecl si_idecl
    (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl iv_mp) (preturn iv_mp))
    [iv_br].
Proof.
  constructor.
  - constructor; [exact iv_wf_br|constructor].
  - constructor; [|constructor].
    split; [constructor|]. cbv zeta. split; [|split].
    + exact iv_wf_Γ1.
    + exact iv_br_typed.
    + exact iv_bty_typed.
Qed.

Definition iv_match_ty : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl iv_mp) (preturn iv_mp))
    ([] ++ [iv_disc]).

Lemma iv_match_typed : si_Σ ;;; iv_Γ1 |-E iv_match : iv_match_ty.
Proof.
  eapply (typeE_Case _ _ iv_ci iv_mp iv_disc [iv_br] [] sProp si_mdecl si_idecl).
  - exact si_declared_inductive.
  - exact iv_pret_typed.
  - exact iv_disc_typed.
  - exact iv_case_side.
  - exact iv_case_brs.
Qed.

(** [match c x … end : (λX : Prop. X) T], [T] the type the [match] rule gives. *)
Lemma iv_match_typed_conv : si_Σ ;;; iv_Γ1 |-E iv_match : tApp (iv_idS sProp) iv_match_ty.
Proof. exact (iv_retype si_Σ si_wfE iv_Γ1 iv_match iv_match_ty sProp iv_bty_typed iv_match_typed). Qed.

(** The type [(λX : Prop. X) T] is not [T] ([iv_match_ty]). *)
Lemma iv_match_conv_differs : tApp (iv_idS sProp) iv_match_ty <> iv_match_ty.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_match_conv_differs *)
Definition inversion_CaseE_inst :=
  inversion_CaseE si_Σ si_wfE (T := tApp (iv_idS sProp) iv_match_ty) iv_match_typed_conv.

(** *** A fixpoint

  [fix f (x : I (∀P:Prop. P)) : I (∀P:Prop. P) := x], structural on [x]. *)

Definition iv_IF : term := tApp (tInd si_ind []) iv_False.
Definition iv_fix_ty : term := tProd si_na iv_IF iv_IF.
Definition iv_mfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_fix_ty; dbody := tLambda si_na iv_IF (tRel 0); rarg := 0 |}].
Definition iv_Γf : context := [vass si_na iv_fix_ty].

Lemma iv_IF_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E iv_IF : si_P.
Proof. intros h. exact (iv_IX_typed Γ iv_False h (iv_False_typed si_Σ Γ h)). Qed.

Lemma iv_wf_IF (Γ : context) : wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na iv_IF).
Proof. intros h. exact (iv_wf_vass si_Σ Γ si_na iv_IF sProp h (iv_IF_typed Γ h) eq_refl). Qed.

Lemma iv_fix_ty_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E iv_fix_ty : tSort (Sort.sort_of_product sProp sProp).
Proof.
  intros h. unfold iv_fix_ty. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na iv_IF sProp (iv_IF_typed Γ h) eq_refl).
  - exact (iv_IF_typed _ (iv_wf_IF Γ h)).
Qed.

Lemma iv_wf_Γf : wf_localE si_Σ iv_Γf.
Proof. exact (iv_wf_vass si_Σ [] si_na iv_fix_ty _ localenv_nil (iv_fix_ty_typed [] localenv_nil) eq_refl). Qed.

Lemma iv_fix_body_typed : si_Σ ;;; iv_Γf |-E tLambda si_na iv_IF (tRel 0) : lift0 1 iv_fix_ty.
Proof.
  change (lift0 1 iv_fix_ty) with (tProd si_na iv_IF iv_IF).
  apply typeE_Lambda.
  - exact (iv_vass si_Σ iv_Γf si_na iv_IF sProp (iv_IF_typed iv_Γf iv_wf_Γf) eq_refl).
  - exact (typeE_Rel _ _ 0 (vass si_na iv_IF) (iv_wf_IF iv_Γf iv_wf_Γf) eq_refl).
Qed.

Lemma iv_fix_guard : fix_guard si_Σ [] iv_mfix.
Proof.
  change (guard_cl Fix si_Σ [] iv_mfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma iv_wf_fix : wf_fixpointE si_Σ [] iv_mfix.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_fix_ty. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma iv_fix_typed : si_Σ ;;; [] |-E tFix iv_mfix 0 : iv_fix_ty.
Proof.
  refine (typeE_Fix _ _ iv_mfix 0 _ localenv_nil iv_fix_guard eq_refl _ _ iv_wf_fix).
  - constructor; [|constructor].
    exact (iv_vass si_Σ [] si_na iv_fix_ty _ (iv_fix_ty_typed [] localenv_nil) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef si_Σ iv_Γf si_na _ (lift0 1 iv_fix_ty) _ iv_fix_body_typed
             (iv_fix_ty_typed iv_Γf iv_wf_Γf) eq_refl).
Qed.

(** [fix f … : (λX : Prop. X) (I (∀P:Prop. P) → I (∀P:Prop. P))]. *)
Lemma iv_fix_typed_conv :
  si_Σ ;;; [] |-E tFix iv_mfix 0 : tApp (iv_idS (Sort.sort_of_product sProp sProp)) iv_fix_ty.
Proof.
  exact (iv_retype si_Σ si_wfE [] (tFix iv_mfix 0) iv_fix_ty (Sort.sort_of_product sProp sProp)
           (iv_fix_ty_typed [] localenv_nil) iv_fix_typed).
Qed.

(** The declared type of the first definition of [iv_mfix] is [I (∀P:Prop. P) → I (∀P:Prop. P)],
    and the type [(λX : Prop. X) (I (∀P:Prop. P) → I (∀P:Prop. P))] differs from it. *)
Lemma iv_fix_conv_differs :
  (forall d, nth_error iv_mfix 0 = Some d -> dtype d = iv_fix_ty) /\
  tApp (iv_idS (Sort.sort_of_product sProp sProp)) iv_fix_ty <> iv_fix_ty.
Proof. split; [intros d h; injection h as <-; reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_fix_conv_differs *)
Definition inversion_FixE_inst :=
  inversion_FixE si_Σ si_wfE (T := tApp (iv_idS (Sort.sort_of_product sProp sProp)) iv_fix_ty) iv_fix_typed_conv.

(** *** An application whose codomain depends on the argument

  [c (∀P:Prop. P) : I (∀P:Prop. P)]: the type of [c] is [Π A : Prop. I A], so the application
  instantiates the codomain [I A] at the argument. *)

Definition iv_cF : term := tApp (tConstruct si_ind 0 []) iv_False.

Lemma iv_cF_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E iv_cF : (iv_Ix 0) {0 := iv_False}.
Proof.
  intros h.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (iv_Ix 0) _ iv_False (iv_cstr_prod_typed Γ h)
           (iv_cstr_typed Γ h) (iv_False_typed si_Σ Γ h)).
Qed.

(** The substitution changes the codomain: [I A] becomes [I (∀P:Prop. P)]. *)
Lemma iv_cF_codomain_moves : (iv_Ix 0) {0 := iv_False} <> iv_Ix 0.
Proof. discriminate. Qed.

(** **** The application [c (z → z)] in the context [z := ∀P:Prop. P : Prop]

  The argument [z → z] uses the let [z] of [iv_Γz]; the application has the type
  [(I A){0 := z → z}] = [I (z → z)], and it is typed at [I ((∀P:Prop. P) → z)] by [typeE_Cumul],
  whose conversion is the δ-step of the first [z] ([iv_spec_zz]). *)

Definition iv_Γz : context := [vdef si_na iv_False si_P].

Lemma iv_wf_Γz : wf_localE si_Σ iv_Γz.
Proof. exact (iv_wf_vdef si_Σ [] localenv_nil). Qed.

Definition iv_zz : term := tProd si_na (tRel 0) (tRel 1).
Definition iv_czz : term := tApp (tConstruct si_ind 0 []) iv_zz.
Definition iv_IFz : term := tApp (tInd si_ind []) (tProd si_na iv_False (tRel 1)).

Lemma iv_zz_typed : si_Σ ;;; iv_Γz |-E iv_zz : si_P.
Proof.
  have hz : si_Σ ;;; iv_Γz |-E tRel 0 : si_P := typeE_Rel _ _ 0 (vdef si_na iv_False si_P) iv_wf_Γz eq_refl.
  have w := iv_wf_vass si_Σ iv_Γz si_na (tRel 0) sProp iv_wf_Γz hz eq_refl.
  exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp (iv_vass_s si_Σ iv_Γz si_na (tRel 0) sProp hz eq_refl)
           (typeE_Rel _ _ 1 (vdef si_na iv_False si_P) w eq_refl)).
Qed.

Lemma iv_czz_typed : si_Σ ;;; iv_Γz |-E iv_czz : (iv_Ix 0) {0 := iv_zz}.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (iv_Ix 0) _ iv_zz (iv_cstr_prod_typed iv_Γz iv_wf_Γz)
           (iv_cstr_typed iv_Γz iv_wf_Γz) iv_zz_typed).
Qed.

Lemma iv_IFz_typed : si_Σ ;;; iv_Γz |-E iv_IFz : si_P.
Proof.
  have hF := iv_False_typed si_Σ iv_Γz iv_wf_Γz.
  have w := iv_wf_vass si_Σ iv_Γz si_na iv_False sProp iv_wf_Γz hF eq_refl.
  exact (iv_IX_typed iv_Γz _ iv_wf_Γz
           (typeE_Prod _ _ si_na iv_False (tRel 1) sProp sProp (iv_vass_s si_Σ iv_Γz si_na iv_False sProp hF eq_refl)
              (typeE_Rel _ _ 1 (vdef si_na iv_False si_P) w eq_refl))).
Qed.

(** [I (z → z) ≤ I ((∀P:Prop. P) → z)]: congruence, and the δ-step of [z] in the domain. *)
Lemma iv_spec_zz : cumulSpecE si_Σ iv_Γz (tApp (tInd si_ind []) iv_zz) iv_IFz.
Proof.
  unfold cumulSpecE, iv_zz, iv_IFz. apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_Prod; [reflexivity| |apply cumulE_Refl].
  exact (cumulE_rel si_Σ iv_Γz Conv 0 iv_False eq_refl).
Qed.

Lemma iv_czz_typed_IFz : si_Σ ;;; iv_Γz |-E iv_czz : iv_IFz.
Proof. exact (typeE_Cumul _ _ iv_czz _ iv_IFz sProp iv_czz_typed iv_IFz_typed iv_spec_zz). Qed.

(** The substitution changes the codomain ([I A] becomes [I (z → z)]), and the argument [z → z]
    uses the variable of the context. *)
Lemma iv_czz_codomain_moves : (iv_Ix 0) {0 := iv_zz} <> iv_Ix 0 /\ noccur_between 0 1 iv_zz = false.
Proof. split; [discriminate|reflexivity]. Qed.

(** The codomain moves, the argument uses [z], [z] is let-bound to [∀P:Prop. P] in [iv_Γz], and
    the type [I ((∀P:Prop. P) → z)] the application is typed at is not [I (z → z)]. *)
Lemma iv_czz_IFz_nondeg :
  [/\ (iv_Ix 0) {0 := iv_zz} <> iv_Ix 0, noccur_between 0 1 iv_zz = false,
      nth_error iv_Γz 0 = Some (vdef si_na iv_False si_P) & iv_IFz <> (iv_Ix 0) {0 := iv_zz}].
Proof. split; [discriminate|reflexivity|reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_czz_IFz_nondeg *)
Lemma inversion_AppE_inst :
  ∑ na A B, si_Σ ;;; iv_Γz |-E tConstruct si_ind 0 [] : tProd na A B × si_Σ ;;; iv_Γz |-E iv_zz : A ×
    si_Σ ;;; iv_Γz ⊢E B{0 := iv_zz} ≤ iv_IFz.
Proof. exact (inversion_AppE si_Σ si_wfE (T := iv_IFz) iv_czz_typed_IFz). Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_czz_IFz_nondeg *)
Definition inversion_App_sizeE_inst :=
  inversion_App_sizeE si_Σ si_wfE (T := iv_IFz) iv_czz_typed_IFz.

(** ** Instances in [Σ_po]: a constant and a primitive integer *)

(** [Σ_po_wf] of [PCUICEtaPrimOpInstance], unsquashed: the same proof without its first
    [constructor]. *)
Lemma iv_po_wf_ext : wf_ext Σ_po.
Proof.
  split; [|exact po_udecl_ok].
  split; [exact po_univs_ok|]. split; [exact po_retro_wf|].
  cbn. constructor.
  - constructor; [constructor|].
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_land_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_land_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

Definition iv_po_wfE : wfE Σ_po0 := wf_incl_E (fst iv_po_wf_ext).

Lemma iv_po_declared_int : declared_constant Σ_po po_int_kn po_int_body.
Proof. right; left; reflexivity. Qed.

Lemma iv_land_typed : Σ_po ;;; [] |-E tConst po_land_kn [] : po_land_ty.
Proof. exact (typeE_Const _ _ po_land_kn [] po_land_body localenv_nil Σ_po_declared_land eq_refl). Qed.

(** [int : Set] in any well-formed context of [Σ_po]. *)
Lemma iv_int_typed (Γ : context) : wf_localE Σ_po Γ -> Σ_po ;;; Γ |-E tConst po_int_kn [] : tSort Sort.type0.
Proof. intros h. exact (typeE_Const _ _ po_int_kn [] po_int_body h iv_po_declared_int eq_refl). Qed.

(** [int → int → int : Set]. *)
Lemma iv_land_ty_typed :
  Σ_po ;;; [] |-E po_land_ty : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have hd : forall Γ, wf_localE Σ_po Γ ->
    lift_typing typingE Σ_po Γ (j_vass_s (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0).
  { intros Γ h.
    exact (iv_vass_s Σ_po Γ (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0 (iv_int_typed Γ h) eq_refl). }
  have w1 : wf_localE Σ_po [vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn [])].
  { exact (iv_wf_vass Σ_po [] (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0 localenv_nil
             (iv_int_typed [] localenv_nil) eq_refl). }
  have w2 := iv_wf_vass Σ_po _ (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0 w1
    (iv_int_typed _ w1) eq_refl.
  unfold po_land_ty, tImpl. apply typeE_Prod; [exact (hd [] localenv_nil)|].
  apply typeE_Prod; [exact (hd _ w1)|].
  exact (iv_int_typed _ w2).
Qed.

(** [land : (λX : Set. X) (int → int → int)]. *)
Lemma iv_land_typed_conv :
  Σ_po ;;; [] |-E tConst po_land_kn []
    : tApp (iv_idS (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0))) po_land_ty.
Proof. exact (iv_retype Σ_po iv_po_wfE [] (tConst po_land_kn []) po_land_ty _ iv_land_ty_typed iv_land_typed). Qed.

(** **** [land] and the literal [1] typed through a let-bound variable of the context

  [N := int : Set ⊢ land : N → int → int] and [N := int : Set ⊢ 1 : N]: each derivation ends in
  [typeE_Cumul], whose conversion is the δ-step of [N] (in the first domain for [land]). *)

Definition iv_ΓN : context := [vdef si_na (tConst po_int_kn []) (tSort Sort.type0)].

Lemma iv_wf_ΓN : wf_localE Σ_po iv_ΓN.
Proof.
  apply localenv_cons_def; [constructor|].
  refine (iv_vdef Σ_po [] si_na _ _ (Sort.super Sort.type0) (iv_int_typed [] localenv_nil) _ eq_refl).
  apply typeE_Sort; [constructor|].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := Σ_po) iv_po_wfE (iv_int_typed [] localenv_nil)).
Qed.

Definition iv_iA : aname := mkBindAnn nAnon rel_of_Type.
Definition iv_NT : term := tProd iv_iA (tRel 0) (tImpl (tConst po_int_kn []) (tConst po_int_kn [])).

Lemma iv_NT_typed :
  Σ_po ;;; iv_ΓN |-E iv_NT : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have hN : Σ_po ;;; iv_ΓN |-E tRel 0 : tSort Sort.type0 :=
    typeE_Rel _ _ 0 (vdef si_na (tConst po_int_kn []) (tSort Sort.type0)) iv_wf_ΓN eq_refl.
  have w1 := iv_wf_vass Σ_po iv_ΓN iv_iA (tRel 0) Sort.type0 iv_wf_ΓN hN eq_refl.
  have w2 := iv_wf_vass Σ_po _ iv_iA (tConst po_int_kn []) Sort.type0 w1 (iv_int_typed _ w1) eq_refl.
  unfold iv_NT, tImpl. apply typeE_Prod; [exact (iv_vass_s Σ_po iv_ΓN iv_iA (tRel 0) Sort.type0 hN eq_refl)|].
  apply typeE_Prod; [exact (iv_vass_s Σ_po _ iv_iA (tConst po_int_kn []) Sort.type0 (iv_int_typed _ w1) eq_refl)|].
  exact (iv_int_typed _ w2).
Qed.

Lemma iv_land_typed_N : Σ_po ;;; iv_ΓN |-E tConst po_land_kn [] : iv_NT.
Proof.
  refine (typeE_Cumul _ _ _ po_land_ty iv_NT _
            (typeE_Const _ _ po_land_kn [] po_land_body iv_wf_ΓN Σ_po_declared_land eq_refl) iv_NT_typed _).
  unfold po_land_ty, iv_NT, tImpl. apply cumulE_Prod; [reflexivity| |apply cumulE_Refl].
  apply cumulE_Sym. exact (cumulE_rel Σ_po iv_ΓN Conv 0 (tConst po_int_kn []) eq_refl).
Qed.

(** [land] is declared in [Σ_po] with the type [po_land_ty], [int → int → int]; the first domain
    of [N → int → int] is the variable of [iv_ΓN], let-bound to [int], and [N → int → int] is not
    [po_land_ty]. *)
Lemma iv_N_land_nondeg :
  nth_error iv_ΓN 0 = Some (vdef si_na (tConst po_int_kn []) (tSort Sort.type0)) /\
  declared_constant Σ_po po_land_kn po_land_body /\ cst_type po_land_body = po_land_ty /\ iv_NT <> po_land_ty.
Proof. split; [reflexivity|split; [exact Σ_po_declared_land|split; [reflexivity|discriminate]]]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_N_land_nondeg *)
Lemma inversion_ConstE_inst :
  ∑ decl, wf_localE Σ_po iv_ΓN × declared_constant Σ_po po_land_kn decl ×
    consistent_instance_ext Σ_po (cst_universes decl) [] ×
    Σ_po ;;; iv_ΓN ⊢E subst_instance [] (cst_type decl) ≤ iv_NT.
Proof. exact (inversion_ConstE Σ_po iv_po_wfE (T := iv_NT) iv_land_typed_N). Qed.

(** The literal [1] of the primitive integers. *)
Definition iv_one : PCUICAst.prim_val := prim_int 1%uint63.

Lemma iv_prim_typed : Σ_po ;;; [] |-E tPrim iv_one : prim_type iv_one po_int_kn.
Proof.
  refine (typeE_Prim Σ_po [] iv_one po_int_kn po_int_body localenv_nil eq_refl
            iv_po_declared_int _ _).
  - split; reflexivity.
  - constructor.
Qed.

(** [1 : (λX : Set. X) int]. *)
Lemma iv_prim_typed_conv :
  Σ_po ;;; [] |-E tPrim iv_one : tApp (iv_idS Sort.type0) (prim_type iv_one po_int_kn).
Proof.
  exact (iv_retype Σ_po iv_po_wfE [] (tPrim iv_one) (prim_type iv_one po_int_kn) Sort.type0
           (iv_int_typed [] localenv_nil) iv_prim_typed).
Qed.

Lemma iv_prim_typed_N : Σ_po ;;; iv_ΓN |-E tPrim iv_one : tRel 0.
Proof.
  refine (typeE_Cumul _ _ _ (prim_type iv_one po_int_kn) (tRel 0) Sort.type0 _
            (typeE_Rel _ _ 0 (vdef si_na (tConst po_int_kn []) (tSort Sort.type0)) iv_wf_ΓN eq_refl) _).
  - refine (typeE_Prim Σ_po iv_ΓN iv_one po_int_kn po_int_body iv_wf_ΓN eq_refl iv_po_declared_int _ _);
      [split; reflexivity|constructor].
  - apply cumulE_Sym. exact (cumulE_rel Σ_po iv_ΓN Conv 0 (tConst po_int_kn []) eq_refl).
Qed.

(** The type [N] of [1] is the variable of [iv_ΓN], let-bound to [int], and is not the primitive
    type [int] itself. *)
Lemma iv_N_prim_nondeg :
  nth_error iv_ΓN 0 = Some (vdef si_na (tConst po_int_kn []) (tSort Sort.type0)) /\
  tRel 0 <> prim_type iv_one po_int_kn.
Proof. split; [reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_N_prim_nondeg *)
Lemma inversion_PrimE_inst :
  ∑ prim_ty cdecl,
    [× wf_localE Σ_po iv_ΓN,
      primitive_constant Σ_po (prim_val_tag iv_one) = Some prim_ty,
      declared_constant Σ_po prim_ty cdecl,
      primitive_invariants (prim_val_tag iv_one) cdecl,
      primitive_typing_hyps (typingE Σ_po) Σ_po iv_ΓN iv_one &
      Σ_po ;;; iv_ΓN ⊢E prim_type iv_one prim_ty ≤ tRel 0].
Proof. exact (inversion_PrimE Σ_po iv_po_wfE (Γ := iv_ΓN) (T := tRel 0) iv_prim_typed_N). Qed.

(** ** The environment [iv_env]: [CoInductive R (A : Prop) : Prop := mkR { f : A }] *)

Definition iv_kn : kername := (MPfile ["InvInst"], "R").
Definition iv_ind : inductive := {| inductive_mind := iv_kn; inductive_ind := 0 |}.
Definition iv_fna : aname := mkBindAnn (nNamed "f") Relevant.

Definition iv_cdecl : constructor_body :=
  {| cstr_name := "mkR"; cstr_args := [vass iv_fna (tRel 0)]; cstr_indices := [];
     cstr_type := tProd si_na si_P (tProd iv_fna (tRel 0) (tApp (tRel 2) (tRel 1))); cstr_arity := 1 |}.

(** The projection [f]: in the context [A : Prop, r : R A], its type is [A]. *)
Definition iv_pdecl : projection_body := {| proj_name := "f"; proj_relevance := Relevant; proj_type := tRel 1 |}.

Definition iv_idecl : one_inductive_body :=
  {| ind_name := "R"; ind_indices := []; ind_sort := sProp; ind_type := si_arity;
     ind_kelim := IntoAny; ind_ctors := [iv_cdecl]; ind_projs := [iv_pdecl]; ind_relevance := Relevant |}.

Definition iv_mdecl : mutual_inductive_body :=
  {| ind_finite := CoFinite; ind_npars := 1; ind_params := si_params; ind_bodies := [iv_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition iv_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(iv_kn, InductiveDecl iv_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition iv_Σ : global_env_ext := (iv_env, Monomorphic_ctx).

Definition iv_Γi : context := arities_context [iv_idecl].

Lemma iv_wf_Γi : wf_local si_Σ0 iv_Γi.
Proof.
  apply localenv_cons_abs; [constructor|].
  exact (si_vass _ (mkBindAnn (nNamed "R") rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
Qed.

(** The constructor type [Π A : Prop. A -> R A], in the arities context. *)
Lemma iv_ctype_typed :
  si_Σ0 ;;; iv_Γi |- cstr_type iv_cdecl
    : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.sort_of_product sProp sProp)).
Proof.
  have w2 := si_wf_P iv_Γi iv_wf_Γi.
  have hA : si_Σ0 ;;; iv_Γi ,, vass si_na si_P |- tRel 0 : tSort sProp :=
    type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl.
  have w3 : wf_local si_Σ0 ((iv_Γi ,, vass si_na si_P) ,, vass iv_fna (tRel 0)).
  { apply localenv_cons_abs; [exact w2|exact (si_vass _ iv_fna _ _ hA eq_refl)]. }
  apply type_Prod.
  - exact (si_vass_s _ si_na _ _ (si_P_typed iv_Γi iv_wf_Γi) eq_refl).
  - apply type_Prod.
    + exact (si_vass_s _ iv_fna _ _ hA eq_refl).
    + refine (type_App _ _ (tRel 2) si_na si_P (tSort sProp)
                (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 1) _ _ _).
      * exact (si_arity_typed _ w3).
      * exact (type_Rel _ _ 2 (vass (mkBindAnn (nNamed "R") rel_of_Type) si_arity) w3 eq_refl).
      * exact (type_Rel _ _ 1 (vass si_na si_P) w3 eq_refl).
Qed.

Lemma iv_on_constructor :
  on_constructor cumulSpec0 (lift_typing typing) si_Σ0 iv_mdecl 0 iv_idecl [] iv_cdecl [sProp].
Proof.
  have w2 := si_wf_P iv_Γi iv_wf_Γi.
  unshelve econstructor.
  - reflexivity.
  - reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon Relevant) _ _ iv_ctype_typed eq_refl).
  - split; [exact tt|].
    exact (si_vass_s _ iv_fna _ _ (type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl) eq_refl).
  - constructor.
  - cbn. eapply pos_ass.
    + apply pos_arg_closed. reflexivity.
    + eapply pos_ass.
      * apply pos_arg_closed. reflexivity.
      * exact (pos_concl _ _ _ [vass iv_fna (tRel 0); vass si_na si_P] [tRel 1]
                 (All_cons (x := tRel 1) (eq_refl : is_true (closedn 2 (tRel 1))) All_nil)).
  - intros v e. discriminate e.
  - destruct lets_in_constructor_types; [exact I|reflexivity].
Qed.

Lemma iv_on_ind_body :
  on_ind_body cumulSpec0 (lift_typing typing) si_Σ0 iv_kn iv_mdecl 0 iv_idecl.
Proof.
  unshelve econstructor.
  - exact [[sProp]].
  - exists (tSort sProp). split; [reflexivity|].
    apply arity_red_sort. apply whd_stop. reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
  - constructor; [exact iv_on_constructor|constructor].
  - cbn. constructor; try reflexivity.
    constructor; [|constructor]. cbn. constructor; cbn; reflexivity.
  - reflexivity.
  - reflexivity.
  - exact I.
Qed.

Lemma iv_on_inductive : on_inductive cumulSpec0 (lift_typing typing) si_Σ0 iv_kn iv_mdecl.
Proof.
  constructor.
  - constructor; [exact iv_on_ind_body|constructor].
  - exact (si_wf_P [] si_wf_nil).
  - reflexivity.
  - reflexivity.
Qed.

(** [si_wf]'s proof, with [iv_on_inductive] for the declaration. *)
Lemma iv_wf : wf iv_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                            (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx].
      * exfalso. eapply LevelSet.empty_spec. exact Hx.
      * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
    + exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact si_on_udecl.
    + exact iv_on_inductive.
    + cbn. intros i h; discriminate h.
Qed.

Definition iv_wfE : wfE iv_env := wf_incl_E iv_wf.

Lemma iv_declared_inductive : declared_inductive iv_Σ iv_ind iv_mdecl iv_idecl.
Proof. split; [left; reflexivity|reflexivity]. Qed.

Lemma iv_declared_constructor : declared_constructor iv_Σ (iv_ind, 0) iv_mdecl iv_idecl iv_cdecl.
Proof. split; [exact iv_declared_inductive|reflexivity]. Qed.

(** ** Instances in [iv_Σ]: a cofixpoint and a projection *)

Definition iv_R (X : term) : term := tApp (tInd iv_ind []) X.

Lemma iv_Rind_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E tInd iv_ind [] : si_arity.
Proof. intros h. exact (typeE_Ind _ _ iv_ind [] iv_mdecl iv_idecl h iv_declared_inductive eq_refl). Qed.

Lemma iv_RX_typed (Γ : context) X : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E X : si_P -> iv_Σ ;;; Γ |-E iv_R X : si_P.
Proof.
  intros h hX.
  exact (typeE_App _ _ (tInd iv_ind []) si_na si_P si_P _ X (iv_PP_typed iv_Σ Γ h) (iv_Rind_typed Γ h) hX).
Qed.

(** [mkR : Π A : Prop. A -> R A]. *)
Lemma iv_mkR_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tConstruct iv_ind 0 [] : tProd si_na si_P (tProd iv_fna (tRel 0) (iv_R (tRel 1))).
Proof.
  intros h.
  exact (typeE_Construct _ _ iv_ind 0 [] iv_mdecl iv_idecl iv_cdecl h iv_declared_constructor eq_refl).
Qed.

Lemma iv_mkR_ty_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tProd si_na si_P (tProd iv_fna (tRel 0) (iv_R (tRel 1)))
    : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.sort_of_product sProp sProp)).
Proof.
  intros h.
  have w1 := iv_wf_P iv_Σ Γ h.
  have hA : iv_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 : tSort sProp :=
    typeE_Rel _ _ 0 (vass si_na si_P) w1 eq_refl.
  have w2 := iv_wf_vass iv_Σ _ iv_fna (tRel 0) sProp w1 hA eq_refl.
  apply typeE_Prod; [exact (iv_vass_s iv_Σ Γ si_na si_P _ (iv_P_typed iv_Σ Γ h) eq_refl)|].
  apply typeE_Prod; [exact (iv_vass_s iv_Σ _ iv_fna (tRel 0) sProp hA eq_refl)|].
  exact (iv_RX_typed _ (tRel 1) w2 (typeE_Rel _ _ 1 (vass si_na si_P) w2 eq_refl)).
Qed.

(** *** A cofixpoint

  In the context [p : ∀P:Prop. P], [cofix g : R (∀P:Prop. P) := mkR (∀P:Prop. P) p]. *)

Definition iv_RF : term := iv_R iv_False.
Definition iv_cofix_body : term := tApp (tApp (tConstruct iv_ind 0 []) iv_False) (tRel 1).
Definition iv_cmfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_RF; dbody := iv_cofix_body; rarg := 0 |}].
Definition iv_Γc : context := [vass si_na iv_False].
Definition iv_Γcf : context := [vass si_na iv_RF; vass si_na iv_False].

Lemma iv_wf_Γc : wf_localE iv_Σ iv_Γc.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_False sProp localenv_nil (iv_False_typed iv_Σ [] localenv_nil) eq_refl). Qed.

Lemma iv_RF_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E iv_RF : si_P.
Proof. intros h. exact (iv_RX_typed Γ iv_False h (iv_False_typed iv_Σ Γ h)). Qed.

(** [mkR (∀P:Prop. P) : (∀P:Prop. P) -> R (∀P:Prop. P)]. *)
Lemma iv_mkRF_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tApp (tConstruct iv_ind 0 []) iv_False : tProd iv_fna iv_False iv_RF.
Proof.
  intros h.
  exact (typeE_App _ _ (tConstruct iv_ind 0 []) si_na si_P _ _ iv_False (iv_mkR_ty_typed Γ h)
           (iv_mkR_typed Γ h) (iv_False_typed iv_Σ Γ h)).
Qed.

Lemma iv_wf_Γcf : wf_localE iv_Σ iv_Γcf.
Proof. exact (iv_wf_vass iv_Σ iv_Γc si_na iv_RF sProp iv_wf_Γc (iv_RF_typed iv_Γc iv_wf_Γc) eq_refl). Qed.

Lemma iv_cofix_body_typed : iv_Σ ;;; iv_Γcf |-E iv_cofix_body : lift0 1 iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ iv_Γcf iv_wf_Γcf.
  have wF := iv_wf_vass iv_Σ iv_Γcf iv_fna iv_False sProp iv_wf_Γcf hF eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tRel 1) _ (iv_mkRF_typed iv_Γcf iv_wf_Γcf) _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ iv_Γcf iv_fna iv_False sProp hF eq_refl)|].
    exact (iv_RF_typed _ wF).
  - exact (typeE_Rel _ _ 1 (vass si_na iv_False) iv_wf_Γcf eq_refl).
Qed.

Lemma iv_cofix_guard : cofix_guard iv_Σ iv_Γc iv_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ iv_Γc iv_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma iv_wf_cofix : wf_cofixpointE iv_Σ iv_Γc iv_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_RF. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma iv_cofix_typed : iv_Σ ;;; iv_Γc |-E tCoFix iv_cmfix 0 : iv_RF.
Proof.
  refine (typeE_CoFix _ _ iv_cmfix 0 _ iv_wf_Γc iv_cofix_guard eq_refl _ _ iv_wf_cofix).
  - constructor; [|constructor].
    exact (iv_vass iv_Σ iv_Γc si_na iv_RF sProp (iv_RF_typed iv_Γc iv_wf_Γc) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef iv_Σ iv_Γcf si_na iv_cofix_body (lift0 1 iv_RF) sProp iv_cofix_body_typed
             (iv_RF_typed iv_Γcf iv_wf_Γcf) eq_refl).
Qed.

(** [cofix g … : (λX : Prop. X) (R (∀P:Prop. P))]. *)
Lemma iv_cofix_typed_conv : iv_Σ ;;; iv_Γc |-E tCoFix iv_cmfix 0 : tApp (iv_idS sProp) iv_RF.
Proof.
  exact (iv_retype iv_Σ iv_wfE iv_Γc (tCoFix iv_cmfix 0) iv_RF sProp (iv_RF_typed iv_Γc iv_wf_Γc) iv_cofix_typed).
Qed.

(** The declared type of the first definition of [iv_cmfix] is [R (∀P:Prop. P)], and the type
    [(λX : Prop. X) (R (∀P:Prop. P))] differs from it. *)
Lemma iv_RF_conv_differs :
  (forall d, nth_error iv_cmfix 0 = Some d -> dtype d = iv_RF) /\ tApp (iv_idS sProp) iv_RF <> iv_RF.
Proof. split; [intros d h; injection h as <-; reflexivity|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_RF_conv_differs *)
Definition inversion_CoFixE_inst :=
  inversion_CoFixE iv_Σ iv_wfE (T := tApp (iv_idS sProp) iv_RF) iv_cofix_typed_conv.

(** *** A projection

  In the context [r : R (∀P:Prop. P)], [r.(f) : ∀P:Prop. P]. *)

Definition iv_proj : projection := {| proj_ind := iv_ind; proj_npars := 1; proj_arg := 0 |}.
Definition iv_Γr : context := [vass si_na iv_RF].

Lemma iv_wf_Γr : wf_localE iv_Σ iv_Γr.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_RF sProp localenv_nil (iv_RF_typed [] localenv_nil) eq_refl). Qed.

Lemma iv_declared_projection : declared_projection iv_Σ iv_proj iv_mdecl iv_idecl iv_cdecl iv_pdecl.
Proof. split; [exact iv_declared_constructor|split; reflexivity]. Qed.

Lemma iv_proj_typed : iv_Σ ;;; iv_Γr |-E tProj iv_proj (tRel 0) : iv_False.
Proof.
  exact (typeE_Proj _ _ iv_proj (tRel 0) [] iv_mdecl iv_idecl iv_cdecl iv_pdecl [iv_False]
           iv_declared_projection (typeE_Rel _ _ 0 (vass si_na iv_RF) iv_wf_Γr eq_refl) eq_refl).
Qed.

(** [r.(f) : (λX : Prop. X) (∀P:Prop. P)]. *)
Lemma iv_proj_typed_conv : iv_Σ ;;; iv_Γr |-E tProj iv_proj (tRel 0) : tApp (iv_idS sProp) iv_False.
Proof.
  exact (iv_retype iv_Σ iv_wfE iv_Γr (tProj iv_proj (tRel 0)) iv_False sProp
           (iv_False_typed iv_Σ iv_Γr iv_wf_Γr) iv_proj_typed).
Qed.

(** The type [(λX : Prop. X) (∀P:Prop. P)] is not [∀P:Prop. P]. *)
Lemma iv_False_conv_differs : tApp (iv_idS sProp) iv_False <> iv_False.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_False_conv_differs *)
Definition inversion_ProjE_inst :=
  inversion_ProjE iv_Σ iv_wfE (T := tApp (iv_idS sProp) iv_False) iv_proj_typed_conv.
