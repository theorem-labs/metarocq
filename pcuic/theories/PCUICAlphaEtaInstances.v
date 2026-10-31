(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 19 of 60 instances sampled (seed 202610301905) from the 323 that an earlier focused review had not covered (31.7%, 95% upper bound 42.9%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus two further rows that both reviews had passed and later root rulings reclassified under the same standard (S12, S36). 18 of the 19 sampled misses are corrected at this head (S36 is not yet), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at this head: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count still includes 2 targets whose only NONDEGEN instance is already judged false and not yet corrected: PCUICClassificationEta.wf_fixpoint_spineE and wf_cofixpoint_spineE), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances of these 3 are built and under review, not yet landed); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T02:35Z, 11 NONDEGEN tags are judged false and not yet corrected, all conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are the 2 above. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the later retags, whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations. Prose overclaims were not mechanically enumerated, because that detector failed its controls. Later root rulings reclassified two sampled rows that both reviews had passed, S36 (the red → conv → red class) and S12 (its conclusion is the input's own cumulativity), raising the sampled rate from at least 17 to at least 19 of 60; the 45-row marker census stayed at 2 reopened. *)

(** * Satisfying instances of the lemmas of [PCUICAlphaEta] (row T6)

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]); the derivations are those of
  [PCUICInversionEtaInstances], in particular the typing
  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g ⊢ y : k (λ_:Prop. g _)] ([iv_rel_typed]),
  at a type that is not [y]'s declared type [k g] and η-contracts to it ([al_Γk_eta_nondeg]).

  **The α-variants.** [al_Γk] is [iv_Γk] with the variable [y] named [x] (it is anonymous in
  [iv_Γk]); [al_keta] is [iv_keta] with the binder of [λ_:Prop. g _] named [x]; [al_mfix] is the
  fixpoint [iv_mfix] with its name and both binders named [x]; [al_id] and [al_PP] are [λ_:Prop. _]
  and [Prop → Prop] with the binder named [x]; [al_mp] is the [match] predicate [iv_mp] whose
  context (the one binder of [ind_predicate_context]) is named [x]; [[x : Π x : Prop. Prop]] is
  [[_ : Prop → Prop]] with both names [x]. Each differs syntactically from its original
  ([al_Γk_differs], [al_keta_differs], [al_mfix_differs], [al_PP_differs], [al_id_PP_differ],
  [al_mp_differs], [al_ΓPP_differs]).

  **Every lemma** is applied to these, every premise proved here. [typing_alpha_propE] and its
  corollaries (which use [validityE] of T2a and a copy-18b lemma) are applied in section
  [AlphaClassInstances], whose [Context] held T1's forecast class until copy 18b landed
  (frac/eta 3e6b422d); the class is deleted and no lemma takes one.

  **Non-degeneracy.** Every instance except [cmp_global_instance_empty_eq_inst] and
  [type_Cumul'E_inst] relates two syntactically different terms, contexts or fixpoints (for
  [inst_case_predicate_context_eqE_inst], the two contexts of its premise); the tag at each
  instance names the lemma that states the difference, or the reason. [eq_context_conversionE_inst]
  and [typing_alpha_propE_inst] move the typing [iv_rel_typed] into the renamed context
  ([al_Γk_eta_nondeg] states that its type [k (λ_:Prop. g _)] is not [y]'s declared type [k g] and
  η-contracts to it in one step); they, [isType_eq_context_conversionE_inst] and
  [wf_local_alphaE_inst] are tagged NOT-BUILT: [iv_Γk] and [al_Γk] differ only in a binder name,
  with identical declaration types, so each runs only reflexive per-declaration conversions.
  [type_Cumul'E_inst] is tagged IMPOSSIBLE: its target only repacks
  its own premises with the conversion rule. [wf_local_eq_context_upto_namesE_inst] and
  [lift_judgment_alphaE_inst] relate two different contexts or judgments but are tagged
  IMPOSSIBLE too: the premise of [wf_local_eq_context_upto_namesE] lets only the binder names
  differ, and the premise of [lift_judgment_alphaE] already types every α-variant.
  [eq_context_upto_conv_context_relE_inst] and [upto_names_conv_contextE_inst] relate
  [[_ : Prop → Prop]] and [[x : Π x : Prop. Prop]], whose declared types are themselves different
  α-variants ([al_ΓPP_differs]).
  [inst_case_predicate_context_eqE_inst] relates the two different constructions
  [case_predicate_context] and [inst_case_predicate_context] of the predicate [al_mp], whose
  context is an α-variant of [ind_predicate_context] (the lemma's premise), not the context
  itself ([al_mp_differs]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICClosedBodies PCUICTypingEta PCUICTypingEtaNotions PCUICEtaCanon PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICWsCumulEtaCtx
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     PCUICAlpha PCUICAlphaEta.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

(* The α-variants and the derivations the instances use ([al_univ_inst] is a universe
   instance, not an instance of a lemma).
   WITNESSES: al_* al_univ_inst al_id_PP_differ al_Γk_differs al_Γk_eta_nondeg *)

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** The α-variants, without any class *)

Definition al_xna : aname := mkBindAnn (nNamed "x") Relevant.
Definition al_Γk : context := [vass al_xna (tApp (tRel 0) (tRel 1)); vass si_na iv_K; vass si_na iv_PP].
Definition al_eta_g : term := tLambda al_xna si_P (tApp (tRel 3) (tRel 0)).
Definition al_keta : term := tApp (tRel 1) al_eta_g.
Definition al_id : term := tLambda al_xna si_P (tRel 0).
Definition al_PP : term := tProd al_xna si_P si_P.
Definition al_fix_ty : term := tProd al_xna iv_IF iv_IF.
Definition al_mfix : mfixpoint term :=
  [{| dname := al_xna; dtype := al_fix_ty; dbody := tLambda al_xna iv_IF (tRel 0); rarg := 0 |}].

Lemma al_Γk_differs : iv_Γk <> al_Γk.
Proof. discriminate. Qed.

Lemma al_keta_differs : iv_keta <> al_keta.
Proof. discriminate. Qed.

Lemma al_mfix_differs : iv_mfix <> al_mfix.
Proof. discriminate. Qed.

Lemma al_PP_differs : iv_PP <> al_PP.
Proof. discriminate. Qed.

Lemma al_id_PP_differ : iv_id <> al_id /\ iv_PP <> al_PP.
Proof. split; discriminate. Qed.

Lemma al_Γk_keta_differ : iv_Γk <> al_Γk /\ iv_keta <> al_keta.
Proof. split; discriminate. Qed.

(** The typing [y : k (λ_:Prop. g _)] ([iv_rel_typed]) that [eq_context_conversionE_inst] and
    [typing_alpha_propE_inst] move: [al_Γk] differs from [iv_Γk]; in both, [y] ([tRel 0]) is
    declared at [k g] ([iv_kg] after the lift); the type [k (λ_:Prop. g _)] is not [k g] and
    η-contracts to it in one step. *)
Lemma al_Γk_eta_nondeg :
  iv_Γk <> al_Γk /\
  option_map (fun d => lift0 1 (decl_type d)) (nth_error iv_Γk 0) = Some iv_kg /\
  option_map (fun d => lift0 1 (decl_type d)) (nth_error al_Γk 0) = Some iv_kg /\
  iv_keta <> iv_kg /\ ∥ PCUICEtaDefs.eta1 iv_keta iv_kg ∥.
Proof.
  split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
  split; [discriminate|]. constructor.
  exact (PCUICEtaDefs.app_eta_r _ _ (tRel 1) (PCUICEtaDefs.eta_red si_na (tRel 2) si_P)).
Qed.

Lemma al_Γk_alpha : iv_Γk ≡Γ al_Γk.
Proof. constructor; [reflexivity|]. constructor; [exact eq_refl|reflexivity]. Qed.

Lemma al_Γk_names : eq_context_upto_names al_Γk iv_Γk.
Proof. constructor; [|reflexivity]. constructor. exact eq_refl. Qed.

Lemma al_keta_alpha : iv_keta ≡' al_keta.
Proof. constructor; [constructor|]. constructor; [exact eq_refl|reflexivity|reflexivity]. Qed.

Lemma al_PP_alpha : iv_PP ≡α al_PP.
Proof. constructor; [exact eq_refl|reflexivity|reflexivity]. Qed.

(** The one-declaration contexts [[_ : Prop → Prop]] and [[x : Π x : Prop. Prop]]: the names and the
    declared types differ, the types being α-variants. *)
Lemma al_ΓPP_alpha : [vass si_na iv_PP] ≡Γ [vass al_xna al_PP].
Proof.
  constructor; [reflexivity|]. constructor; [exact eq_refl|].
  constructor; [exact eq_refl|reflexivity|reflexivity].
Qed.

Lemma al_ΓPP_differs : [vass si_na iv_PP] <> [vass al_xna al_PP] /\ iv_PP <> al_PP.
Proof. split; discriminate. Qed.

Lemma al_mfix_alpha : eq_mfixpoint upto_names' iv_mfix al_mfix.
Proof.
  constructor; [|constructor]. cbn.
  split; [constructor; [exact eq_refl|reflexivity|reflexivity]|].
  split; [constructor; [exact eq_refl|reflexivity|reflexivity]|].
  split; reflexivity.
Qed.

(** The [match] predicate [iv_mp] with the binder of its context named [x]: its context is an
    α-variant of [ind_predicate_context si_ind si_mdecl si_idecl] (the context of [iv_mp]). *)
Definition al_mp : predicate term :=
  {| pparams := [tRel 0]; puinst := []; pcontext := [vass al_xna (iv_Ix 0)]; preturn := iv_Ix 1 |}.

Lemma al_mp_differs : pcontext al_mp <> ind_predicate_context si_ind si_mdecl si_idecl.
Proof. vm_compute. discriminate. Qed.

Lemma al_wf_mp : wf_predicate si_mdecl si_idecl al_mp.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma al_mp_names : eq_context_upto_names (ind_predicate_context si_ind si_mdecl si_idecl) (pcontext al_mp).
Proof. cbn. constructor; [constructor; reflexivity|constructor]. Qed.

(** ** The other lemmas, applied *)

(** The two-level universe instance [[a; Set]]. *)
Definition al_univ_inst : Instance.t := [Level.level "a"; Level.lzero].

Lemma al_univ_inst_cmp :
  cmp_global_instance empty_global_env (fun _ => eq) Conv (IndRef si_ind) 1 al_univ_inst al_univ_inst.
Proof. unfold al_univ_inst. cbn. repeat constructor. Qed.

(** Run at the two-level instance [[a; Set]] ([al_univ_inst]), an inductive reference applied
    to one argument, so the premise is proved level by level (not by the empty comparison) and
    the lemma's proof inverts it at each level.
    INSTANCE IMPOSSIBLE: the conclusion is u = u' and its one premise forces u and u' to be the same instance: in the fixed environment empty_global_env every lookup_env is None, so global_variance_gen is AllEqual at every reference gr and every napp, and the premise is cmp_universe_instance (fun _ => eq) u u', the pointwise equality of u and u'. *)
Definition cmp_global_instance_empty_eq_inst : al_univ_inst = al_univ_inst :=
  cmp_global_instance_empty_eq Conv (IndRef si_ind) 1 al_univ_inst al_univ_inst al_univ_inst_cmp.

(** INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_keta_differs *)
Definition eq_term_upto_names_upto_domain_r_inst : upto_domain_r iv_keta al_keta :=
  eq_term_upto_names_upto_domain_r Conv 0 iv_keta al_keta al_keta_alpha.

(** [canon] of two syntactically different α-variants.
    INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_keta_differs *)
Definition upto_names_canon_eq_inst : canon iv_keta = canon al_keta :=
  upto_names_canon_eq iv_keta al_keta al_keta_alpha.

(** [k (λ_:Prop. g _)] and [k (λx:Prop. g x)] joined in [iv_Γk].
    INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_keta_differs *)
Definition upto_names_JoinE_inst : JoinE si_Σ iv_Γk Cumul iv_keta al_keta :=
  upto_names_JoinE si_Σ iv_Γk Cumul iv_keta al_keta al_keta_alpha.

(** The conversion witness of [iv_mfix] transported to the renamed fixpoint.
    INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_mfix_differs *)
Lemma upto_names_mfix_on_indE_inst :
  mfix_on_ind check_one_fix (conv_witnessE si_Σ []) (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) al_mfix.
Proof.
  refine (upto_names_mfix_on_indE (Σ := si_Σ) (wfΣ := si_wfE) [] check_one_fix _ iv_mfix al_mfix
            rarg_check_one_fix eq_refl _ al_mfix_alpha iv_wf_fix.2.2).
  constructor; [reflexivity|constructor].
Qed.

(** [[_ : Prop → Prop]] against [[x : Π x : Prop. Prop]]: the declared types are different
    α-variants ([al_ΓPP_differs]).
    INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_ΓPP_differs *)
Definition eq_context_upto_conv_context_relE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] [vass si_na iv_PP] [vass al_xna al_PP] :=
  eq_context_upto_conv_context_relE (Σ := si_Σ) (wfΣ := si_wfE) [] [vass si_na iv_PP] [vass al_xna al_PP]
    eq_refl eq_refl al_ΓPP_alpha.

(** The predicate context [x : I A] of [al_mp] against the context [I : I A] of the inductive.
    INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_mp_differs *)
Definition inst_case_predicate_context_eqE_inst :
  eq_context_upto_names (case_predicate_context si_ind si_mdecl si_idecl al_mp) (inst_case_predicate_context al_mp) :=
  inst_case_predicate_context_eqE (Σ := si_Σ) (wfΣ := si_wfE) (ind := si_ind) (mdecl := si_mdecl)
    (idecl := si_idecl) (p := al_mp) al_wf_mp al_mp_names.

(** INSTANCE IMPOSSIBLE: the premise [eq_context_upto_names Δ' Δ] ([All2] of [eq_decl_upto_names], [PCUICEquality]) gives each declaration of [Δ'] the type and body of the matching declaration of [Δ], and only the binder name may differ; so in every instance and environment the proof of [wf_local_eq_context_upto_namesE] transports the premise's typings along a context conversion ([eq_context_upto_conv_context_relE]) whose every per-declaration step is reflexive, and the conclusion is the premise's own typings under renamed binders (the class of [PCUICSREtaConvInstances.eq_context_alpha_convE_inst]) *)
Definition wf_local_eq_context_upto_namesE_inst : wf_localE si_Σ ([] ,,, al_Γk) :=
  wf_local_eq_context_upto_namesE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := iv_Γk) iv_wf_Γk al_Γk_names.

Definition al_wf_Γk : wf_localE si_Σ al_Γk := wf_local_eq_context_upto_namesE_inst.

(** The typing [y : k (λ_:Prop. g _)] ([iv_rel_typed]) moved into the renamed context [al_Γk]:
    [y] is declared at [k g] in both contexts, and [k (λ_:Prop. g _)] is not [k g] and
    η-contracts to it in one step ([al_Γk_eta_nondeg]).
    INSTANCE NOT-BUILT: degenerate, runs on [iv_Γk ≡Γ al_Γk], two contexts that differ only in the first binder name with identical declaration types ([al_Γk_alpha] proves each type part by reflexivity), so every per-declaration conversion of [eq_context_conversionE] relates a type to itself and the conclusion is the input typing [iv_rel_typed] re-indexed by a renaming; non-degenerate instances exist on contexts with α-different declaration types (as [al_ΓPP_differs]); no non-degenerate witness built yet *)
Definition eq_context_conversionE_inst : si_Σ ;;; al_Γk |-E tRel 0 : iv_keta :=
  eq_context_conversionE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γk) (Δ := al_Γk) iv_rel_typed al_Γk_alpha al_wf_Γk.

(** The same two contexts, joined declaration by declaration ([al_ΓPP_differs]).
    INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_ΓPP_differs *)
Definition upto_names_conv_contextE_inst : conv_context (@JoinE _) si_Σ [vass si_na iv_PP] [vass al_xna al_PP] :=
  upto_names_conv_contextE si_Σ [vass si_na iv_PP] [vass al_xna al_PP] al_ΓPP_alpha.

Definition al_keta_isType : isTypeE si_Σ iv_Γk iv_keta := has_sort_isTypeE _ iv_keta_typed.

(** INSTANCE NOT-BUILT: degenerate, runs on [iv_Γk ≡Γ al_Γk], two contexts that differ only in the first binder name with identical declaration types ([al_Γk_alpha] proves each type part by reflexivity), so every per-declaration conversion of [isType_eq_context_conversionE] relates a type to itself and the conclusion is the input [al_keta_isType] re-indexed by a renaming; non-degenerate instances exist on contexts with α-different declaration types (as [al_ΓPP_differs]); no non-degenerate witness built yet *)
Definition isType_eq_context_conversionE_inst : isTypeE si_Σ al_Γk iv_keta :=
  isType_eq_context_conversionE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γk) (Δ := al_Γk) al_keta_isType al_Γk_alpha
    al_wf_Γk.

(** Inversion of [upto_names] at the concrete terms below: a sort has only itself as α-variant. *)
Ltac al_inv :=
  repeat match goal with
  | H : eq_term_upto_univ_napp _ _ _ _ _ (tSort _) _ |- _ => depelim H
  | H : eq_term_upto_univ_napp _ _ _ _ _ (tRel _) _ |- _ => depelim H
  end; cbn in *; subst.

(** Every α-variant of [Prop → Prop] is a type, and every α-variant of [λ_:Prop. _] has type
    [Prop → Prop]: the premise of [lift_judgment_alphaE], proved by inversion of [upto_names]. *)
Lemma al_PP_variants Γ : wf_localE si_Σ Γ ->
  forall u, upto_names' iv_PP u -> si_Σ ;;; Γ |-E u : tSort iv_sPP.
Proof.
  intros h u e. unfold iv_PP in e. depelim e. unfold si_P in *. al_inv.
  match goal with H : eq_binder_annot _ _ |- _ => rename H into hna end.
  refine (typeE_Prod _ _ na' si_P si_P (Sort.super sProp) (Sort.super sProp) _ _).
  - exact (iv_vass_s si_Σ Γ na' si_P _ (iv_P_typed si_Σ Γ h) hna).
  - exact (iv_P_typed si_Σ _ (iv_wf_vass si_Σ Γ na' si_P _ h (iv_P_typed si_Σ Γ h) hna)).
Qed.

Lemma al_id_variants Γ : wf_localE si_Σ Γ ->
  forall u, upto_names' iv_id u -> si_Σ ;;; Γ |-E u : iv_PP.
Proof.
  intros h u e. unfold iv_id in e. depelim e. unfold si_P in *. al_inv.
  match goal with H : eq_binder_annot _ _ |- _ => rename H into hna end.
  have w := iv_wf_vass si_Σ Γ na' si_P _ h (iv_P_typed si_Σ Γ h) hna.
  eapply typeE_Cumul with (A := tProd na' si_P si_P).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ Γ na' si_P _ (iv_P_typed si_Σ Γ h) hna).
    + exact (typeE_Rel _ _ 0 (vass na' si_P) w eq_refl).
  - exact (iv_PP_typed si_Σ Γ h).
  - apply eq_term_upto_univ_cumulSpecE. constructor; [exact (eq_sym hna)|reflexivity|reflexivity].
Qed.

(** The judgment [λ_:Prop. _ : Prop → Prop] moved to its α-variant [λx:Prop. _ : Π x : Prop. Prop].
    INSTANCE IMPOSSIBLE: the premise already types every α-variant (its functions take each [u] with [upto_names' t u] to a typing of [u]); the proof of [lift_judgment_alphaE] applies them at [tm'] and [t'] through the generic [lift_sorting_it_impl_gen], then moves the term's type from [t] to its α-variant [t'] by [type_Cumul'E] (tagged IMPOSSIBLE in this file) and the α-to-cumulativity embedding [eq_term_upto_univ_cumulSpecE]; so in every instance and environment the conclusion is the premise instantiated at [tm'] and [t'] and repacked *)
Lemma lift_judgment_alphaE_inst : lift_typing typingE si_Σ [] (Judge (Some al_id) al_PP None None).
Proof.
  eapply (lift_judgment_alphaE (tm := Some iv_id) (t := iv_PP)).
  - split; [exact (al_id_variants [] localenv_nil)|].
    exists iv_sPP. split; [exact (al_PP_variants [] localenv_nil)|]. split; exact I.
  - cbn. constructor; [exact eq_refl|reflexivity|reflexivity].
  - exact al_PP_alpha.
Qed.

(** [y : k g] retyped at [k (λ_:Prop. g _)] through the cumulativity premise [iv_spec_eta].
    INSTANCE IMPOSSIBLE: the target's proof only unpacks and repacks its own premises: it projects the sort s out of the isTypeE premise and applies the conversion constructor typeE_Cumul to the typing premise, that sort derivation and the cumulativity premise (PCUICAlphaEta.v:171-178), so in every environment, context and instance the conclusion t : T' is assembled from the instance's own premises by one constructor, and no instance exercises more. *)
Definition type_Cumul'E_inst : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta :=
  PCUICAlphaEta.type_Cumul'E iv_kg iv_y_typed al_keta_isType iv_spec_eta.

Lemma al_PP_isWfArity : isWfArityE si_Σ [] iv_PP.
Proof.
  split; [exact (has_sort_isTypeE _ (iv_PP_typed si_Σ [] localenv_nil))|].
  exists [vass si_na si_P], sProp. reflexivity.
Qed.

(** ** The main theorem's family (it took T1's forecast class until copy 18b landed) *)

Section AlphaClassInstances.

  (** The same typing as [eq_context_conversionE_inst], through the main theorem's typing
      component, into the renamed context ([al_Γk_eta_nondeg]).
      INSTANCE NOT-BUILT: degenerate, runs on [iv_Γk ≡Γ al_Γk], two contexts that differ only in the first binder name with identical declaration types ([al_Γk_alpha] proves each type part by reflexivity), and the term is unchanged ([u = v = tRel 0]), so every per-declaration conversion relates a type to itself and the conclusion is the input typing [iv_rel_typed] re-indexed by a renaming; non-degenerate instances exist on contexts with α-different declaration types (as [al_ΓPP_differs]); no non-degenerate witness built yet *)
  Definition typing_alpha_propE_inst : si_Σ ;;; al_Γk |-E tRel 0 : iv_keta :=
    (typing_alpha_propE si_Σ si_wfE iv_Γk (tRel 0) iv_keta iv_rel_typed).2.2 al_Γk (tRel 0)
      ltac:(reflexivity) al_Γk_alpha.

  (** INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_keta_differs *)
  Definition typing_alphaE_inst : si_Σ ;;; iv_Γk |-E al_keta : si_P :=
    typing_alphaE (Σ := si_Σ) (wfΣ := si_wfE) (u := iv_keta) (v := al_keta) iv_keta_typed al_keta_alpha.

  (** INSTANCE NOT-BUILT: degenerate, runs on [iv_Γk ≡Γ al_Γk], two contexts that differ only in the first binder name with identical declaration types ([al_Γk_alpha] proves each type part by reflexivity), so every per-declaration conversion of [PCUICAlphaEta.wf_local_alphaE] relates a type to itself and the conclusion is the input [iv_wf_Γk] re-indexed by a renaming; non-degenerate instances exist on contexts with α-different declaration types (as [al_ΓPP_differs]); no non-degenerate witness built yet
      TARGET PCUICAlphaEta.wf_local_alphaE *)
  Definition wf_local_alphaE_inst : wf_localE si_Σ al_Γk :=
    PCUICAlphaEta.wf_local_alphaE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γk) (Γ' := al_Γk) iv_wf_Γk al_Γk_alpha.

  (** INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_keta_differs *)
  Definition isType_alphaE_inst : isTypeE si_Σ iv_Γk al_keta :=
    isType_alphaE (Σ := si_Σ) (wfΣ := si_wfE) iv_Γk iv_keta al_keta al_keta_isType al_keta_alpha.

  (** Both the context and the type change.
      INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_Γk_keta_differ *)
  Definition isType_alpha_ctxE_inst : isTypeE si_Σ al_Γk al_keta :=
    isType_alpha_ctxE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γk) (Δ := al_Γk) (u := iv_keta) (v := al_keta)
      al_keta_isType al_Γk_alpha al_keta_alpha.

  (** INSTANCE NONDEGEN PCUICAlphaEtaInstances.al_PP_differs *)
  Definition isWfArity_alphaE_inst : isWfArityE si_Σ [] al_PP :=
    isWfArity_alphaE (Σ := si_Σ) (wfΣ := si_wfE) (u := iv_PP) (v := al_PP) al_PP_isWfArity al_PP_alpha.

End AlphaClassInstances.
