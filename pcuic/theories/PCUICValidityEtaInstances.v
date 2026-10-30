(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: 10 of 60 sampled instances (residual 16.7%, 95% upper bound 26.6%), seed 202610301905, measured on the pre-retag head; H' additionally corrects 10 tags and 7 prose rows that review found false, so the figure is conservative here. *)

(** * Satisfying instances of the lemmas of [PCUICValidityEta], and the two T2a contracts

  **The contracts.** The two fields of the checker's [T2a_facts]
  ([safechecker/theories/PCUICTypingEtaHyps.v], branch [wip/etak-k7-2026-10-29] @ [0bbee83d]) and
  the two fields of [SRForecastT2a], the class [PCUICSREta.v] declared before it imported this
  lemma file (be252347 removed the class; [PCUICSREta.v] now uses [validityE] and
  [inversion_mkAppsE] directly), are copied here and inhabited by [validityE] and
  [inversion_mkAppsE]: [T2a_inversion_mkApps_fit], [T2a_validity_fit], [SR_T2a_validityE_fit],
  [SR_T2a_inversion_mkAppsE_fit]. Each copy is its text with one change: [typing_spineE] is written
  [PCUICAritiesEta.typing_spineE], the [PCUICArities] spine the texts mean ([PCUICGenerationEta]
  declares another [typing_spineE]).

  **The instances.** Each lemma family of [PCUICValidityEta] with a premise has an instance below,
  in [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]: [Inductive I (A : Prop) : Prop := c : I A]),
  in [iv_Σ] ([PCUICInversionEtaInstances]: a coinductive record with one projection), or in the
  environments of [PCUICTypingEtaCopies2Instances]: the empty [e0_env] and [up_env], which holds one
  universe-polymorphic axiom [T@{l0} : Type@{l0}] (universe context [up_univs]). Every instance
  APPLIES its lemma to concrete premises, each proved, using the derivations of
  [PCUICInversionEtaInstances] and [PCUICTypingEtaCopies2Instances]. The six lemmas that needed a
  forecast class before copy 16 landed (frac/eta 0fb43f10: [validity_envE], [validityE],
  [inversion_mkAppsE], [type_App'E], [type_mkApps_arityE], [declared_projection_typeE], now copy
  16's) keep the statement shape of their instance: the premises and the conclusion at concrete
  arguments, the conclusion now given by the lemma.
  The universe and environment lemmas are applied where they do work: [isType_weaken_fullE] and
  [isType_extendsE] go from [e0_env] to [up_env], an extension
  ([PCUICTypingEtaCopies2Instances.e0_up_extends]) whose declarations differ from those of
  [e0_env] ([vi_up_adds_decl]); [isWfArity_subst_instance_declE] instantiates the universe
  context of [T] at [l0 := Set], which changes both the context and the arity
  ([vi_up_inst_changes_ctx]). [isType_Sort_invE] is tagged IMPOSSIBLE at its instance: every
  derivation of [Γ ⊢E tSort s : T] stores [wf_sort Σ s], and the lemma returns it. Its instance
  runs on [vi_s0_cumul_typed], a typing of [Type@{l0}] built by [typeE_Cumul] over [up_s0_typed].
  The copy lemmas of copies 10, 12, 14 and 16 that [PCUICValidityEta] proved before those copies
  landed are gone from it; their instances are in [PCUICTypingEtaCopies2Instances] and
  [PCUICTypingEtaCopy16Instances].
  [validityE] and [validity_envE] run on [c (∀P:Prop. P) : (I A){0 := ∀P:Prop. P}]
  ([PCUICInversionEtaInstances.iv_cF_typed]), whose type the substitution changes
  ([PCUICInversionEtaInstances.iv_cF_codomain_moves]); [type_App'E] builds that judgment.
  [inversion_mkAppsE] runs on the same application typed at [(λX : Prop. X) (I (∀P:Prop. P))]
  ([PCUICInversionEtaInstances.iv_cF_typed_conv]): its spine [[∀P:Prop. P]] is not empty, and
  that type is not [I (∀P:Prop. P)] ([vi_mkApps_spine_nondeg]). Each instance carries its tag
  (instance-gate grammar).

  WITNESSES: T2a_* SR_T2a_* vi_IF_isType0 up_s0_typed_e0 up_s0_isType_e0 vi_s2_typed vi_s1_cumul_s2 vi_s0_cumul_typed
  ([T2a_*], [SR_T2a_*]: the contract fits above, generic in [Σ], not instances; the others: typing
  pieces the instances use) *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICArities PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICWfUniversesEta PCUICWsCumulEtaCtxTyp
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICInductivesEta
     PCUICValidityEta.
From MetaRocq.PCUIC Require PCUICTypingEtaCopies2Instances.

Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.

(** ** The T2a contracts, inhabited by the E lemmas *)

Section ContractFit.

  (** The checker's [T2a_facts] (its section variable [{cf : checker_flags}] made a [Context]). *)
  Section Checker.
    Context {cf : checker_flags}.

    Definition T2a_inversion_mkApps_fit :
      forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-E mkApps f u : T -> ∑ A : term, Σ;;; Γ |-E f : A × PCUICAritiesEta.typing_spineE Σ Γ A u T
      := fun Σ wfΣ Γ f u T h => inversion_mkAppsE (wfΣ := wfΣ) h.

    Definition T2a_validity_fit :
      forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ T
      := fun Σ wfΣ Γ t T h => validityE (wfΣ := wfΣ) h.
  End Checker.

  (** The two fields of [SRForecastT2a], the class [PCUICSREta.v] declared before be252347. *)
  Definition SR_T2a_validityE_fit :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T},
    Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T
    := fun cf Σ wfΣ Γ t T h => validityE (wfΣ := wfΣ) h.

  Definition SR_T2a_inversion_mkAppsE_fit :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ f u T},
    Σ ;;; Γ |-E mkApps f u : T ->
    ∑ A, Σ ;;; Γ |-E f : A × PCUICAritiesEta.typing_spineE Σ Γ A u T
    := fun cf Σ wfΣ Γ f u T h => inversion_mkAppsE (wfΣ := wfΣ) h.

End ContractFit.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** The universe and environment lemmas *)

(** [isType_weaken_fullE], [isType_extendsE]: [up_env] extends the empty [e0_env] by the declaration
    of [T] ([PCUICTypingEtaCopies2Instances.e0_up_extends]). The premise types [Type@{l0}], at the
    bound level [l0] of [up_univs], over [e0_env]; the conclusion is that judgment over [up_env]. *)
Lemma up_s0_typed_e0 :
  PCUICTypingEtaCopies2Instances.up_Σ0 ;;; [] |-E tSort PCUICTypingEtaCopies2Instances.up_s0
    : tSort (Sort.super PCUICTypingEtaCopies2Instances.up_s0).
Proof. apply typeE_Sort; [constructor|exact PCUICTypingEtaCopies2Instances.up_wf_sort0]. Qed.

Definition up_s0_isType_e0 :
  isTypeE PCUICTypingEtaCopies2Instances.up_Σ0 [] (tSort PCUICTypingEtaCopies2Instances.up_s0) :=
  has_sort_isTypeE _ up_s0_typed_e0.

(** The extension is strict: [up_env] has a declaration that [e0_env] has not. *)
Lemma vi_up_adds_decl :
  declarations PCUICTypingEtaCopies2Instances.e0_env <> declarations PCUICTypingEtaCopies2Instances.up_env.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICValidityEtaInstances.vi_up_adds_decl *)
Definition isType_weaken_fullE_inst :
  isTypeE (PCUICTypingEtaCopies2Instances.up_env, PCUICTypingEtaCopies2Instances.up_univs) []
    (tSort PCUICTypingEtaCopies2Instances.up_s0) :=
  isType_weaken_fullE PCUICTypingEtaCopies2Instances.up_Σ0 PCUICTypingEtaCopies2Instances.up_env
    PCUICTypingEtaCopies2Instances.e0_wfE PCUICTypingEtaCopies2Instances.up_wfE
    PCUICTypingEtaCopies2Instances.e0_up_extends [] (tSort PCUICTypingEtaCopies2Instances.up_s0)
    (tSort PCUICTypingEtaCopies2Instances.up_s0) up_s0_isType_e0.

(* INSTANCE NONDEGEN PCUICValidityEtaInstances.vi_up_adds_decl *)
Definition isType_extendsE_inst :
  isTypeE (PCUICTypingEtaCopies2Instances.up_env, PCUICTypingEtaCopies2Instances.up_univs) []
    (tSort PCUICTypingEtaCopies2Instances.up_s0) :=
  isType_extendsE PCUICTypingEtaCopies2Instances.e0_env PCUICTypingEtaCopies2Instances.up_env
    PCUICTypingEtaCopies2Instances.up_univs PCUICTypingEtaCopies2Instances.e0_wfE
    PCUICTypingEtaCopies2Instances.up_wfE PCUICTypingEtaCopies2Instances.e0_up_extends []
    (tSort PCUICTypingEtaCopies2Instances.up_s0) up_s0_isType_e0.

(** [Type@{l0+2} : Type@{l0+3}] in [(up_env, up_univs)]. *)
Lemma vi_s2_typed :
  PCUICTypingEtaCopies2Instances.up_Σp ;;; []
    |-E tSort (Sort.super (Sort.super PCUICTypingEtaCopies2Instances.up_s0))
    : tSort (Sort.super (Sort.super (Sort.super PCUICTypingEtaCopies2Instances.up_s0))).
Proof.
  apply typeE_Sort; [constructor|].
  exact (PCUICWfUniverses.wf_sort_super
           (PCUICWfUniverses.wf_sort_super PCUICTypingEtaCopies2Instances.up_wf_sort_p)).
Qed.

(** [Type@{l0+1} ≤ Type@{l0+2}] in [(up_env, up_univs)]. *)
Lemma vi_s1_cumul_s2 :
  cumulSpecE PCUICTypingEtaCopies2Instances.up_Σp []
    (tSort (Sort.super PCUICTypingEtaCopies2Instances.up_s0))
    (tSort (Sort.super (Sort.super PCUICTypingEtaCopies2Instances.up_s0))).
Proof.
  apply cumulE_Sort.
  change (leq0_universe_n 0 (global_ext_constraints PCUICTypingEtaCopies2Instances.up_Σp)
            (Universe.succ (Universe.make' (Level.lvar 0)))
            (Universe.succ (Universe.succ (Universe.make' (Level.lvar 0))))).
  intros v _. rewrite !val_map_succ. lia.
Qed.

(** [Type@{l0} : Type@{l0+2}], by [typeE_Cumul] from [up_s0_typed] ([Type@{l0} : Type@{l0+1}]). *)
Definition vi_s0_cumul_typed :
  PCUICTypingEtaCopies2Instances.up_Σp ;;; [] |-E tSort PCUICTypingEtaCopies2Instances.up_s0
    : tSort (Sort.super (Sort.super PCUICTypingEtaCopies2Instances.up_s0)) :=
  typeE_Cumul _ _ (tSort PCUICTypingEtaCopies2Instances.up_s0)
    (tSort (Sort.super PCUICTypingEtaCopies2Instances.up_s0))
    (tSort (Sort.super (Sort.super PCUICTypingEtaCopies2Instances.up_s0)))
    (Sort.super (Sort.super (Sort.super PCUICTypingEtaCopies2Instances.up_s0)))
    PCUICTypingEtaCopies2Instances.up_s0_typed vi_s2_typed vi_s1_cumul_s2.

(** [isType_Sort_invE] at [Type@{l0}] in [(up_env, up_univs)], on the typing [vi_s0_cumul_typed],
    built by [typeE_Cumul] over [up_s0_typed].
    INSTANCE IMPOSSIBLE: every derivation of [Γ ⊢E tSort s : T] is [typeE_Sort] under [typeE_Cumul] steps (no other typing rule concludes a judgment with the subject [tSort s]), and [typeE_Sort] stores [wf_sort Σ s] as a premise; [inversion_SortE] passes that premise through and [isType_Sort_invE] returns it, so in every instance and environment the conclusion is part of the premise. *)
Definition isType_Sort_invE_inst :
  wf_sort PCUICTypingEtaCopies2Instances.up_Σp PCUICTypingEtaCopies2Instances.up_s0 :=
  isType_Sort_invE (Σ := PCUICTypingEtaCopies2Instances.up_Σp) (s := PCUICTypingEtaCopies2Instances.up_s0)
    PCUICTypingEtaCopies2Instances.up_wfE
    (has_sort_isTypeE _ vi_s0_cumul_typed).

(** The instantiation [l0 := Set] changes the context [x : Type@{l0}] and the arity
    [Type@{l0}]. *)
Lemma vi_up_inst_changes_ctx :
  subst_instance [Level.lzero] PCUICTypingEtaCopies2Instances.up_Γ <> PCUICTypingEtaCopies2Instances.up_Γ /\
  subst_instance [Level.lzero] (tSort PCUICTypingEtaCopies2Instances.up_s0)
    <> tSort PCUICTypingEtaCopies2Instances.up_s0.
Proof. split; discriminate. Qed.

(** [isWfArity_subst_instance_declE] at the universe-polymorphic axiom [T] of [up_env]: the arity
    [Type@{l0}] in the context [x : Type@{l0}], instantiated at [l0 := Set]
    ([PCUICTypingEtaCopies2Instances.up_cu]), which changes both the context and the arity.
    INSTANCE NONDEGEN PCUICValidityEtaInstances.vi_up_inst_changes_ctx *)
Lemma isWfArity_subst_instance_declE_inst :
  isWfArityE PCUICTypingEtaCopies2Instances.up_Σm
    (subst_instance [Level.lzero] PCUICTypingEtaCopies2Instances.up_Γ)
    (subst_instance [Level.lzero] (tSort PCUICTypingEtaCopies2Instances.up_s0)).
Proof.
  refine (isWfArity_subst_instance_declE (Σ := PCUICTypingEtaCopies2Instances.up_Σm)
            (Γ := PCUICTypingEtaCopies2Instances.up_Γ) (T := tSort PCUICTypingEtaCopies2Instances.up_s0)
            (c := PCUICTypingEtaCopies2Instances.up_kn)
            (decl := ConstantDecl PCUICTypingEtaCopies2Instances.up_cb) (u := [Level.lzero])
            PCUICTypingEtaCopies2Instances.up_wfE PCUICTypingEtaCopies2Instances.up_lookup _
            PCUICTypingEtaCopies2Instances.up_cu).
  split.
  - apply (has_sort_isTypeE (Sort.super PCUICTypingEtaCopies2Instances.up_s0)).
    apply typeE_Sort; [exact PCUICTypingEtaCopies2Instances.up_wf_Γ
                      |exact PCUICTypingEtaCopies2Instances.up_wf_sort_p].
  - exists [], PCUICTypingEtaCopies2Instances.up_s0. reflexivity.
Qed.

(** ** Contexts and judgments *)

(** [I (∀P:Prop. P)] is a type in the empty context ([iv_IF_typed]: an application of [I]). *)
Lemma vi_IF_isType0 : isTypeE si_Σ [] iv_IF.
Proof. exact (has_sort_isTypeE sProp (iv_IF_typed [] localenv_nil)). Qed.

(** The context [iv_Γk] the closed type is weakened into is not empty, and the weakened type
    [I (∀P:Prop. P)] is not a sort. *)
Lemma isType_weakeningE_inst_nondeg : iv_Γk <> [] /\ (forall s, iv_IF <> tSort s).
Proof. split; [discriminate|intros s; discriminate]. Qed.

(** [isType_weakeningE] at [I (∀P:Prop. P)], from its typing in [[]] ([vi_IF_isType0]), weakened
    into [iv_Γk]; [iv_Γk] is not empty and [I (∀P:Prop. P)] is not a sort.
    INSTANCE NONDEGEN PCUICValidityEtaInstances.isType_weakeningE_inst_nondeg *)
Definition isType_weakeningE_inst : isTypeE si_Σ iv_Γk iv_IF :=
  isType_weakeningE (Σ := si_Σ) (Γ := iv_Γk) (T := iv_IF) si_wfE iv_wf_Γk vi_IF_isType0.

(** [type_ctx_wf_univE] on the one-declaration context [x : Prop] at [Type₁].
    INSTANCE IMPOSSIBLE: the proof of [type_ctx_wf_univE] is an induction on [Δ] that only takes the first component of its premise at each declaration ([intros [h _]; auto]) until the empty context, where [type_local_ctx] is [wf_sort Σ s] itself; so in every instance and environment the conclusion is a piece of the premise, unpacked. *)
Lemma type_ctx_wf_univE_inst : wf_sort si_Σ (Sort.super sProp).
Proof.
  apply (type_ctx_wf_univE si_Σ [] [vass si_na si_P] (Sort.super sProp)).
  split; [exact (typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil))|].
  exact (iv_vass_s si_Σ [] si_na si_P (Sort.super sProp) (iv_P_typed si_Σ [] localenv_nil) eq_refl).
Qed.

(** The relative context [k : (Prop → Prop) → Prop, y : k g] is not closed: [closed_ctx] is [false]
    on it, because the [g] of [k g], [tRel 1] under the one declaration [k], is free in it. It is
    the part of [iv_Γk] above [iv_Γg] (by the definitions of [iv_Γk] and [iv_Γg]); in [iv_Γk], that
    [tRel 1] is the declaration [g : Prop → Prop] of [iv_Γg]. *)
Lemma vi_rel_ctx_open : closed_ctx [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K] = false.
Proof. reflexivity. Qed.

(* INSTANCE IMPOSSIBLE: the proof of [validity_wf_localE] is an induction on its [All_local_rel] premise that, at each assumption, takes the sort the premise's own judgment stores ([lift_sorting_extract], a record repack that copies that sort into the judgment) and conses it onto the list, and at each let reuses the premise's judgment; so in every instance and environment the sort list and each judgment of the conclusion are the premise's own fields, repacked. *)
Definition validity_wf_localE_inst :=
  validity_wf_localE (Σ := si_Σ) iv_Γg [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K]
    (All_local_env_app_inv (Γ := iv_Γg) (Γ' := [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K])
       iv_wf_Γk).2.

(* INSTANCE NONDEGEN PCUICValidityEtaInstances.vi_rel_ctx_open *)
Definition wf_local_validityE_inst :=
  wf_local_validityE (Σ := si_Σ) (wfΣ := si_wfE) iv_Γg [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K]
    iv_wf_Γk.

(** ** The six lemmas of copy 16, applied *)

(** [validityE] at [c (∀P:Prop. P) : (I A){0 := ∀P:Prop. P}].
    INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_cF_codomain_moves *)
Lemma validityE_inst :
  [× wfE si_Σ, si_Σ ;;; [] |-E iv_cF : (iv_Ix 0) {0 := iv_False} &
     isTypeE si_Σ [] ((iv_Ix 0) {0 := iv_False})].
Proof.
  split; [exact si_wfE|exact (iv_cF_typed [] localenv_nil)|].
  exact (validityE (Σ := si_Σ) (wfΣ := si_wfE) (T := (iv_Ix 0) {0 := iv_False}) (iv_cF_typed [] localenv_nil)).
Qed.

(** [validity_envE] at the same application, in the context [x : Prop].
    INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_cF_codomain_moves *)
Definition validity_envE_inst :
  on_global_env cumulSpecE0
    (fun Σ Γ j => lift_sorting (fun _ T => isTypeE Σ Γ T) (fun _ s => wf_sort Σ s) j) si_Σ.1 *
  (wf_localE si_Σ iv_Γ1 * isTypeE si_Σ iv_Γ1 ((iv_Ix 0) {0 := iv_False})) :=
  validity_envE si_Σ si_wfE iv_Γ1 iv_cF ((iv_Ix 0) {0 := iv_False}) (iv_cF_typed iv_Γ1 iv_wf_Γ1).

(** The spine [[∀P:Prop. P]] is not empty: [c (∀P:Prop. P)] is not its head [c]; and the type
    [(λX : Prop. X) (I (∀P:Prop. P))] is not [I (∀P:Prop. P)]. *)
Lemma vi_mkApps_spine_nondeg :
  [/\ [iv_False] <> [],
      mkApps (tConstruct si_ind 0 []) [iv_False] <> tConstruct si_ind 0 [] &
      tApp (iv_idS sProp) iv_IF <> iv_IF].
Proof. split; discriminate. Qed.

(** [inversion_mkAppsE] at [c (∀P:Prop. P) : (λX : Prop. X) (I (∀P:Prop. P))]: the spine
    [[∀P:Prop. P]] is not empty, and the type is not [I (∀P:Prop. P)] ([vi_mkApps_spine_nondeg]).
    INSTANCE NONDEGEN PCUICValidityEtaInstances.vi_mkApps_spine_nondeg
    TARGET PCUICValidityEta.inversion_mkAppsE *)
Definition inversion_mkAppsE_inst :
  (si_Σ ;;; [] |-E mkApps (tConstruct si_ind 0 []) [iv_False] : tApp (iv_idS sProp) iv_IF) ×
  ∑ A, si_Σ ;;; [] |-E tConstruct si_ind 0 [] : A ×
    PCUICAritiesEta.typing_spineE si_Σ [] A [iv_False] (tApp (iv_idS sProp) iv_IF) :=
  (iv_cF_typed_conv,
   inversion_mkAppsE (Σ := si_Σ) (wfΣ := si_wfE) (f := tConstruct si_ind 0 []) (u := [iv_False])
     (T := tApp (iv_idS sProp) iv_IF) iv_cF_typed_conv).

(** [type_App'E] at [c : Π A : Prop. I A] and [∀P:Prop. P : Prop]: the codomain [I A] is
    instantiated at the argument.
    INSTANCE NONDEGEN PCUICInversionEtaInstances.iv_cF_codomain_moves *)
Lemma type_App'E_inst :
  [× si_Σ ;;; [] |-E tConstruct si_ind 0 [] : tProd si_na si_P (iv_Ix 0), si_Σ ;;; [] |-E iv_False : si_P &
     si_Σ ;;; [] |-E tApp (tConstruct si_ind 0 []) iv_False : (iv_Ix 0) {0 := iv_False}].
Proof.
  split; [exact (iv_cstr_typed [] localenv_nil)|exact (iv_False_typed si_Σ [] localenv_nil)|].
  exact (type_App'E (Σ := si_Σ) (wfΣ := si_wfE) (B := iv_Ix 0) (u := iv_False) (iv_cstr_typed [] localenv_nil)
           (iv_False_typed si_Σ [] localenv_nil)).
Qed.

(** The spine is not empty: the application differs from its head, and the arity [Prop → Prop]
    differs from the sort [Prop] the spine reaches. *)
Lemma type_mkApps_arityE_inst_nondeg : mkApps (tInd si_ind []) [iv_False] <> tInd si_ind [] /\ si_arity <> tSort sProp.
Proof. split; discriminate. Qed.

(** [type_mkApps_arityE] at [I (∀P:Prop. P) : Prop], along the arity [Prop → Prop].
    INSTANCE NONDEGEN PCUICValidityEtaInstances.type_mkApps_arityE_inst_nondeg *)
Lemma type_mkApps_arityE_inst :
  [× si_Σ ;;; [] |-E tInd si_ind [] : si_arity,
     arity_spineE si_Σ [] si_arity [iv_False] (tSort sProp) &
     si_Σ ;;; [] |-E mkApps (tInd si_ind []) [iv_False] : tSort sProp].
Proof.
  have sp : arity_spineE si_Σ [] si_arity [iv_False] (tSort sProp).
  { exact (arity_spine_assE _ _ iv_False [] si_na si_P (tSort sProp) (tSort sProp)
             (iv_False_typed si_Σ [] localenv_nil) (arity_spine_nilE _ _ (tSort sProp))). }
  split; [exact (iv_ind_typed [] localenv_nil)|exact sp|].
  exact (type_mkApps_arityE (Σ := si_Σ) (wfΣ := si_wfE) (tty := si_arity) (u := [iv_False])
           (iv_ind_typed [] localenv_nil) sp).
Qed.

(** The type of the projection [f] is the parameter [A], a variable, not a closed type. *)
Lemma declared_projection_typeE_inst_nondeg : closed (proj_type iv_pdecl) = false.
Proof. reflexivity. Qed.

(** [declared_projection_typeE] at the projection [f] of [R]: its type [A] is a type in the
    context [A : Prop, r : R A].
    INSTANCE NONDEGEN PCUICValidityEtaInstances.declared_projection_typeE_inst_nondeg *)
Lemma declared_projection_typeE_inst :
  wfE iv_Σ.1 × declared_projection iv_Σ iv_proj iv_mdecl iv_idecl iv_cdecl iv_pdecl ×
  let u := abstract_instance (ind_universes iv_mdecl) in
  isTypeE (iv_Σ.1, ind_universes iv_mdecl)
    ((vass {| binder_name := nNamed iv_idecl.(ind_name); binder_relevance := iv_idecl.(ind_relevance) |}
        (mkApps (tInd iv_proj.(proj_ind) u) (to_extended_list (smash_context [] (ind_params iv_mdecl)))))::
      smash_context [] (ind_params iv_mdecl)) iv_pdecl.(proj_type).
Proof.
  split; [exact iv_wfE|split; [exact iv_declared_projection|]].
  exact (PCUICInductivesEta.declared_projection_typeE (Σ := iv_Σ) (pdecl := iv_pdecl) iv_wfE
           iv_declared_projection).
Qed.
