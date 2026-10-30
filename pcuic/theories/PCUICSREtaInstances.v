(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICSREta] (row T1)

  **No forecast class.** The lemmas of [PCUICSREta] that used a forecast fact took its forecast
  class [SRForecastCopy18] (copy 18b) as a premise until copy 18b landed (frac/eta 3e6b422d); the
  class is deleted (copies 10, 12, 14, 15, 16 and 18a landed earlier). The instances below, in
  section [SRInstances] (which held the class), apply the lemmas. Everything each instance needs
  (the environment, its [wfE], every typing derivation, every reduction step) is proved here or
  in [PCUICInversionEtaInstances] and [PCUICEtaIdxEnv]. The instance of
  [on_constructor_closed_indicesE], whose E copy of [PCUICSR.v:1138] was deleted for copy 18b's
  identical one, is copy 18b's ([PCUICTypingEtaCopy18bInstances.on_constructor_closed_indicesE_inst]).
  The instances of [subsletE_open_terms] and of the [subsletE] substitution lemma, which left this
  file, are in [PCUICTypingEtaCopies2Instances] and [PCUICTypingEtaCopy15Instances]
  ([substitution_ws_cumul_pbE_typed_inst]).

  **The environments** ([PCUICCumulativitySpecEtaClosureInstances], [PCUICEtaPrimOpInstance],
  [PCUICInversionEtaInstances], [PCUICEtaIdxEnv]):
  - [si_Σ]: [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE];
  - [iv_Σ]: [CoInductive R (A : Prop) : Prop := mkR { f : A }], with [iv_wfE];
  - [PCUICEtaIdxEnv.ji_Σ]: the polymorphic cumulative [J@{i} (A : Prop) : Type@{i} → Prop] with
    the constructor [jc : Π (X : Type@{i}). J A X] (one argument, one index), with [ji_wfE];
  - [Σ_po]: [int : Set], [land : int -> int -> int] registered as [Int63land], the primitive
    integers on [int], with [iv_po_wfE].

  **Non-degeneracy.** Each subject-reduction instance takes a real reduction step of a term with a
  real typing derivation. The steps: β ([sr_red1E_beta_inst]), ζ ([subject_reduction1E_zeta_inst]),
  ι on a [match] ([subject_reduction1E_iota_inst]), fixpoint unfolding
  ([subject_reduction1E_fix_inst]), a β step in a declaration of the context
  ([subject_reduction_ctxE_inst]), β in a type ([type_reductionE_inst], [isType_redE_inst]) and
  in the domain of an arity ([isWfArity_red1E_inst]). [subject_reduction1E_eta_inst] reduces a term
  whose typing derivation goes through an η step: in [g : Prop → Prop, k : (Prop → Prop) → Prop,
  y : k g], the redex [(λz:Prop. y) (∀P:Prop. P)] is typed at [k (λx:Prop. g x)] because [y] is
  ([iv_rel_typed], a [typeE_Cumul] whose conversion is [cumul_eta_l]).

  The helpers of [sr_red1E] that relate two objects relate two different ones:
  [substitution_ws_cumul_pb_subst_convE_inst] substitutes the two lists [[(λx:Prop. x) (∀P:Prop. P)]]
  and [[∀P:Prop. P]] (one β step apart) into [(λy:Prop. y) x] and [x] (one β step apart);
  [conv_context_smash_endE_inst] smashes [w : z, z := (λx:Prop. x) (∀P:Prop. P)] and
  [w : z, z := ∀P:Prop. P] (one β step apart, in the body of the let, which the smash substitutes
  into [w]); [cmp_global_instance_cstr_irrelevantE_inst] compares the two different universe
  instances [[Set]] and [[a]] of the polymorphic cumulative [J@{i}] of [PCUICEtaIdxEnv];
  [ctx_inst_merge'E_inst] steps the argument [(λx:Prop. x) (∀P:Prop. P)] of a telescope. The
  lemmas about a constructor run on [jc] (an argument that the universe instance moves, an index
  that is not closed), those about a branch on a branch of [jc] whose binder name differs from
  [jc]'s, the four [spine_subst_inst_subst*E] on a spine with a let (so [s] is not [List.rev inst]
  and [expand_lets] moves [Δ']), [weakening_closed_red1_cb] on an open step (so the lift moves it),
  [prim_op_head_typeE] and [typing_spine_prim_arg_typesE] on a type that is a β-redex (so the
  comparison is not reflexive).

  **Tags.** Each instance carries its tag in the comment directly above it: NONDEGEN with the
  compiled lemma that states what makes it non-degenerate, or IMPOSSIBLE with the property of
  the statement that makes every instance degenerate (four rows:
  [declared_projection_declared_constructorE], [declared_projection_indicesE],
  [PCUICSREta.conv_refl'E] and [conv_context_reflE]).

  **Helpers without an instance of their own**, each run on a real step by an instance here:
  - [ctx_inst_mergeE]: helper, exercised by [ctx_inst_merge'E_inst] ([ctx_inst_merge'E] is its one
    caller; inside [sr_red1E], [sr_red1E_Case] calls [ctx_inst_merge'E] for a step in the
    parameters of a [match]);
  - [lift_judgment_SRE]: helper, exercised by [isWfArity_red1E_inst]: the step in the domain of
    [Π z : (λx:Prop. x) (∀P:Prop. P). Prop] runs [isType_red1E], then [subject_reduction1E], then
    [sr_red1E_Prod], which calls it (it is also called by [sr_red1E_ctx], [sr_red1E_Lambda] and
    [sr_red1E_LetIn]);
  - [typing_spine_prim_argsE]: helper, exercised by [prim_app_typing_invE_inst]:
    [prim_app_typing_invE] calls it on the spine [1 3] of [land 1 3] in [Σ_po]. *)

From Stdlib Require Import ssreflect ssrbool PrimInt63.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping
     PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICCasesContexts PCUICEquality PCUICReduction PCUICConfluence PCUICWellScopedCumulativity
     PCUICPrimitiveRed PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions
     PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICWeakeningTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaPrimOpInstance
     PCUICInversionEta PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICInductivesEta
     PCUICValidityEta PCUICSREta.
From MetaRocq.PCUIC Require PCUICSR PCUICEtaIdxEnv.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(* The pieces the instances are built from (terms, contexts, typing derivations, steps):
   WITNESSES: sri_* *)

(** ** Pieces, without any class *)

(** [(λx:Prop. x) (∀P:Prop. P)], a β-redex of type [Prop], and its step. *)
Definition sri_A : term := tApp iv_id iv_False.

Lemma sri_beta (Γ : context) : red1 si_Σ Γ sri_A iv_False.
Proof. exact (red_beta si_Σ Γ si_na si_P (tRel 0) iv_False). Qed.

(** The β step moves the term: the redex is not its reduct. *)
Lemma sri_beta_nondeg : sri_A <> iv_False.
Proof. intros h; vm_compute in h; discriminate h. Qed.

(** The two one-term lists [[(λx:Prop. x) (∀P:Prop. P)]] and [[∀P:Prop. P]] differ. *)
Lemma sri_inst_nondeg : [sri_A] <> [iv_False].
Proof. intros h; vm_compute in h; discriminate h. Qed.

Lemma sri_A_isType : isTypeE si_Σ [] sri_A.
Proof. exact (has_sort_isTypeE sProp (iv_app_typed si_Σ [] localenv_nil)). Qed.

(** The context [z : (λx:Prop. x) (∀P:Prop. P)]. *)
Definition sri_Γz : context := [vass si_na sri_A].

Lemma sri_wf_Γz : wf_localE si_Σ sri_Γz.
Proof. exact (iv_wf_vass si_Σ [] si_na sri_A sProp localenv_nil (iv_app_typed si_Σ [] localenv_nil) eq_refl). Qed.

Lemma sri_z_typed : si_Σ ;;; sri_Γz |-E tRel 0 : sri_A.
Proof. exact (typeE_Rel _ _ 0 (vass si_na sri_A) sri_wf_Γz eq_refl). Qed.

(** The context step [z : (λx:Prop. x) (∀P:Prop. P)] ⇝ [z : ∀P:Prop. P]. *)
Lemma sri_red_ctx : red1_ctx si_Σ sri_Γz [vass si_na iv_False].
Proof. constructor. split; [reflexivity|exact (sri_beta [])]. Qed.

(** The context step moves the context. *)
Lemma sri_ctx_nondeg : sri_Γz <> [vass si_na iv_False].
Proof. intros h; vm_compute in h; discriminate h. Qed.

(** The η-typed redex [(λz:Prop. y) (∀P:Prop. P)] in [iv_Γk], at [k (λx:Prop. g x)]. *)
Definition sri_eta_redex : term := tApp (tLambda si_na si_P (tRel 1)) iv_False.

Lemma sri_eta_redex_typed : si_Σ ;;; iv_Γk |-E sri_eta_redex : iv_keta.
Proof.
  have w := iv_wf_P si_Σ iv_Γk iv_wf_Γk.
  have hy : si_Σ ;;; iv_Γk ,, vass si_na si_P |-E tRel 1 : lift0 1 iv_keta.
  { exact (weakeningE si_Σ iv_Γk [vass si_na si_P] (tRel 0) iv_keta si_wfE w iv_rel_typed). }
  have hk : si_Σ ;;; iv_Γk ,, vass si_na si_P |-E lift0 1 iv_keta : tSort sProp.
  { exact (weakeningE si_Σ iv_Γk [vass si_na si_P] iv_keta si_P si_wfE w iv_keta_typed). }
  have hP := iv_P_typed si_Σ iv_Γk iv_wf_Γk.
  exact (typeE_App _ _ (tLambda si_na si_P (tRel 1)) si_na si_P (lift0 1 iv_keta) _ iv_False
           (typeE_Prod _ _ si_na si_P (lift0 1 iv_keta) _ sProp (iv_vass_s si_Σ iv_Γk si_na si_P _ hP eq_refl) hk)
           (typeE_Lambda _ _ si_na si_P (tRel 1) (lift0 1 iv_keta) (iv_vass si_Σ iv_Γk si_na si_P _ hP eq_refl) hy)
           (iv_False_typed si_Σ iv_Γk iv_wf_Γk)).
Qed.

(** [c (∀P:Prop. P) : I (∀P:Prop. P)], the argument of the fixpoint. *)
Definition sri_cF : term := tApp (tConstruct si_ind 0 []) iv_False.

Lemma sri_cF_typed : si_Σ ;;; [] |-E sri_cF : iv_IF.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ iv_False
           (iv_cstr_prod_typed [] localenv_nil) (iv_cstr_typed [] localenv_nil)
           (iv_False_typed si_Σ [] localenv_nil)).
Qed.

Lemma sri_fix_app_typed : si_Σ ;;; [] |-E mkApps (tFix iv_mfix 0) [sri_cF] : iv_IF.
Proof. exact (typeE_App _ _ (tFix iv_mfix 0) si_na iv_IF iv_IF _ sri_cF (iv_fix_ty_typed [] localenv_nil) iv_fix_typed sri_cF_typed). Qed.

(** Fixpoint unfolding: the argument [c (∀P:Prop. P)] is a constructor application. *)
Lemma sri_fix_red :
  red1 si_Σ [] (mkApps (tFix iv_mfix 0) [sri_cF]) (mkApps (tLambda si_na iv_IF (tRel 0)) [sri_cF]).
Proof. apply red_fix with (narg := 0); reflexivity. Qed.

(** ι: [match c x with c => c x end] ⇝ [c x], in [x : Prop]. *)
Lemma sri_iota_red : red1 si_Σ iv_Γ1 iv_match (iota_red 1 iv_mp [tRel 0] iv_br).
Proof. exact (red_iota si_Σ iv_Γ1 iv_ci 0 [] [tRel 0] iv_mp [iv_br] iv_br eq_refl eq_refl). Qed.

Lemma sri_iota_reduct : iota_red 1 iv_mp [tRel 0] iv_br = iv_disc.
Proof. reflexivity. Qed.

(** The arity [Π z : (λx:Prop. x) (∀P:Prop. P). Prop], whose domain is a β-redex. *)
Definition sri_arity : term := tProd si_na sri_A si_P.

Lemma sri_arity_typed : si_Σ ;;; [] |-E sri_arity : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof.
  exact (typeE_Prod _ _ si_na sri_A si_P sProp (Sort.super sProp)
           (iv_vass_s si_Σ [] si_na sri_A sProp (iv_app_typed si_Σ [] localenv_nil) eq_refl)
           (iv_P_typed si_Σ sri_Γz sri_wf_Γz)).
Qed.

Lemma sri_arity_wf : isWfArityE si_Σ [] sri_arity.
Proof.
  split; [exact (has_sort_isTypeE _ sri_arity_typed)|].
  exists [vass si_na sri_A], sProp. reflexivity.
Qed.

Lemma sri_arity_red : red1 si_Σ [] sri_arity (tProd si_na iv_False si_P).
Proof. exact (prod_red_l si_Σ [] si_na sri_A si_P iv_False (sri_beta [])). Qed.

(** The step in the domain moves the arity. *)
Lemma sri_arity_nondeg : sri_arity <> tProd si_na iv_False si_P.
Proof. intros h; vm_compute in h; discriminate h. Qed.

(** [z := ∀P:Prop. P : Prop ⊢ z : Prop]. *)
Lemma sri_vdef_rel_isType : isTypeE si_Σ ([] ,, vdef si_na iv_False si_P) (tRel 0).
Proof.
  exact (has_sort_isTypeE sProp
           (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) (iv_wf_vdef si_Σ [] localenv_nil) eq_refl)).
Qed.

(** A substitution: [(∀P:Prop. P)] for [x : Prop]. *)
Lemma sri_subslet : subsletE si_Σ [] [iv_False] [vass si_na si_P].
Proof. constructor; [constructor|exact (iv_False_typed si_Σ [] localenv_nil)]. Qed.

Lemma sri_wf_subslet : wf_subsletE si_Σ [] [iv_False] [vass si_na si_P].
Proof. split; [exact (iv_wf_P si_Σ [] localenv_nil)|exact sri_subslet]. Qed.

(** A spine with a let: [x : Prop, y := x : Prop] (the let is the outer declaration), at the
    instance [[∀P:Prop. P]]. Its substitution [sri_sL] has an entry for the let too:
    [y := ∀P:Prop. P, x := ∀P:Prop. P]. *)
Definition sri_ΔL : context := [vdef si_na (tRel 0) si_P; vass si_na si_P].
Definition sri_sL : list term := [iv_False; iv_False].

Lemma sri_wf_ΔL : wf_localE si_Σ sri_ΔL.
Proof.
  have w := iv_wf_P si_Σ [] localenv_nil.
  unfold sri_ΔL. apply localenv_cons_def; [exact w|].
  exact (iv_vdef si_Σ [vass si_na si_P] si_na (tRel 0) si_P _
           (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl) (iv_P_typed si_Σ _ w) eq_refl).
Qed.

Lemma sri_subsletL : subsletE si_Σ [] sri_sL sri_ΔL.
Proof.
  change sri_sL with (subst0 [iv_False] (tRel 0) :: [iv_False]).
  change sri_ΔL with ([vass si_na si_P] ,, vdef si_na (tRel 0) si_P).
  apply cons_let_defE; [exact sri_subslet|exact (iv_False_typed si_Σ [] localenv_nil)].
Qed.

Lemma sri_wf_subsletL : wf_subsletE si_Σ [] sri_sL sri_ΔL.
Proof. split; [exact sri_wf_ΔL|exact sri_subsletL]. Qed.

Lemma sri_spineL : spine_substE si_Σ [] [iv_False] sri_sL sri_ΔL.
Proof.
  constructor.
  - constructor.
  - exact sri_wf_ΔL.
  - exact (PCUICContextSubst.context_subst_def [vass si_na si_P] [iv_False] [iv_False] si_na (tRel 0) si_P
             (PCUICContextSubst.context_subst_ass [] [] [] si_na si_P iv_False PCUICContextSubst.context_subst_nil)).
  - exact sri_subsletL.
Qed.

(** The other side of [sri_subslet]: the β-redex [(λx:Prop. x) (∀P:Prop. P)] for [x : Prop]. *)
Lemma sri_subslet_A : subsletE si_Σ [] [sri_A] [vass si_na si_P].
Proof. constructor; [constructor|exact (iv_app_typed si_Σ [] localenv_nil)]. Qed.

(** [(λx:Prop. x) (∀P:Prop. P) = ∀P:Prop. P], by the β step [sri_beta], in any closed context. *)
Lemma sri_ws_beta pb (Γ : context) (cl : is_closed_context Γ) : ws_cumul_pbE pb si_Σ Γ sri_A iv_False.
Proof. apply red_ws_cumul_pbE. split; [exact cl|reflexivity|exact (red1_red _ _ _ _ (sri_beta Γ))]. Qed.

Lemma sri_terms_beta : ws_cumul_pbE_terms si_Σ [] [sri_A] [iv_False].
Proof. constructor; [exact (sri_ws_beta Conv [] eq_refl)|constructor]. Qed.

(** [x : Prop ⊢ (λy:Prop. y) x ≤ x], by β. *)
Definition sri_id_x : term := tApp iv_id (tRel 0).

Lemma sri_ws_id_x : ws_cumul_pbE Cumul si_Σ [vass si_na si_P] sri_id_x (tRel 0).
Proof.
  apply red_ws_cumul_pbE. split; [reflexivity|reflexivity|].
  exact (red1_red _ _ _ _ (red_beta si_Σ [vass si_na si_P] si_na si_P (tRel 0) (tRel 0))).
Qed.

(** [x : Prop ⊢ (λy:Prop. y) x ⇝1 x], a closed step between two open terms. *)
Lemma sri_cr1_id_x : closed_red1 si_Σ [vass si_na si_P] sri_id_x (tRel 0).
Proof. split; [reflexivity|reflexivity|exact (red_beta si_Σ [vass si_na si_P] si_na si_P (tRel 0) (tRel 0))]. Qed.

(** [w : z, z := b : Prop] (the let is the outer declaration), at the β-redex
    [b := (λx:Prop. x) (∀P:Prop. P)] and at its reduct [b := ∀P:Prop. P]. *)
Definition sri_Δlet (b : term) : context := [vass si_na (tRel 0); vdef si_na b si_P].

Lemma sri_wf_Δlet (b : term) : si_Σ ;;; [] |-E b : si_P -> wf_localE si_Σ (sri_Δlet b).
Proof.
  intros hb.
  have wd : wf_localE si_Σ ([] ,, vdef si_na b si_P).
  { apply localenv_cons_def; [exact localenv_nil|].
    exact (iv_vdef si_Σ [] si_na b si_P _ hb (iv_P_typed si_Σ [] localenv_nil) eq_refl). }
  exact (iv_wf_vass si_Σ ([] ,, vdef si_na b si_P) si_na (tRel 0) sProp wd
           (typeE_Rel _ _ 0 (vdef si_na b si_P) wd eq_refl) eq_refl).
Qed.

(** The two lets are one β step apart in the body; [w : z] is the same on both sides. *)
Lemma sri_ctx_let_beta : ws_cumul_ctx_pbE Conv si_Σ (sri_Δlet sri_A) (sri_Δlet iv_False).
Proof.
  constructor; [constructor; [constructor|]|].
  - constructor; [reflexivity|exact (sri_ws_beta Conv [] eq_refl)|apply ws_cumul_pbE_refl; reflexivity].
  - constructor; [reflexivity|apply ws_cumul_pbE_refl; reflexivity].
Qed.

(** The closed step [(λx:Prop. x) (∀P:Prop. P) ⇝1 ∀P:Prop. P], in any closed context. *)
Lemma sri_cr1 (Γ : context) (cl : is_closed_context Γ) : closed_red1 si_Σ Γ sri_A iv_False.
Proof. split; [exact cl|reflexivity|exact (sri_beta Γ)]. Qed.

(** The arities context of [I] and [X : Prop → Prop ⊢ X (∀P:Prop. P) : Prop]. *)
Definition sri_Γa : context := (arities_context (ind_bodies si_mdecl))@[[]].

Lemma sri_wf_Γa : wf_localE si_Σ sri_Γa.
Proof.
  exact (iv_wf_vass si_Σ [] (mkBindAnn (nNamed "I") rel_of_Type) si_arity _ localenv_nil
           (iv_PP_typed si_Σ [] localenv_nil) eq_refl).
Qed.

Lemma sri_Ia_isType : isTypeE si_Σ (sri_Γa ,,, []) (tApp (tRel 0) iv_False).
Proof.
  apply (has_sort_isTypeE sProp).
  exact (typeE_App _ _ (tRel 0) si_na si_P (tSort sProp) _ iv_False (iv_PP_typed si_Σ sri_Γa sri_wf_Γa)
           (typeE_Rel _ _ 0 (vass (mkBindAnn (nNamed "I") rel_of_Type) si_arity) sri_wf_Γa eq_refl)
           (iv_False_typed si_Σ sri_Γa sri_wf_Γa)).
Qed.

(** *** Pieces in [PCUICEtaIdxEnv.ji_Σ]: [J@{Set} A X] in [ji_Γ = [X : Set; A : Prop]] *)

Definition sri_ji_cb : ClosedBodies PCUICEtaIdxEnv.ji_Σ :=
  @wfE_ClosedBodies _ PCUICEtaIdxEnv.ji_Σ PCUICEtaIdxEnv.ji_wfE.

(** The branch of [jc], which binds [jc]'s argument under the name [Z] ([jc] names it [X]). *)
Definition sri_jbr : branch term :=
  {| bcontext := [vass PCUICEtaIdxEnv.ji_naZ PCUICEtaIdxEnv.ji_T]; bbody := tRel 0 |}.

Lemma sri_jbr_wf : wf_branch PCUICEtaIdxEnv.ji_cdecl sri_jbr.
Proof. repeat constructor. Qed.

Lemma sri_jbr_eq :
  eq_context_upto_names (bcontext sri_jbr)
    (cstr_branch_context PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_cdecl).
Proof.
  change (eq_context_upto_names [vass PCUICEtaIdxEnv.ji_naZ PCUICEtaIdxEnv.ji_T]
            [vass PCUICEtaIdxEnv.ji_naX PCUICEtaIdxEnv.ji_T]).
  repeat constructor.
Qed.

Lemma sri_jTSet_typed (Γ : context) : wf_localE PCUICEtaIdxEnv.ji_Σ Γ ->
  PCUICEtaIdxEnv.ji_Σ ;;; Γ |-E PCUICEtaIdxEnv.ji_TSet : tSort (Sort.super Sort.type0).
Proof. intros h. exact (typeE_Sort _ _ Sort.type0 h (PCUICWfUniverses.wf_sort_type0 _)). Qed.

Lemma sri_wf_jΓ : wf_localE PCUICEtaIdxEnv.ji_Σ PCUICEtaIdxEnv.ji_Γ.
Proof.
  have w := iv_wf_P PCUICEtaIdxEnv.ji_Σ [] localenv_nil.
  exact (iv_wf_vass PCUICEtaIdxEnv.ji_Σ _ PCUICEtaIdxEnv.ji_naX PCUICEtaIdxEnv.ji_TSet _ w
           (sri_jTSet_typed _ w) eq_refl).
Qed.

(** The branch context of [sri_jbr] at [J@{Set} A]: [Z : Set]. *)
Lemma sri_jbr_wf_ctx :
  wf_localE PCUICEtaIdxEnv.ji_Σ
    (PCUICEtaIdxEnv.ji_Γ ,,, PCUICCases.case_branch_context PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl
       PCUICEtaIdxEnv.ji_p (forget_types (bcontext sri_jbr)) PCUICEtaIdxEnv.ji_cdecl).
Proof.
  change (wf_localE PCUICEtaIdxEnv.ji_Σ (PCUICEtaIdxEnv.ji_Γ ,, vass PCUICEtaIdxEnv.ji_naZ PCUICEtaIdxEnv.ji_TSet)).
  exact (iv_wf_vass PCUICEtaIdxEnv.ji_Σ _ PCUICEtaIdxEnv.ji_naZ PCUICEtaIdxEnv.ji_TSet _ sri_wf_jΓ
           (sri_jTSet_typed _ sri_wf_jΓ) eq_refl).
Qed.

(** [(λY:Prop. Y) A ⇝1 A] in [ji_Γ]: an open step ([A] is [tRel 1]). *)
Lemma sri_jidA_cr1 : closed_red1 PCUICEtaIdxEnv.ji_Σ PCUICEtaIdxEnv.ji_Γ PCUICEtaIdxEnv.ji_idA (tRel 1).
Proof. split; [reflexivity|reflexivity|exact (red_beta _ _ si_na si_P (tRel 0) (tRel 1))]. Qed.

(** *** Pieces in [Σ_po]: [land 1 3 : int] *)

Definition sri_iA : aname := {| binder_name := nAnon; binder_relevance := rel_of_Type |}.
Definition sri_int : term := tConst po_int_kn [].

Lemma sri_int_typed (Γ : context) (h : wf_localE Σ_po Γ) :
  Σ_po ;;; Γ |-E sri_int : (cst_type po_int_body)@[[]].
Proof. exact (typeE_Const _ _ po_int_kn [] po_int_body h iv_po_declared_int eq_refl). Qed.

Lemma sri_impl_typed (Γ : context) (h : wf_localE Σ_po Γ) :
  ∑ s, Σ_po ;;; Γ |-E tImpl sri_int sri_int : tSort s.
Proof.
  have hi := sri_int_typed Γ h.
  eexists. unfold tImpl. eapply typeE_Prod.
  - eapply (iv_vass_s Σ_po Γ sri_iA sri_int); [exact hi|reflexivity].
  - exact (sri_int_typed _ (iv_wf_vass Σ_po Γ sri_iA sri_int _ h hi eq_refl)).
Qed.

Lemma sri_land_ty_typed : ∑ s, Σ_po ;;; [] |-E po_land_ty : tSort s.
Proof.
  have hi := sri_int_typed [] localenv_nil.
  have w := iv_wf_vass Σ_po [] sri_iA sri_int _ localenv_nil hi eq_refl.
  destruct (sri_impl_typed _ w) as [s2 h2].
  eexists. unfold po_land_ty, tImpl at 1. eapply typeE_Prod.
  - eapply (iv_vass_s Σ_po [] sri_iA sri_int); [exact hi|reflexivity].
  - exact h2.
Qed.

Lemma sri_prim_typed (i : PrimInt63.int) : Σ_po ;;; [] |-E tPrim (prim_int i) : sri_int.
Proof.
  refine (typeE_Prim Σ_po [] (prim_int i) po_int_kn po_int_body localenv_nil eq_refl
            iv_po_declared_int _ _).
  - split; reflexivity.
  - constructor.
Qed.

Lemma sri_land_app_typed :
  Σ_po ;;; [] |-E mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 3%uint63]) : sri_int.
Proof.
  destruct sri_land_ty_typed as [s hl].
  destruct (sri_impl_typed [] localenv_nil) as [s' himpl].
  have h1 : Σ_po ;;; [] |-E tApp (tConst po_land_kn []) (tPrim (prim_int 1%uint63)) : tImpl sri_int sri_int.
  { exact (typeE_App _ _ (tConst po_land_kn []) sri_iA sri_int (lift 1 0 (tImpl sri_int sri_int)) s
             (tPrim (prim_int 1%uint63)) hl iv_land_typed (sri_prim_typed 1%uint63)). }
  exact (typeE_App _ _ (tApp (tConst po_land_kn []) (tPrim (prim_int 1%uint63))) sri_iA sri_int
           (lift 1 0 sri_int) s' (tPrim (prim_int 3%uint63)) himpl h1 (sri_prim_typed 3%uint63)).
Qed.

Lemma sri_po_on_result : on_prim_op_result Σ_po SInt.
Proof. exists po_int_kn, po_int_body. split; [reflexivity|exact iv_po_declared_int|split; reflexivity]. Qed.

Lemma sri_tag_declared : prim_op_tag_declared Σ_po primInt.
Proof. exists po_int_kn, po_int_body. split; [reflexivity|exact iv_po_declared_int|split; reflexivity]. Qed.

(** [int] is a registered primitive type with no body: what the primitive lemmas type comes from
    the registration of [int63] in [Σ_po] and from [int]'s declared sort, not from unfolding. *)
Lemma sri_po_int_nondeg :
  Retroknowledge.retro_int63 (retroknowledge Σ_po.1) = Some po_int_kn /\ cst_body po_int_body = None.
Proof. split; reflexivity. Qed.

Definition sri_po_cb : ClosedBodies Σ_po0 := @wfE_ClosedBodies _ Σ_po0 iv_po_wfE.

(** [(λT:Set. T) (int → int → int)], a β-redex whose reduct is the type of [land]. *)
Definition sri_land_ty_beta : term := tApp (tLambda sri_iA (tSort Sort.type0) (tRel 0)) po_land_ty.

Lemma sri_land_ty_red : closed_red Σ_po [] sri_land_ty_beta po_land_ty.
Proof.
  split; [reflexivity|reflexivity|].
  exact (red1_red _ _ _ _ (red_beta Σ_po [] sri_iA (tSort Sort.type0) (tRel 0) po_land_ty)).
Qed.

Lemma sri_land_ty_ws : Σ_po ;;; [] ⊢E po_land_ty ≤ sri_land_ty_beta.
Proof. exact (red_ws_cumul_pbE_inv (Σ := Σ_po) (wfΣ := sri_po_cb) (pb := Cumul) sri_land_ty_red). Qed.

(** [(λT:Set. T) int], a β-redex whose reduct is [int], and [land 1 3] typed at it. *)
Definition sri_int_beta : term := tApp (tLambda sri_iA (tSort Sort.type0) (tRel 0)) sri_int.

Lemma sri_int_beta_typed : Σ_po ;;; [] |-E sri_int_beta : tSort Sort.type0.
Proof.
  have hS : Σ_po ;;; [] |-E tSort Sort.type0 : tSort (Sort.super Sort.type0).
  { exact (typeE_Sort _ _ Sort.type0 localenv_nil (PCUICWfUniverses.wf_sort_type0 _)). }
  have w := iv_wf_vass Σ_po [] sri_iA (tSort Sort.type0) _ localenv_nil hS eq_refl.
  have hS' : Σ_po ;;; [] ,, vass sri_iA (tSort Sort.type0) |-E tSort Sort.type0 : tSort (Sort.super Sort.type0).
  { exact (typeE_Sort _ _ Sort.type0 w (PCUICWfUniverses.wf_sort_type0 _)). }
  exact (typeE_App _ _ (tLambda sri_iA (tSort Sort.type0) (tRel 0)) sri_iA (tSort Sort.type0) (tSort Sort.type0)
           _ sri_int
           (typeE_Prod _ _ sri_iA (tSort Sort.type0) (tSort Sort.type0) _ _
              (iv_vass_s Σ_po [] sri_iA _ _ hS eq_refl) hS')
           (typeE_Lambda _ _ sri_iA (tSort Sort.type0) (tRel 0) (tSort Sort.type0)
              (iv_vass Σ_po [] sri_iA _ _ hS eq_refl)
              (typeE_Rel _ _ 0 (vass sri_iA (tSort Sort.type0)) w eq_refl))
           (sri_int_typed [] localenv_nil)).
Qed.

Lemma sri_int_beta_cumul : cumulSpecE Σ_po [] sri_int sri_int_beta.
Proof. apply cumulE_Sym. exact (cumulE_beta _ _ Conv sri_iA (tSort Sort.type0) (tRel 0) sri_int). Qed.

Lemma sri_land_app_typed_beta :
  Σ_po ;;; [] |-E mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 3%uint63]) : sri_int_beta.
Proof. exact (typeE_Cumul _ _ _ sri_int sri_int_beta Sort.type0 sri_land_app_typed sri_int_beta_typed sri_int_beta_cumul). Qed.

Section SRInstances.

  (** *** [sr_red1E] and its corollaries *)

  (** [sr_red1E] (through [env_propE_typing]) at β, with [typing_closed_red1E] for the step.
      TARGET PCUICSREta.sr_red1E
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma sr_red1E_beta_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    have ht := iv_app_typed si_Σ [] localenv_nil.
    pose proof (env_propE_typing sr_red1E si_Σ si_wfE [] _ _ ht) as h.
    unfold SR_red1E in h.
    exact (h iv_False (typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) ht (sri_beta []))).
  Qed.

  (** The β step moves the term, and the type [k (λx:Prop. g x)] it is typed at is the η-expanded
      one, not [k g], the declared type of [y]. *)
  Lemma subject_reduction1E_eta_inst_nondeg : sri_eta_redex <> tRel 0 /\ iv_kg <> iv_keta.
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** β on a term typed through η.
      TARGET PCUICSREta.subject_reduction1E
      INSTANCE NONDEGEN PCUICSREtaInstances.subject_reduction1E_eta_inst_nondeg *)
  Lemma subject_reduction1E_eta_inst : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta.
  Proof.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_eta_redex) (T := iv_keta)
             sri_eta_redex_typed (red_beta si_Σ iv_Γk si_na si_P (tRel 1) iv_False)).
  Qed.

  (** The ζ step moves the term. *)
  Lemma subject_reduction1E_zeta_inst_nondeg : tLetIn si_na iv_False si_P (tRel 0) <> iv_False.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** ζ: [let z : Prop := ∀P:Prop. P in z] ⇝ [∀P:Prop. P].
      TARGET PCUICSREta.subject_reduction1E
      INSTANCE NONDEGEN PCUICSREtaInstances.subject_reduction1E_zeta_inst_nondeg *)
  Lemma subject_reduction1E_zeta_inst : si_Σ ;;; [] |-E iv_False : tLetIn si_na iv_False si_P si_P.
  Proof.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) (iv_let_typed si_Σ [] localenv_nil)
             (red_zeta si_Σ [] si_na iv_False si_P (tRel 0))).
  Qed.

  (** The ι step moves the term. *)
  Lemma subject_reduction1E_iota_inst_nondeg : iv_match <> iv_disc.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** ι on the [match] of [PCUICInversionEtaInstances].
      TARGET PCUICSREta.subject_reduction1E
      INSTANCE NONDEGEN PCUICSREtaInstances.subject_reduction1E_iota_inst_nondeg *)
  Lemma subject_reduction1E_iota_inst : si_Σ ;;; iv_Γ1 |-E iv_disc : iv_match_ty.
  Proof.
    rewrite -sri_iota_reduct.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) (t := iv_match) iv_match_typed sri_iota_red).
  Qed.

  (** The fixpoint unfolding moves the term. *)
  Lemma subject_reduction1E_fix_inst_nondeg :
    mkApps (tFix iv_mfix 0) [sri_cF] <> mkApps (tLambda si_na iv_IF (tRel 0)) [sri_cF].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** Fixpoint unfolding.
      TARGET PCUICSREta.subject_reduction1E
      INSTANCE NONDEGEN PCUICSREtaInstances.subject_reduction1E_fix_inst_nondeg *)
  Lemma subject_reduction1E_fix_inst :
    si_Σ ;;; [] |-E mkApps (tLambda si_na iv_IF (tRel 0)) [sri_cF] : iv_IF.
  Proof.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) (t := mkApps (tFix iv_mfix 0) [sri_cF])
             sri_fix_app_typed sri_fix_red).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma subject_reductionE_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    exact (subject_reductionE si_Σ [] sri_A iv_False si_P si_wfE (iv_app_typed si_Σ [] localenv_nil)
             (red1_red _ _ _ _ (sri_beta []))).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma subject_reduction1_closedE_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    have ht := iv_app_typed si_Σ [] localenv_nil.
    exact (subject_reduction1_closedE si_Σ [] sri_A iv_False si_P si_wfE ht
             (typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) ht (sri_beta []))).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma subject_reduction_closedE_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    have ht := iv_app_typed si_Σ [] localenv_nil.
    exact (subject_reduction_closedE si_Σ [] sri_A iv_False si_P si_wfE ht
             (typing_closed_redE (Σ := si_Σ) (wfΣ := si_wfE) ht (red1_red _ _ _ _ (sri_beta [])))).
  Qed.

  (** *** Reduction of the type *)

  (** The type [(λx:Prop. x) (∀P:Prop. P)] steps to [∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma type_reductionE_inst : si_Σ ;;; sri_Γz |-E tRel 0 : iv_False.
  Proof.
    exact (type_reductionE (Σ := si_Σ) (wfΣ := si_wfE) sri_z_typed
             (red1_red _ _ sri_A iv_False (sri_beta sri_Γz))).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma type_reduction_closedE_inst : si_Σ ;;; sri_Γz |-E tRel 0 : iv_False.
  Proof.
    exact (type_reduction_closedE (Σ := si_Σ) (wfΣ := si_wfE) sri_z_typed
             (typing_closed_redE (Σ := si_Σ) (wfΣ := si_wfE) (iv_app_typed si_Σ sri_Γz sri_wf_Γz)
                (red1_red _ _ sri_A iv_False (sri_beta sri_Γz)))).
  Qed.

  (** *** Section [SRContextE] *)

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma isType_red1E_inst : isTypeE si_Σ [] iv_False.
  Proof. exact (isType_red1E (Σ := si_Σ) (wfΣ := si_wfE) (A := sri_A) sri_A_isType (sri_beta [])). Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Lemma isType_redE_inst : isTypeE si_Σ [] iv_False.
  Proof.
    exact (isType_redE (Σ := si_Σ) (wfΣ := si_wfE) sri_A_isType (red1_red _ _ sri_A iv_False (sri_beta []))).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_arity_nondeg *)
  Lemma isWfArity_red1E_inst : isWfArityE si_Σ [] (tProd si_na iv_False si_P).
  Proof. exact (isWfArity_red1E (Σ := si_Σ) (wfΣ := si_wfE) (A := sri_arity) sri_arity_wf sri_arity_red). Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_arity_nondeg *)
  Lemma isWfArity_redE_inst : isWfArityE si_Σ [] (tProd si_na iv_False si_P).
  Proof.
    exact (isWfArity_redE (Σ := si_Σ) (wfΣ := si_wfE) sri_arity_wf
             (red1_red _ _ sri_arity (tProd si_na iv_False si_P) sri_arity_red)).
  Qed.

  (** A β step in the declaration of the variable that the term is.
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_nondeg *)
  Lemma subject_reduction_ctxE_inst : si_Σ ;;; [vass si_na iv_False] |-E tRel 0 : sri_A.
  Proof.
    exact (subject_reduction_ctxE (Σ := si_Σ) (wfΣ := si_wfE) sri_Γz [vass si_na iv_False] (tRel 0) sri_A
             sri_red_ctx sri_z_typed).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_nondeg *)
  Lemma wf_local_red1E_inst : wf_localE si_Σ [vass si_na iv_False].
  Proof. exact (wf_local_red1E (Σ := si_Σ) (wfΣ := si_wfE) (Γ := sri_Γz) sri_red_ctx sri_wf_Γz). Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_nondeg *)
  Lemma wf_local_redE_inst : wf_localE si_Σ [vass si_na iv_False].
  Proof.
    exact (wf_local_redE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := sri_Γz) (PCUICSR.red1_red_ctx si_Σ _ _ sri_red_ctx)
             sri_wf_Γz).
  Qed.

  (** The substitution of the let's body moves [w : z]. *)
  Lemma wf_local_subst1E_inst_nondeg : subst_context [iv_False] 0 [vass si_na (tRel 0)] <> [vass si_na (tRel 0)].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [let z : Prop := ∀P:Prop. P, w : z] gives [w : ∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.wf_local_subst1E_inst_nondeg *)
  Lemma wf_local_subst1E_inst : wf_localE si_Σ ([] ,,, subst_context [iv_False] 0 [vass si_na (tRel 0)]).
  Proof.
    apply (wf_local_subst1E (Σ := si_Σ) (wfΣ := si_wfE) [] si_na iv_False si_P [vass si_na (tRel 0)]).
    have wd := iv_wf_vdef si_Σ [] localenv_nil.
    exact (iv_wf_vass si_Σ ([] ,, vdef si_na iv_False si_P) si_na (tRel 0) sProp wd
             (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) wd eq_refl) eq_refl).
  Qed.

  (** The declaration [y : k g] has an open type ([k g] is [tApp (tRel 0) (tRel 1)]), so the lift
      by one moves it. *)
  Lemma wf_local_isType_nthE_inst_nondeg :
    lift0 1 (decl_type (vass si_na (tApp (tRel 0) (tRel 1)))) <> decl_type (vass si_na (tApp (tRel 0) (tRel 1))).
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.wf_local_isType_nthE_inst_nondeg *)
  Lemma wf_local_isType_nthE_inst :
    ∑ s, si_Σ ;;; iv_Γk |-E lift0 1 (tApp (tRel 0) (tRel 1)) : tSort s.
  Proof.
    exact (wf_local_isType_nthE (Σ := si_Σ) (wfΣ := si_wfE) iv_Γk 0 (vass si_na (tApp (tRel 0) (tRel 1)))
             iv_wf_Γk eq_refl).
  Qed.

  (** *** [isType_tLetInE], both directions, at [let z : Prop := ∀P:Prop. P in z] *)

  (** The body of the let is its bound variable: the let's value matters ([z{0 := ∀P:Prop. P}] is
      not [z]). *)
  Lemma isType_tLetInE_inst_nondeg : subst1 iv_False 0 (tRel 0) <> tRel 0.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.isType_tLetInE_inst_nondeg *)
  Lemma isType_tLetInE_inst :
    isTypeE si_Σ [] (tLetIn si_na iv_False si_P (tRel 0)) ×
    (lift_typing typingE si_Σ [] (j_vdef si_na iv_False si_P) ×
     isTypeE si_Σ ([] ,, vdef si_na iv_False si_P) (tRel 0)).
  Proof.
    (* [pose proof], not ssreflect's [have :=], which would abstract the forecast-class holes
       instead of resolving them from the section's [Context]. *)
    pose proof (snd (isType_tLetInE (Σ := si_Σ) (HΣ' := si_wfE) (t := iv_False))
                  (iv_vdef_False si_Σ [] localenv_nil, sri_vdef_rel_isType)) as h.
    exact (h, fst (isType_tLetInE (Σ := si_Σ) (HΣ' := si_wfE)) h).
  Qed.

  (** *** Helpers of [sr_red1E]: projections, constructors, branches *)

  (** At the projection of the record [R] of [iv_Σ].
      INSTANCE IMPOSSIBLE: the conclusion mdecl = mdecl' /\ idecl = idecl' /\ cdecl = cdecl' compares the results of two lookups of the same names (the inductive p.(proj_ind) and its constructor 0); lookups are functional, so in every environment, whatever its wfE, the two sides are equal *)
  Lemma declared_projection_declared_constructorE_inst :
    iv_mdecl = iv_mdecl /\ iv_idecl = iv_idecl /\ iv_cdecl = iv_cdecl.
  Proof.
    exact (declared_projection_declared_constructorE (Σ := iv_Σ) (wfΣ := iv_wfE)
             iv_declared_projection iv_declared_constructor).
  Qed.

  (** At the projection of the record [R] of [iv_Σ].
      INSTANCE IMPOSSIBLE: the conclusion #|ind_indices idecl| = 0 is a numeral equation on the declaration that the premise looks up; every instance names a concrete declaration, so in every instance it computes to 0 = 0 and holds by reflexivity *)
  Lemma declared_projection_indicesE_inst : #|ind_indices iv_idecl| = 0.
  Proof. exact (declared_projection_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_projection). Qed.

  (** The record [R] has a parameter, and the instance applies it to one argument: the spine is
      not empty. *)
  Lemma isType_mkApps_Ind_proj_invE_inst_nondeg : ind_npars iv_mdecl <> 0 /\ #|[iv_False]| = ind_npars iv_mdecl.
  Proof. split; [intros h; vm_compute in h; discriminate h|reflexivity]. Qed.

  (** [R (∀P:Prop. P)] is a type: its parameter spine.
      INSTANCE NONDEGEN PCUICSREtaInstances.isType_mkApps_Ind_proj_invE_inst_nondeg *)
  Definition isType_mkApps_Ind_proj_invE_inst :=
    isType_mkApps_Ind_proj_invE (Σ := iv_Σ) (Γ := []) (u := []) (pars := [iv_False]) iv_wfE
      iv_declared_projection (has_sort_isTypeE sProp (iv_RF_typed [] localenv_nil)).

  (** [jc] has an argument, and the universe instance [[Set]] moves it ([X : Type@{i}] becomes
      [X : Type@{Set}]). *)
  Lemma on_constructor_wf_argsE_inst_nondeg :
    cstr_args PCUICEtaIdxEnv.ji_cdecl <> [] /\
    subst_instance PCUICEtaIdxEnv.ji_u0 (cstr_args PCUICEtaIdxEnv.ji_cdecl) <> cstr_args PCUICEtaIdxEnv.ji_cdecl.
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** At [jc] of [J@{Set}].
      INSTANCE NONDEGEN PCUICSREtaInstances.on_constructor_wf_argsE_inst_nondeg *)
  Definition on_constructor_wf_argsE_inst :=
    PCUICSREta.on_constructor_wf_argsE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE)
      (cdecl := PCUICEtaIdxEnv.ji_cdecl) (u := PCUICEtaIdxEnv.ji_u0)
      PCUICEtaIdxEnv.ji_declared_constructor PCUICEtaIdxEnv.ji_cons0.

  (** [jc] has an argument: the context is not only the arities and the parameters. *)
  Lemma on_constructor_wf_arities_pars_argsE_inst_nondeg : cstr_args PCUICEtaIdxEnv.ji_cdecl <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** At [jc] of [J].
      INSTANCE NONDEGEN PCUICSREtaInstances.on_constructor_wf_arities_pars_argsE_inst_nondeg *)
  Definition on_constructor_wf_arities_pars_argsE_inst :=
    on_constructor_wf_arities_pars_argsE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE)
      (cdecl := PCUICEtaIdxEnv.ji_cdecl) PCUICEtaIdxEnv.ji_declared_constructor.

  (** [jc] has an index, and it is not closed (it is the argument [X]). *)
  Lemma on_constructor_closed_indices_instE_inst_nondeg :
    cstr_indices PCUICEtaIdxEnv.ji_cdecl <> [] /\ forallb (closedn 0) (cstr_indices PCUICEtaIdxEnv.ji_cdecl) = false.
  Proof. split; [intros h; vm_compute in h; discriminate h|reflexivity]. Qed.

  (** At [jc] of [J@{Set}].
      INSTANCE NONDEGEN PCUICSREtaInstances.on_constructor_closed_indices_instE_inst_nondeg *)
  Definition on_constructor_closed_indices_instE_inst :=
    on_constructor_closed_indices_instE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE)
      (cdecl := PCUICEtaIdxEnv.ji_cdecl) (u := PCUICEtaIdxEnv.ji_u0)
      PCUICEtaIdxEnv.ji_declared_constructor PCUICEtaIdxEnv.ji_cons0.

  (** The two universe instances [[Set]] and [[a]] of [J] differ. *)
  Lemma sri_ju_differ : PCUICEtaIdxEnv.ji_u0 <> PCUICEtaIdxEnv.ji_u1.
  Proof. discriminate. Qed.

  (** At the polymorphic cumulative [J@{i}] of [PCUICEtaIdxEnv] (its constructor [jc], the
      covariant variance), with two different universe instances [[Set]] and [[a]]
      ([sri_ju_differ]): the premise is [Set ≤ a] at the full arity of [J] ([ji_cmp]), and the
      conclusion relates the two instances at [Conv] for [jc] fully applied.
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_ju_differ *)
  Lemma cmp_global_instance_cstr_irrelevantE_inst :
    cmp_global_instance PCUICEtaIdxEnv.ji_Σ.1 (compare_universe PCUICEtaIdxEnv.ji_Σ) Conv
      (ConstructRef PCUICEtaIdxEnv.ji_ind 0)
      (ind_npars PCUICEtaIdxEnv.ji_mdecl + context_assumptions (cstr_args PCUICEtaIdxEnv.ji_cdecl))
      PCUICEtaIdxEnv.ji_u0 PCUICEtaIdxEnv.ji_u1.
  Proof.
    exact (cmp_global_instance_cstr_irrelevantE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE)
             (u := PCUICEtaIdxEnv.ji_u0) (u' := PCUICEtaIdxEnv.ji_u1)
             PCUICEtaIdxEnv.ji_declared_constructor PCUICEtaIdxEnv.ji_cmp).
  Qed.

  (** The branch context ([Z : Set], named by the branch) and the pre-branch context
      ([X : Set], named by [jc]) differ: the lemma's renaming is not the identity. *)
  Lemma wf_pre_case_branch_contextE_inst_nondeg :
    PCUICCases.case_branch_context PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_p
      (forget_types (bcontext sri_jbr)) PCUICEtaIdxEnv.ji_cdecl <>
    pre_case_branch_context PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl (pparams PCUICEtaIdxEnv.ji_p)
      (puinst PCUICEtaIdxEnv.ji_p) PCUICEtaIdxEnv.ji_cdecl.
  Proof. intros h; apply (f_equal (map decl_name)) in h; vm_compute in h; discriminate h. Qed.

  (** The branch [sri_jbr] of [jc] in a [match] on [J@{Set} A] in [ji_Γ].
      INSTANCE NONDEGEN PCUICSREtaInstances.wf_pre_case_branch_contextE_inst_nondeg *)
  Definition wf_pre_case_branch_contextE_inst :=
    wf_pre_case_branch_contextE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE) (Γ := PCUICEtaIdxEnv.ji_Γ)
      (p := PCUICEtaIdxEnv.ji_p) (br := sri_jbr) (cdecl := PCUICEtaIdxEnv.ji_cdecl)
      PCUICEtaIdxEnv.ji_declared_inductive sri_jbr_wf PCUICEtaIdxEnv.ji_cons0 sri_jbr_wf_ctx.

  (** The instantiated branch context ([Z : Set]) and the pre-branch context ([X : Set]) differ:
      the conclusion is not between equal contexts. *)
  Lemma inst_case_branch_context_eqE_inst_nondeg :
    inst_case_branch_context PCUICEtaIdxEnv.ji_p sri_jbr <>
    pre_case_branch_context PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl (pparams PCUICEtaIdxEnv.ji_p)
      (puinst PCUICEtaIdxEnv.ji_p) PCUICEtaIdxEnv.ji_cdecl.
  Proof. intros h; apply (f_equal (map decl_name)) in h; vm_compute in h; discriminate h. Qed.

  (** The branch [sri_jbr] of [jc] at [J@{Set} A].
      INSTANCE NONDEGEN PCUICSREtaInstances.inst_case_branch_context_eqE_inst_nondeg *)
  Definition inst_case_branch_context_eqE_inst :=
    inst_case_branch_context_eqE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE)
      (p := PCUICEtaIdxEnv.ji_p) (br := sri_jbr) (ind := PCUICEtaIdxEnv.ji_ind) (cdecl := PCUICEtaIdxEnv.ji_cdecl)
      PCUICEtaIdxEnv.ji_declared_minductive PCUICEtaIdxEnv.ji_cons0 sri_jbr_eq.

  (** INSTANCE IMPOSSIBLE: the only premise is x = y, and Σ and Γ carry no premise at all, so every instance, in every environment and context, compares a term with itself *)
  Definition conv_refl'E_inst : JoinE si_Σ [] Conv iv_False iv_False :=
    PCUICSREta.conv_refl'E (Σ := si_Σ) (Γ := []) eq_refl.

  (** INSTANCE IMPOSSIBLE: a Reflexive instance with no premise (Σ is any environment, with no wf premise), so every instance relates a context to itself *)
  Definition conv_context_reflE_inst := conv_context_reflE si_Σ sri_Γz.

  (** *** Helpers of [sr_red1E]: spines and substitutions *)

  (** The spine has a let, so its substitution is not the reversed instance, and [expand_lets]
      moves [Δ'] (its [tRel 1] is [x], below the let [y]). *)
  Lemma spine_subst_inst_substE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\ expand_lets_ctx sri_ΔL [vass si_na (tRel 1)] <> [vass si_na (tRel 1)].
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_substE_inst_nondeg *)
  Definition spine_subst_inst_substE_inst :=
    spine_subst_inst_substE (Δ := sri_ΔL) (Δ' := [vass si_na (tRel 1)]) sri_spineL.

  Lemma spine_subst_inst_subst_termE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\ expand_lets sri_ΔL (tRel 1) <> tRel 1.
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_subst_termE_inst_nondeg *)
  Definition spine_subst_inst_subst_termE_inst :=
    spine_subst_inst_subst_termE (Δ := sri_ΔL) (Δ' := tRel 1) sri_spineL.

  Lemma spine_subst_inst_subst_kE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\ expand_lets_k_ctx sri_ΔL 1 [vass si_na (tRel 2)] <> [vass si_na (tRel 2)].
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_subst_kE_inst_nondeg *)
  Definition spine_subst_inst_subst_kE_inst :=
    spine_subst_inst_subst_kE (Δ := sri_ΔL) (k := 1) (Δ' := [vass si_na (tRel 2)]) sri_spineL.

  Lemma spine_subst_inst_subst_term_kE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\ expand_lets_k sri_ΔL 1 (tRel 2) <> tRel 2.
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_subst_term_kE_inst_nondeg *)
  Definition spine_subst_inst_subst_term_kE_inst :=
    spine_subst_inst_subst_term_kE (Δ := sri_ΔL) (k := 1) (Δ' := tRel 2) sri_spineL.

  (** The instance is not empty: the conclusion types a term. *)
  Lemma spine_subst_wt_termsE_inst_nondeg : [iv_False] <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_wt_termsE_inst_nondeg *)
  Definition spine_subst_wt_termsE_inst := spine_subst_wt_termsE (inst := [iv_False]) sri_spineL.

  (** Skipping one entry drops the let and keeps the assumption: neither all nor nothing. *)
  Lemma wf_subslet_skipnE_inst_nondeg : skipn 1 sri_sL <> sri_sL /\ skipn 1 sri_sL <> [].
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.wf_subslet_skipnE_inst_nondeg *)
  Definition wf_subslet_skipnE_inst := wf_subslet_skipnE (s := sri_sL) (Δ := sri_ΔL) (n := 1) sri_wf_subsletL.

  (** The two substitutions differ, and so do the two compared terms. *)
  Lemma substitution_ws_cumul_pb_subst_convE_inst_nondeg : [sri_A] <> [iv_False] /\ sri_id_x <> tRel 0.
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** [s = [(λx:Prop. x) (∀P:Prop. P)]] and [s' = [∀P:Prop. P]], one β step apart
      ([sri_terms_beta]); [T = (λy:Prop. y) x] and [U = x], one β step apart in [x : Prop]
      ([sri_ws_id_x]). The conclusion relates [(λy:Prop. y) ((λx:Prop. x) (∀P:Prop. P))] and
      [∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.substitution_ws_cumul_pb_subst_convE_inst_nondeg *)
  Lemma substitution_ws_cumul_pb_subst_convE_inst : si_Σ ;;; [] ⊢E tApp iv_id sri_A ≤ iv_False.
  Proof.
    exact (substitution_ws_cumul_pb_subst_convE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := [])
             (s := [sri_A]) (s' := [iv_False]) (T := sri_id_x) (U := tRel 0)
             sri_subslet_A sri_wf_subslet sri_terms_beta sri_ws_id_x).
  Qed.

  (** *** Helpers of [sr_red1E]: contexts and types *)

  (** The context added below is not empty. *)
  Lemma isType_weakenE_inst_nondeg : [vdef si_na iv_False si_P] <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.isType_weakenE_inst_nondeg *)
  Definition isType_weakenE_inst :=
    PCUICSREta.isType_weakenE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := [vdef si_na iv_False si_P])
      (iv_wf_vdef si_Σ [] localenv_nil) sri_A_isType.

  (** Expanding the let moves [z] to its value. *)
  Lemma isType_expand_letsE_inst_nondeg : expand_lets_k [vdef si_na iv_False si_P] 0 (tRel 0) <> tRel 0.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** Expanding the let [z := ∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.isType_expand_letsE_inst_nondeg *)
  Definition isType_expand_letsE_inst :=
    isType_expand_letsE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := [vdef si_na iv_False si_P]) (Δ := []) sri_vdef_rel_isType.

  (** The extended substitution of the let moves [z] to its value. *)
  Lemma isType_subst_extended_substE_inst_nondeg :
    subst (extended_subst [vdef si_na iv_False si_P] 0) 0 (tRel 0) <> tRel 0.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.isType_subst_extended_substE_inst_nondeg *)
  Definition isType_subst_extended_substE_inst :=
    isType_subst_extended_substE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := [vdef si_na iv_False si_P]) (Δ := [])
      sri_vdef_rel_isType.

  (** The substitution of the inductive for the arity variable moves [X (∀P:Prop. P)]. *)
  Lemma isType_subst_aritiesE_inst_nondeg :
    subst (ind_subst si_mdecl si_ind []) 0 (tApp (tRel 0) iv_False) <> tApp (tRel 0) iv_False.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [X (∀P:Prop. P)] in the arities context becomes [I (∀P:Prop. P)].
      INSTANCE NONDEGEN PCUICSREtaInstances.isType_subst_aritiesE_inst_nondeg *)
  Definition isType_subst_aritiesE_inst :=
    isType_subst_aritiesE (Σ := si_Σ) (wfΣ := si_wfE) (u := []) (Γ := []) (T := tApp (tRel 0) iv_False)
      si_declared_inductive eq_refl sri_Ia_isType.

  (** The two lets differ. *)
  Lemma conv_context_smash_endE_inst_nondeg : sri_Δlet sri_A <> sri_Δlet iv_False.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [Δ = sri_Δlet ((λx:Prop. x) (∀P:Prop. P))] and [Δ' = sri_Δlet (∀P:Prop. P)], one β step
      apart ([sri_ctx_let_beta]). The smash substitutes the body of the let into [w]: the
      conclusion relates [w : (λx:Prop. x) (∀P:Prop. P)] and [w : ∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.conv_context_smash_endE_inst_nondeg *)
  Lemma conv_context_smash_endE_inst : ws_cumul_ctx_pbE Conv si_Σ [vass si_na sri_A] [vass si_na iv_False].
  Proof.
    exact (conv_context_smash_endE (Σ := si_Σ) (wfΣ := si_wfE) [] (sri_Δlet sri_A) (sri_Δlet iv_False)
             (sri_wf_Δlet sri_A (iv_app_typed si_Σ [] localenv_nil))
             (sri_wf_Δlet iv_False (iv_False_typed si_Σ [] localenv_nil)) sri_ctx_let_beta).
  Qed.

  (** The telescope [x : Prop] instantiated by [(λx:Prop. x) (∀P:Prop. P)], which steps to
      [∀P:Prop. P] ([sri_cr1]); the reduction premise is [subject_reduction1E]. This runs
      [ctx_inst_mergeE] on that step.
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_inst_nondeg *)
  Lemma ctx_inst_merge'E_inst : ctx_instE si_Σ [] [iv_False] (List.rev [vass si_na si_P]).
  Proof.
    have ha := iv_app_typed si_Σ [] localenv_nil.
    apply (ctx_inst_merge'E (Σ := si_Σ) (wfΣ := si_wfE) [] [sri_A] [iv_False] [vass si_na si_P]).
    - exact (iv_wf_P si_Σ [] localenv_nil).
    - constructor; [|constructor].
      intros u r. exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) ha (closed_red1_red1 r)).
    - constructor; [exact ha|constructor].
    - constructor. exact (sri_cr1 [] eq_refl).
  Qed.

  (** *** Helpers of [sr_red1E]: closed reductions *)

  (** The two abstractions differ. *)
  Lemma closed_red1_it_mkLambda_or_LetIn_cb_inst_nondeg :
    it_mkLambda_or_LetIn [vass si_na si_P] sri_A <> it_mkLambda_or_LetIn [vass si_na si_P] iv_False.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.closed_red1_it_mkLambda_or_LetIn_cb_inst_nondeg *)
  Definition closed_red1_it_mkLambda_or_LetIn_cb_inst :=
    closed_red1_it_mkLambda_or_LetIn_cb (Σ := si_Σ) (Γ := []) (Δ := [vass si_na si_P]) (t := sri_A)
      (sri_cr1 ([] ,,, [vass si_na si_P]) eq_refl).

  (** The two applications differ. *)
  Lemma closed_red1_mkApps_left_cb_inst_nondeg : mkApps sri_A [iv_False] <> mkApps iv_False [iv_False].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.closed_red1_mkApps_left_cb_inst_nondeg *)
  Definition closed_red1_mkApps_left_cb_inst :=
    closed_red1_mkApps_left_cb (Σ := si_Σ) (t := sri_A) (ts := [iv_False]) (sri_cr1 [] eq_refl) eq_refl.

  (** The step is between open terms, so the lift moves them. *)
  Lemma weakening_closed_red1_cb_inst_nondeg : lift 1 0 sri_id_x <> sri_id_x.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [x : Prop ⊢ (λy:Prop. y) x ⇝1 x], weakened by [y : Prop] below it: [y : Prop, x : Prop ⊢
      (λy:Prop. y) y' ⇝1 y'] with [y'] the lifted variable.
      INSTANCE NONDEGEN PCUICSREtaInstances.weakening_closed_red1_cb_inst_nondeg *)
  Definition weakening_closed_red1_cb_inst :=
    weakening_closed_red1_cb (Σ := si_Σ) (Γ := [vass si_na si_P]) (Γ' := []) (Γ'' := [vass si_na si_P])
      (M := sri_id_x) (N := tRel 0) sri_cr1_id_x eq_refl.

  (** The branch context is not empty (so the step is weakened under [jc]'s binder), the lift
      moves the open return clause [(λY:Prop. Y) A], and the two branch types differ. *)
  Lemma closed_red1_case_branch_type_cb_inst_nondeg :
    (case_branch_type PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_idecl PCUICEtaIdxEnv.ji_p
       sri_jbr PCUICEtaIdxEnv.ji_idA 0 PCUICEtaIdxEnv.ji_cdecl).1 <> [] /\
    lift0 1 PCUICEtaIdxEnv.ji_idA <> PCUICEtaIdxEnv.ji_idA /\
    (case_branch_type PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_idecl PCUICEtaIdxEnv.ji_p
       sri_jbr PCUICEtaIdxEnv.ji_idA 0 PCUICEtaIdxEnv.ji_cdecl).2 <>
    (case_branch_type PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_idecl PCUICEtaIdxEnv.ji_p
       sri_jbr (tRel 1) 0 PCUICEtaIdxEnv.ji_cdecl).2.
  Proof. split; [|split]; intros h; vm_compute in h; discriminate h. Qed.

  (** The return clause [(λY:Prop. Y) A] steps to [A] in [ji_Γ]; so does the type of the branch
      [sri_jbr] of [jc], under its binder [Z].
      INSTANCE NONDEGEN PCUICSREtaInstances.closed_red1_case_branch_type_cb_inst_nondeg *)
  Definition closed_red1_case_branch_type_cb_inst :=
    closed_red1_case_branch_type_cb (Σ := PCUICEtaIdxEnv.ji_Σ) (cbΣ := sri_ji_cb) (Γ := PCUICEtaIdxEnv.ji_Γ)
      (ret := PCUICEtaIdxEnv.ji_idA) (ret' := tRel 1) (ind := PCUICEtaIdxEnv.ji_ind) (mdecl := PCUICEtaIdxEnv.ji_mdecl)
      (idecl := PCUICEtaIdxEnv.ji_idecl) (k := 0) (cdecl := PCUICEtaIdxEnv.ji_cdecl) (br := sri_jbr)
      (p := PCUICEtaIdxEnv.ji_p) sri_jbr_wf eq_refl eq_refl sri_jidA_cr1.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_inst_nondeg *)
  Lemma closed_red_red_subst0_cb_inst : closed_red si_Σ [] (subst0 [sri_A] (tRel 0)) (subst0 [iv_False] (tRel 0)).
  Proof.
    apply (closed_red_red_subst0_cb (Σ := si_Σ) (Δ := [vass si_na si_P]) (s := [sri_A]) (s' := [iv_False]));
      [reflexivity| |repeat constructor|reflexivity].
    constructor; [|constructor].
    split; [reflexivity|reflexivity|exact (red1_red _ _ _ _ (sri_beta []))].
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_nondeg *)
  Lemma red1_it_mkLambda_or_LetIn_ctx_cb_inst :
    red1 si_Σ [] (it_mkLambda_or_LetIn sri_Γz (tRel 0)) (it_mkLambda_or_LetIn [vass si_na iv_False] (tRel 0)).
  Proof.
    apply (red1_it_mkLambda_or_LetIn_ctx_cb (Σ := si_Σ) [] sri_Γz [vass si_na iv_False] (tRel 0)).
    constructor. split; [reflexivity|exact (sri_beta _)].
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Definition wt_closed_red1E_inst :=
    wt_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) (T := sri_A) (si_P; iv_app_typed si_Σ [] localenv_nil) (sri_beta []).

  (** *** [case_nondep_predicate_convE]: two different discriminees, one return clause that does not
      use it ([match] of [PCUICInversionEtaInstances]: [I x] for any discriminee). *)

  (** The two discriminees differ. *)
  Lemma case_nondep_predicate_convE_inst_nondeg : iv_disc <> tRel 0.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.case_nondep_predicate_convE_inst_nondeg *)
  Definition case_nondep_predicate_convE_inst :=
    case_nondep_predicate_convE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γ1) (ci := iv_ci) (mdecl := si_mdecl)
      (idecl := si_idecl) (p := iv_mp) (indices := []) (c := iv_disc) (c' := tRel 0) (ps := sProp)
      eq_refl iv_pret_typed eq_refl eq_refl eq_refl eq_refl.

  (** *** Primitive operations, in [Σ_po]: [land 1 3 ⇝ 1] *)

  (** The operation's step moves the term: an application becomes a literal. *)
  Lemma sr_prim_opE_inst_nondeg :
    mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 3%uint63]) <> tPrim (prim_int 1%uint63).
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sr_prim_opE_inst_nondeg *)
  Lemma sr_prim_opE_inst : Σ_po ;;; [] |-E tPrim (prim_int 1%uint63) : sri_int.
  Proof.
    exact (sr_prim_opE (Σ := Σ_po) (wfΣ := iv_po_wfE) (c := po_land_kn) (ls := [LInt 1%uint63; LInt 3%uint63])
             (r := RInt 1%uint63) sri_land_app_typed Σ_po_registers Σ_po_declared_land po_land_1_3 eq_refl).
  Qed.

  (** The spine is not empty: both arguments are checked against [int]. *)
  Lemma prim_app_typing_invE_inst_nondeg : map term_of_lit [LInt 1%uint63; LInt 3%uint63] <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.prim_app_typing_invE_inst_nondeg *)
  Definition prim_app_typing_invE_inst :=
    prim_app_typing_invE (Σ := Σ_po) (wfΣ := iv_po_wfE) (args := map term_of_lit [LInt 1%uint63; LInt 3%uint63])
      Σ_po_registers sri_land_app_typed ltac:(cbn; lia).

  (** The type [A] that [land]'s declared type is compared with is a β-redex, not that type. *)
  Lemma prim_op_head_typeE_inst_nondeg : sri_land_ty_beta <> po_land_ty.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [land]'s type [int → int → int] below [(λT:Set. T) (int → int → int)] ([sri_land_ty_ws]).
      INSTANCE NONDEGEN PCUICSREtaInstances.prim_op_head_typeE_inst_nondeg *)
  Definition prim_op_head_typeE_inst :=
    prim_op_head_typeE (Σ := Σ_po) (wfΣ := iv_po_wfE) (Γ := []) (u := []) (A := sri_land_ty_beta) localenv_nil
      Σ_po_declared_land eq_refl Σ_po_registers sri_land_ty_ws.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_po_int_nondeg *)
  Lemma readback_typedE_inst : Σ_po ;;; [] |-E tPrim (prim_int 1%uint63) : sri_int.
  Proof.
    exact (readback_typedE (Σ := Σ_po) (wfΣ := iv_po_wfE) (s := SInt) (r := RInt 1%uint63) localenv_nil eq_refl
             sri_po_on_result eq_refl).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_po_int_nondeg *)
  Lemma isType_prim_shape_typeE_inst : isTypeE Σ_po [] sri_int.
  Proof.
    exact (isType_prim_shape_typeE (Σ := Σ_po) (wfΣ := iv_po_wfE) (s := SInt) localenv_nil eq_refl
             sri_po_on_result).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_po_int_nondeg *)
  Lemma isType_prim_tag_constantE_inst : isTypeE Σ_po [] sri_int.
  Proof.
    apply (isType_prim_tag_constantE (Σ := Σ_po) (wfΣ := iv_po_wfE) (t := primInt) (kn := po_int_kn)
             (d := po_int_body) localenv_nil);
      [discriminate|exact iv_po_declared_int|split; reflexivity].
  Qed.

  (** The argument types build a product: [int → int → int] is not the result type [int]. *)
  Lemma isType_prim_arg_typesE_inst_nondeg : po_land_ty <> sri_int.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [int -> int -> int], the type of [land], from [int].
      INSTANCE NONDEGEN PCUICSREtaInstances.isType_prim_arg_typesE_inst_nondeg *)
  Lemma isType_prim_arg_typesE_inst : isTypeE Σ_po [] po_land_ty.
  Proof.
    apply (isType_prim_arg_typesE (Σ := Σ_po) (wfΣ := iv_po_wfE) (tags := [primInt; primInt]) (res := sri_int)
             localenv_nil).
    - intros t [<-|[<-|[]]]; discriminate.
    - constructor; [exact sri_tag_declared|constructor; [exact sri_tag_declared|constructor]].
    - reflexivity.
    - exact isType_prim_shape_typeE_inst.
  Qed.

  (** The type [T] the application is typed at is the β-redex [(λT:Set. T) int], not [int]. *)
  Lemma typing_spine_prim_arg_typesE_inst_nondeg : sri_int_beta <> sri_int.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** The spine of [land 1 3] typed at [(λT:Set. T) int] ([sri_land_app_typed_beta]), from
      [inversion_mkAppsE] and [inversion_ConstE]: [int ≤ (λT:Set. T) int].
      INSTANCE NONDEGEN PCUICSREtaInstances.typing_spine_prim_arg_typesE_inst_nondeg *)
  Lemma typing_spine_prim_arg_typesE_inst : Σ_po ;;; [] ⊢E sri_int ≤ sri_int_beta.
  Proof.
    destruct (inversion_mkAppsE (Σ := Σ_po) (wfΣ := iv_po_wfE) sri_land_app_typed_beta) as [A [hA sp]].
    destruct (inversion_ConstE Σ_po iv_po_wfE hA) as (decl & _ & hd & _ & hle).
    assert (ed : decl = po_land_body).
    { destruct hd as [e|[e|[]]]; [injection e as ->; reflexivity|cbv in e; congruence]. }
    subst decl.
    exact (typing_spine_prim_arg_typesE (Σ := Σ_po) (wfΣ := iv_po_wfE) (r := po_retro) (tags := [primInt; primInt])
             (res := sri_int) (T := sri_int_beta) (ls := [LInt 1%uint63; LInt 3%uint63]) po_land_ty A eq_refl hle
             eq_refl sp).
  Qed.

End SRInstances.
