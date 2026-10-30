(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma; the measured reader miss rate is recorded in lanes/eta/meta/reader-catch-rate.tsv. *)

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
  real typing derivation. The steps: β on [(λx:Prop. x → x) (∀P:Prop. P)], whose body uses its
  variable, so the reduct [(∀P:Prop. P) → ∀P:Prop. P] is a new product ([sr_red1E_beta_inst], its
  corollaries, [isType_red1E_inst], [isType_redE_inst], the context step of [wf_local_red1E_inst]
  and [wf_local_redE_inst], the type step of a let in [lift_judgment_SRE_inst]; [sri_xx_nondeg]),
  ζ ([subject_reduction1E_zeta_inst]),
  ι on a [match] ([subject_reduction1E_iota_inst]), fixpoint unfolding
  ([subject_reduction1E_fix_inst]), a β step in a declaration of the context
  ([subject_reduction_ctxE_inst]), β in a type ([type_reductionE_inst]) and
  in the domain of an arity ([isWfArity_red1E_inst]). [subject_reduction1E_eta_inst] reduces a term
  whose typing derivation goes through an η step: in [g : Prop → Prop, k : (Prop → Prop) → Prop,
  y : k g], the redex [(λz : k g. (λw : k g. w) z) y], whose body uses [z] as an argument, has type
  [k g] and is typed at [k (λx:Prop. g x)] by a [typeE_Cumul] whose conversion is [cumul_eta_l]
  ([sri_eta_redex_typed]); its reduct is [(λw : k g. w) y].

  The helpers of [sr_red1E] that relate two objects relate two different ones:
  [substitution_ws_cumul_pb_subst_convE_inst] substitutes the two lists [[(λx:Prop. x) (∀P:Prop. P)]]
  and [[∀P:Prop. P]] (one β step apart) into [(λy:Prop. y) (x → x)] and [x → x] (one β step apart);
  [conv_context_smash_endE_inst] smashes [w : z, z := (λx:Prop. x) (∀P:Prop. P)] and
  [w : z, z := ∀P:Prop. P] (one β step apart, in the body of the let, which the smash substitutes
  into [w]); [ctx_inst_merge'E_inst] steps the argument [(λx:Prop. x) (∀P:Prop. P)] of a telescope.
  ([cmp_global_instance_cstr_irrelevantE_inst] is tagged IMPOSSIBLE: its conclusion relates two
  universe instances only through its premise.) The
  lemmas about a constructor run on [jc] (an argument that the universe instance moves, an index
  that is not closed), those about a branch on a branch of [jc] whose binder name differs from
  [jc]'s, the four [spine_subst_inst_subst*E] on a spine with a let (so [s] is not [List.rev inst])
  and a [Δ'] that uses both the let and the assumption ([y → x]), [weakening_closed_red1_cb] on an
  open step (so the lift moves it),
  [prim_op_head_typeE] and [typing_spine_prim_arg_typesE] on a type that is a β-redex (so the
  comparison is not reflexive).

  **Tags.** Each instance carries its tag in the comment directly above it: NONDEGEN with the
  compiled lemma that states what makes it non-degenerate, or IMPOSSIBLE with the property of
  the statement that makes every instance degenerate (six rows:
  [declared_projection_declared_constructorE], [declared_projection_indicesE],
  [cmp_global_instance_cstr_irrelevantE], [isType_prim_tag_constantE], [PCUICSREta.conv_refl'E]
  and [conv_context_reflE]).

  **Helpers with an instance of their own**, each also run inside another instance here:
  - [ctx_inst_mergeE_inst]: the telescope [x : Prop, f : x → x], whose first argument
    [(λx:Prop. x) (∀P:Prop. P)] steps, so the type of [f] moves with it.
    [ctx_inst_merge'E_inst] runs [ctx_inst_mergeE] through [ctx_inst_merge'E], its one caller
    (inside [sr_red1E], [sr_red1E_Case] calls [ctx_inst_merge'E] for a step in the parameters of
    a [match]);
  - [lift_judgment_SRE_inst]: the let [y := z : (λx:Prop. x → x) (∀P:Prop. P)] in
    [z : (λx:Prop. x → x) (∀P:Prop. P)], whose type steps to [(∀P:Prop. P) → ∀P:Prop. P] while its
    body [z] stays. [isWfArity_red1E_inst] also runs [lift_judgment_SRE], on the step in the
    domain of [Π z : (λx:Prop. x) (∀P:Prop. P). Prop], through [isType_red1E],
    [subject_reduction1E] and [sr_red1E_Prod] (it is also called by [sr_red1E_ctx],
    [sr_red1E_Lambda] and [sr_red1E_LetIn]);
  - [typing_spine_prim_argsE_inst]: the spine [1] of the partial application [land 1] in
    [Σ_po] (one argument of two, so neither part of the conclusion is vacuous).
    [prim_app_typing_invE_inst] runs it through [prim_app_typing_invE] on the spine [1 3] of
    [land 1 3];
  - [typing_closed_red1E_inst] and [typing_closed_redE_inst]: the β step [sri_beta] of the typed
    [(λx:Prop. x) (∀P:Prop. P)], in [[]] and in [z : (λx:Prop. x) (∀P:Prop. P)]
    ([type_reduction_closedE_inst] also runs [typing_closed_redE] on that step;
    [sr_red1E_beta_inst], [subject_reduction1_closedE_inst] and [subject_reduction_closedE_inst]
    run the two lemmas on the β step [sri_xx_beta] of [(λx:Prop. x → x) (∀P:Prop. P)]). *)

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

(** The η-typed redex [(λz : k g. (λw : k g. w) z) y] in [iv_Γk]. Its body [(λw : k g. w) z]
    ([sri_eta_body], where [k g] is [tApp (tRel 2) (tRel 3)]) uses [z] as an argument; its reduct is
    [(λw : k g. w) y]. *)
Definition sri_eta_body : term := tApp (tLambda si_na (lift0 1 iv_kg) (tRel 0)) (tRel 0).
Definition sri_eta_redex : term := tApp (tLambda si_na iv_kg sri_eta_body) (tRel 0).
Definition sri_eta_reduct : term := tApp (tLambda si_na iv_kg (tRel 0)) (tRel 0).

Lemma sri_eta_step : red1 si_Σ iv_Γk sri_eta_redex sri_eta_reduct.
Proof. exact (red_beta si_Σ iv_Γk si_na iv_kg sri_eta_body (tRel 0)). Qed.

(** The redex has type [k g], and [typeE_Cumul] with [iv_spec_eta] (whose conversion is
    [cumul_eta_l]) types it at [k (λx:Prop. g x)]. *)
Lemma sri_eta_redex_typed : si_Σ ;;; iv_Γk |-E sri_eta_redex : iv_keta.
Proof.
  have hkg : si_Σ ;;; iv_Γk |-E iv_kg : tSort sProp.
  { exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ (tRel 2) (iv_K_typed iv_Γk iv_wf_Γk)
             (typeE_Rel _ _ 1 (vass si_na iv_K) iv_wf_Γk eq_refl)
             (typeE_Rel _ _ 2 (vass si_na iv_PP) iv_wf_Γk eq_refl)). }
  have w1 := iv_wf_vass si_Σ iv_Γk si_na iv_kg sProp iv_wf_Γk hkg eq_refl.
  have hkg1 : si_Σ ;;; iv_Γk ,, vass si_na iv_kg |-E lift0 1 iv_kg : tSort sProp.
  { exact (typeE_App _ _ (tRel 2) si_na iv_PP si_P _ (tRel 3) (iv_K_typed _ w1)
             (typeE_Rel _ _ 2 (vass si_na iv_K) w1 eq_refl)
             (typeE_Rel _ _ 3 (vass si_na iv_PP) w1 eq_refl)). }
  have w2 := iv_wf_vass si_Σ _ si_na (lift0 1 iv_kg) sProp w1 hkg1 eq_refl.
  have hkg2 : si_Σ ;;; iv_Γk ,, vass si_na iv_kg ,, vass si_na (lift0 1 iv_kg) |-E lift0 2 iv_kg : tSort sProp.
  { exact (typeE_App _ _ (tRel 3) si_na iv_PP si_P _ (tRel 4) (iv_K_typed _ w2)
             (typeE_Rel _ _ 3 (vass si_na iv_K) w2 eq_refl)
             (typeE_Rel _ _ 4 (vass si_na iv_PP) w2 eq_refl)). }
  have hP1 : si_Σ ;;; iv_Γk ,, vass si_na iv_kg |-E tProd si_na (lift0 1 iv_kg) (lift0 2 iv_kg)
               : tSort (Sort.sort_of_product sProp sProp).
  { exact (typeE_Prod _ _ si_na (lift0 1 iv_kg) (lift0 2 iv_kg) sProp sProp
             (iv_vass_s si_Σ _ si_na (lift0 1 iv_kg) sProp hkg1 eq_refl) hkg2). }
  have hbody : si_Σ ;;; iv_Γk ,, vass si_na iv_kg |-E sri_eta_body : lift0 1 iv_kg.
  { exact (typeE_App _ _ (tLambda si_na (lift0 1 iv_kg) (tRel 0)) si_na (lift0 1 iv_kg) (lift0 2 iv_kg) _ (tRel 0)
             hP1
             (typeE_Lambda _ _ si_na (lift0 1 iv_kg) (tRel 0) (lift0 2 iv_kg)
                (iv_vass si_Σ _ si_na (lift0 1 iv_kg) sProp hkg1 eq_refl)
                (typeE_Rel _ _ 0 (vass si_na (lift0 1 iv_kg)) w2 eq_refl))
             (typeE_Rel _ _ 0 (vass si_na iv_kg) w1 eq_refl)). }
  have hP0 : si_Σ ;;; iv_Γk |-E tProd si_na iv_kg (lift0 1 iv_kg) : tSort (Sort.sort_of_product sProp sProp).
  { exact (typeE_Prod _ _ si_na iv_kg (lift0 1 iv_kg) sProp sProp (iv_vass_s si_Σ _ si_na iv_kg sProp hkg eq_refl)
             hkg1). }
  have hredex : si_Σ ;;; iv_Γk |-E sri_eta_redex : iv_kg.
  { exact (typeE_App _ _ (tLambda si_na iv_kg sri_eta_body) si_na iv_kg (lift0 1 iv_kg) _ (tRel 0) hP0
             (typeE_Lambda _ _ si_na iv_kg sri_eta_body (lift0 1 iv_kg)
                (iv_vass si_Σ _ si_na iv_kg sProp hkg eq_refl) hbody)
             iv_y_typed). }
  exact (typeE_Cumul _ _ sri_eta_redex iv_kg iv_keta sProp hredex iv_keta_typed iv_spec_eta).
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

(** [y → x] in [y := x : Prop, x : Prop] ([sri_ΔL]): the let [y] is [tRel 0] in the domain and the
    assumption [x] is [tRel 2] under the binder. *)
Definition sri_y_to_x : term := tProd si_na (tRel 0) (tRel 2).

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

(** [(λy:Prop. y) x] in [x : Prop]. *)
Definition sri_id_x : term := tApp iv_id (tRel 0).

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

(** The telescope [x : Prop, f : x → x], in which the type of [f] depends on [x]. *)
Definition sri_Δf : context := [vass si_na si_P; vass si_na (tProd si_na (tRel 0) (tRel 1))].

Lemma sri_wf_Δf : wf_localE si_Σ (List.rev sri_Δf).
Proof.
  have w := iv_wf_P si_Σ [] localenv_nil.
  have hx : si_Σ ;;; [vass si_na si_P] |-E tRel 0 : tSort sProp.
  { exact (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl). }
  have wx := iv_wf_vass si_Σ [vass si_na si_P] si_na (tRel 0) sProp w hx eq_refl.
  have hT : si_Σ ;;; [vass si_na si_P] |-E tProd si_na (tRel 0) (tRel 1) : tSort (Sort.sort_of_product sProp sProp).
  { exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp (iv_vass_s si_Σ _ si_na (tRel 0) sProp hx eq_refl)
             (typeE_Rel _ _ 1 (vass si_na si_P) wx eq_refl)). }
  exact (iv_wf_vass si_Σ [vass si_na si_P] si_na _ _ w hT eq_refl).
Qed.

(** [λz : (λx:Prop. x) (∀P:Prop. P). z], the identity on the β-redex. *)
Definition sri_idA : term := tLambda si_na sri_A (tRel 0).

Lemma sri_idA_typed : si_Σ ;;; [] |-E sri_idA : tProd si_na sri_A (lift0 1 sri_A).
Proof.
  exact (typeE_Lambda _ _ si_na sri_A (tRel 0) (lift0 1 sri_A)
           (iv_vass si_Σ [] si_na sri_A sProp (iv_app_typed si_Σ [] localenv_nil) eq_refl)
           (typeE_Rel _ _ 0 (vass si_na sri_A) sri_wf_Γz eq_refl)).
Qed.

(** [x → x] in [x : Prop]: the variable [x] occurs in the domain and under the binder. *)
Definition sri_x_to_x : term := tProd si_na (tRel 0) (tRel 1).

(** [x : Prop ⊢ (λy:Prop. y) (x → x) ≤ x → x], by β. *)
Definition sri_id_x_to_x : term := tApp iv_id sri_x_to_x.

Lemma sri_ws_id_x_to_x : ws_cumul_pbE Cumul si_Σ [vass si_na si_P] sri_id_x_to_x sri_x_to_x.
Proof.
  apply red_ws_cumul_pbE. split; [reflexivity|reflexivity|].
  exact (red1_red _ _ _ _ (red_beta si_Σ [vass si_na si_P] si_na si_P (tRel 0) sri_x_to_x)).
Qed.

(** The redex [(λx:Prop. x → x) (∀P:Prop. P)] ([sri_xx_redex]): its body [x → x] ([sri_x_to_x])
    uses [x]; its reduct is [(∀P:Prop. P) → ∀P:Prop. P] ([sri_xx_reduct]). *)
Definition sri_xx_lam : term := tLambda si_na si_P sri_x_to_x.
Definition sri_xx_redex : term := tApp sri_xx_lam iv_False.
Definition sri_xx_reduct : term := tProd si_na iv_False iv_False.

Lemma sri_xx_body_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ ,, vass si_na si_P |-E sri_x_to_x : si_P.
Proof.
  intros h.
  have w := iv_wf_P si_Σ Γ h.
  have hx : si_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 : tSort sProp.
  { exact (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl). }
  have wx := iv_wf_vass si_Σ _ si_na (tRel 0) sProp w hx eq_refl.
  exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp (iv_vass_s si_Σ _ si_na (tRel 0) sProp hx eq_refl)
           (typeE_Rel _ _ 1 (vass si_na si_P) wx eq_refl)).
Qed.

Lemma sri_xx_lam_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E sri_xx_lam : iv_PP.
Proof.
  intros h.
  exact (typeE_Lambda _ _ si_na si_P sri_x_to_x si_P (iv_vass si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl)
           (sri_xx_body_typed Γ h)).
Qed.

Lemma sri_xx_redex_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E sri_xx_redex : si_P.
Proof.
  intros h.
  exact (typeE_App _ _ sri_xx_lam si_na si_P si_P _ iv_False (iv_PP_typed si_Σ Γ h) (sri_xx_lam_typed Γ h)
           (iv_False_typed si_Σ Γ h)).
Qed.

Lemma sri_xx_redex_isType : isTypeE si_Σ [] sri_xx_redex.
Proof. exact (has_sort_isTypeE sProp (sri_xx_redex_typed [] localenv_nil)). Qed.

Lemma sri_xx_beta (Γ : context) : red1 si_Σ Γ sri_xx_redex sri_xx_reduct.
Proof. exact (red_beta si_Σ Γ si_na si_P sri_x_to_x iv_False). Qed.

Lemma sri_xx_cr1 (Γ : context) (cl : is_closed_context Γ) : closed_red1 si_Σ Γ sri_xx_redex sri_xx_reduct.
Proof. split; [exact cl|reflexivity|exact (sri_xx_beta Γ)]. Qed.

(** The context [z : (λx:Prop. x → x) (∀P:Prop. P)] and its step to [z : (∀P:Prop. P) → ∀P:Prop. P]. *)
Definition sri_Γxx : context := [vass si_na sri_xx_redex].

Lemma sri_wf_Γxx : wf_localE si_Σ sri_Γxx.
Proof. exact (iv_wf_vass si_Σ [] si_na sri_xx_redex sProp localenv_nil (sri_xx_redex_typed [] localenv_nil) eq_refl). Qed.

Lemma sri_zxx_typed : si_Σ ;;; sri_Γxx |-E tRel 0 : sri_xx_redex.
Proof. exact (typeE_Rel _ _ 0 (vass si_na sri_xx_redex) sri_wf_Γxx eq_refl). Qed.

Lemma sri_red_ctx_xx : red1_ctx si_Σ sri_Γxx [vass si_na sri_xx_reduct].
Proof. constructor. split; [reflexivity|exact (sri_xx_beta [])]. Qed.

(** The body [x → x] of the redex uses its variable [x] and is not the bare variable; the reduct is
    the body with [∀P:Prop. P] for [x], and it is neither the argument [∀P:Prop. P], nor the body,
    nor the redex. *)
Lemma sri_xx_nondeg :
  noccur_between 0 1 sri_x_to_x = false /\ sri_x_to_x <> tRel 0 /\
  subst1 iv_False 0 sri_x_to_x = sri_xx_reduct /\
  sri_xx_reduct <> iv_False /\ sri_xx_reduct <> sri_x_to_x /\ sri_xx_reduct <> sri_xx_redex.
Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

(** The context step moves the declaration; the body [x → x] of the redex uses its variable, and the
    new declaration type is neither the argument [∀P:Prop. P] nor the body. *)
Lemma sri_ctx_xx_nondeg :
  sri_Γxx <> [vass si_na sri_xx_reduct] /\ noccur_between 0 1 sri_x_to_x = false /\
  sri_xx_reduct <> iv_False /\ sri_xx_reduct <> sri_x_to_x.
Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

(** [z := ∀P:Prop. P : Prop, w : z → z] ([sri_x_to_x] at [x := z]): the let's variable [z]
    occurs in the domain and under the binder of [w]'s type. *)
Lemma sri_wf_let_x_to_x : wf_localE si_Σ ([] ,, vdef si_na iv_False si_P ,, vass si_na sri_x_to_x).
Proof.
  have wd := iv_wf_vdef si_Σ [] localenv_nil.
  have hz : si_Σ ;;; [] ,, vdef si_na iv_False si_P |-E tRel 0 : tSort sProp.
  { exact (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) wd eq_refl). }
  have wz := iv_wf_vass si_Σ _ si_na (tRel 0) sProp wd hz eq_refl.
  have hT : si_Σ ;;; [] ,, vdef si_na iv_False si_P |-E sri_x_to_x : tSort (Sort.sort_of_product sProp sProp).
  { exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp (iv_vass_s si_Σ _ si_na (tRel 0) sProp hz eq_refl)
             (typeE_Rel _ _ 1 (vdef si_na iv_False si_P) wz eq_refl)). }
  exact (iv_wf_vass si_Σ _ si_na _ _ wd hT eq_refl).
Qed.

(** [z → z] in [z := ∀P:Prop. P : Prop, w : z → z]: [z] is [tRel 1] in the domain and [tRel 2]
    under the binder. *)
Definition sri_z_to_z : term := tProd si_na (tRel 1) (tRel 2).

Lemma sri_z_to_z_isType : isTypeE si_Σ ([vdef si_na iv_False si_P] ,,, [vass si_na sri_x_to_x]) sri_z_to_z.
Proof.
  have ww := sri_wf_let_x_to_x.
  have hz1 : si_Σ ;;; [] ,, vdef si_na iv_False si_P ,, vass si_na sri_x_to_x |-E tRel 1 : tSort sProp.
  { exact (typeE_Rel _ _ 1 (vdef si_na iv_False si_P) ww eq_refl). }
  have wz := iv_wf_vass si_Σ _ si_na (tRel 1) sProp ww hz1 eq_refl.
  apply (has_sort_isTypeE (Sort.sort_of_product sProp sProp)).
  exact (typeE_Prod _ _ si_na (tRel 1) (tRel 2) sProp sProp (iv_vass_s si_Σ _ si_na (tRel 1) sProp hz1 eq_refl)
           (typeE_Rel _ _ 2 (vdef si_na iv_False si_P) wz eq_refl)).
Qed.

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

(** [land 1 : int → int], [land] applied to one of its two arguments. *)
Lemma sri_land_1_typed :
  Σ_po ;;; [] |-E mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63]) : tImpl sri_int sri_int.
Proof.
  destruct sri_land_ty_typed as [s hl].
  exact (typeE_App _ _ (tConst po_land_kn []) sri_iA sri_int (lift 1 0 (tImpl sri_int sri_int)) s
           (tPrim (prim_int 1%uint63)) hl iv_land_typed (sri_prim_typed 1%uint63)).
Qed.

Lemma sri_po_on_result : on_prim_op_result Σ_po SInt.
Proof. exists po_int_kn, po_int_body. split; [reflexivity|exact iv_po_declared_int|split; reflexivity]. Qed.

Lemma sri_tag_declared : prim_op_tag_declared Σ_po primInt.
Proof. exists po_int_kn, po_int_body. split; [reflexivity|exact iv_po_declared_int|split; reflexivity]. Qed.

(** In [Σ_po], [int63] is registered as [po_int_kn] ([int]), so [prim_shape_type] of [Σ_po]'s
    retroknowledge at [SInt] is [int]; and the constant body [po_int_body] has no body. *)
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

  (** [sr_red1E] (through [env_propE_typing]) at β on [(λx:Prop. x → x) (∀P:Prop. P)]
      ([sri_xx_redex_typed]), with [typing_closed_red1E] for the step [sri_xx_beta].
      TARGET PCUICSREta.sr_red1E
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
  Lemma sr_red1E_beta_inst : si_Σ ;;; [] |-E sri_xx_reduct : si_P.
  Proof.
    have ht := sri_xx_redex_typed [] localenv_nil.
    pose proof (env_propE_typing sr_red1E si_Σ si_wfE [] _ _ ht) as h.
    unfold SR_red1E in h.
    exact (h sri_xx_reduct (typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) ht (sri_xx_beta []))).
  Qed.

  (** The body of the redex uses its variable: substituting [∀P:Prop. P] or [y] for [z] in
      [sri_eta_body] gives two different terms. The reduct is neither the redex nor the bare
      variable [tRel 0]. [k g] is the declared type of [y] ([tRel 0] of [iv_Γk]), lifted by one,
      and the type [k (λx:Prop. g x)] the redex is typed at is not [k g]. *)
  Lemma subject_reduction1E_eta_inst_nondeg :
    subst1 iv_False 0 sri_eta_body <> subst1 (tRel 0) 0 sri_eta_body /\
    sri_eta_reduct <> sri_eta_redex /\ sri_eta_reduct <> tRel 0 /\
    option_map (fun d => lift0 1 (decl_type d)) (nth_error iv_Γk 0) = Some iv_kg /\ iv_kg <> iv_keta.
  Proof. split; [|split; [|split; [|split]]]; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** β on the redex [sri_eta_redex], whose body uses its variable, typed at [k (λx:Prop. g x)]
      through η ([sri_eta_redex_typed]).
      TARGET PCUICSREta.subject_reduction1E
      INSTANCE NONDEGEN PCUICSREtaInstances.subject_reduction1E_eta_inst_nondeg *)
  Lemma subject_reduction1E_eta_inst : si_Σ ;;; iv_Γk |-E sri_eta_reduct : iv_keta.
  Proof.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_eta_redex) (T := iv_keta)
             sri_eta_redex_typed sri_eta_step).
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

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
  Lemma subject_reductionE_inst : si_Σ ;;; [] |-E sri_xx_reduct : si_P.
  Proof.
    exact (subject_reductionE si_Σ [] sri_xx_redex sri_xx_reduct si_P si_wfE (sri_xx_redex_typed [] localenv_nil)
             (red1_red _ _ _ _ (sri_xx_beta []))).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
  Lemma subject_reduction1_closedE_inst : si_Σ ;;; [] |-E sri_xx_reduct : si_P.
  Proof.
    have ht := sri_xx_redex_typed [] localenv_nil.
    exact (subject_reduction1_closedE si_Σ [] sri_xx_redex sri_xx_reduct si_P si_wfE ht
             (typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) ht (sri_xx_beta []))).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
  Lemma subject_reduction_closedE_inst : si_Σ ;;; [] |-E sri_xx_reduct : si_P.
  Proof.
    have ht := sri_xx_redex_typed [] localenv_nil.
    exact (subject_reduction_closedE si_Σ [] sri_xx_redex sri_xx_reduct si_P si_wfE ht
             (typing_closed_redE (Σ := si_Σ) (wfΣ := si_wfE) ht (red1_red _ _ _ _ (sri_xx_beta [])))).
  Qed.

  (** The β step [sri_beta] of the typed redex [(λx:Prop. x) (∀P:Prop. P)], in the empty context.
      Its source and target differ ([sri_beta_nondeg]).
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Definition typing_closed_red1E_inst : closed_red1 si_Σ [] sri_A iv_False :=
    typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_A) (u := iv_False)
      (iv_app_typed si_Σ [] localenv_nil) (sri_beta []).

  (** The β step [sri_beta] as a reduction, in the context [z : (λx:Prop. x) (∀P:Prop. P)]. Its
      source and target differ ([sri_beta_nondeg]).
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_beta_nondeg *)
  Definition typing_closed_redE_inst : closed_red si_Σ sri_Γz sri_A iv_False :=
    typing_closed_redE (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_A) (u := iv_False)
      (iv_app_typed si_Σ sri_Γz sri_wf_Γz) (red1_red _ _ _ _ (sri_beta sri_Γz)).

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

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
  Lemma isType_red1E_inst : isTypeE si_Σ [] sri_xx_reduct.
  Proof.
    exact (isType_red1E (Σ := si_Σ) (wfΣ := si_wfE) (A := sri_xx_redex) sri_xx_redex_isType (sri_xx_beta [])).
  Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
  Lemma isType_redE_inst : isTypeE si_Σ [] sri_xx_reduct.
  Proof.
    exact (isType_redE (Σ := si_Σ) (wfΣ := si_wfE) sri_xx_redex_isType
             (red1_red _ _ sri_xx_redex sri_xx_reduct (sri_xx_beta []))).
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

  (** The body [z] of the let is declared at the redex [(λx:Prop. x → x) (∀P:Prop. P)] in
      [sri_Γxx], and the redex is not its reduct [(∀P:Prop. P) → ∀P:Prop. P], the new type of the
      let; the body of the redex uses its variable, and the reduct is neither the argument nor the
      body. *)
  Lemma lift_judgment_SRE_inst_nondeg :
    option_map (fun d => lift0 1 (decl_type d)) (nth_error sri_Γxx 0) = Some sri_xx_redex /\
    sri_xx_redex <> sri_xx_reduct /\ noccur_between 0 1 sri_x_to_x = false /\
    sri_xx_reduct <> iv_False /\ sri_xx_reduct <> sri_x_to_x.
  Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** The let [y := z : (λx:Prop. x → x) (∀P:Prop. P)] in [sri_Γxx], of sort [Prop], and the
      closed step [sri_xx_cr1] of its type to [(∀P:Prop. P) → ∀P:Prop. P], the body [z] kept (the
      left case of [on_one_decl], a step of the type).
      INSTANCE NONDEGEN PCUICSREtaInstances.lift_judgment_SRE_inst_nondeg *)
  Lemma lift_judgment_SRE_inst :
    lift_typing typingE si_Σ sri_Γxx (j_decl_s (mkdecl si_na (Some (tRel 0)) sri_xx_reduct) (Some sProp)).
  Proof.
    have hz := sri_zxx_typed.
    have hB := sri_xx_redex_typed sri_Γxx sri_wf_Γxx.
    apply (lift_judgment_SRE (Σ := si_Σ) (wfΣ := si_wfE) sri_Γxx si_na si_na (Some (tRel 0)) (Some (tRel 0))
             sri_xx_redex sri_xx_reduct (Some sProp)).
    - split.
      + split; [exact hz|].
        intros u r. exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) hz (closed_red1_red1 r)).
      + exists sProp. split; [|split; exact eq_refl].
        split; [exact hB|].
        intros u r. exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) hB (closed_red1_red1 r)).
    - split; [reflexivity|]. left. split; [exact (sri_xx_cr1 sri_Γxx eq_refl)|reflexivity].
  Qed.

  (** A β step in the declaration of the variable that the term is.
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_nondeg *)
  Lemma subject_reduction_ctxE_inst : si_Σ ;;; [vass si_na iv_False] |-E tRel 0 : sri_A.
  Proof.
    exact (subject_reduction_ctxE (Σ := si_Σ) (wfΣ := si_wfE) sri_Γz [vass si_na iv_False] (tRel 0) sri_A
             sri_red_ctx sri_z_typed).
  Qed.

  (** The context step [z : (λx:Prop. x → x) (∀P:Prop. P)] ⇝ [z : (∀P:Prop. P) → ∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_xx_nondeg *)
  Lemma wf_local_red1E_inst : wf_localE si_Σ [vass si_na sri_xx_reduct].
  Proof. exact (wf_local_red1E (Σ := si_Σ) (wfΣ := si_wfE) (Γ := sri_Γxx) sri_red_ctx_xx sri_wf_Γxx). Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.sri_ctx_xx_nondeg *)
  Lemma wf_local_redE_inst : wf_localE si_Σ [vass si_na sri_xx_reduct].
  Proof.
    exact (wf_local_redE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := sri_Γxx) (PCUICSR.red1_red_ctx si_Σ _ _ sri_red_ctx_xx)
             sri_wf_Γxx).
  Qed.

  (** Substituting the let's value [∀P:Prop. P] for [z] in [w : z → z] moves [w]'s type, and the
      resulting declaration is not [w : ∀P:Prop. P] (the type is not the substituted term). *)
  Lemma wf_local_subst1E_inst_nondeg :
    subst_context [iv_False] 0 [vass si_na sri_x_to_x] <> [vass si_na sri_x_to_x] /\
    subst_context [iv_False] 0 [vass si_na sri_x_to_x] <> [vass si_na iv_False].
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** [let z : Prop := ∀P:Prop. P, w : z → z] ([sri_wf_let_x_to_x]) gives
      [w : (∀P:Prop. P) → ∀P:Prop. P].
      INSTANCE NONDEGEN PCUICSREtaInstances.wf_local_subst1E_inst_nondeg *)
  Lemma wf_local_subst1E_inst : wf_localE si_Σ ([] ,,, subst_context [iv_False] 0 [vass si_na sri_x_to_x]).
  Proof.
    exact (wf_local_subst1E (Σ := si_Σ) (wfΣ := si_wfE) [] si_na iv_False si_P [vass si_na sri_x_to_x]
             sri_wf_let_x_to_x).
  Qed.

  (** [iv_Γk] is the declaration [tApp (tRel 0) (tRel 1)] (the [y : k g] of the header) on top of
      [[vass si_na iv_K; vass si_na iv_PP]] ([k : (Prop → Prop) → Prop], [g : Prop → Prop]). The
      type of that head declaration is open, so the lift by one moves it. *)
  Lemma wf_local_isType_nthE_inst_nondeg :
    iv_Γk = vass si_na (tApp (tRel 0) (tRel 1)) :: [vass si_na iv_K; vass si_na iv_PP] /\
    lift0 1 (decl_type (vass si_na (tApp (tRel 0) (tRel 1)))) <> decl_type (vass si_na (tApp (tRel 0) (tRel 1))).
  Proof. split; [reflexivity|intros h; vm_compute in h; discriminate h]. Qed.

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
    (* [pose proof], not ssreflect's [have :=], which would abstract the section's typeclass
       arguments instead of resolving them from the section's [Context]. *)
    pose proof (snd (isType_tLetInE (Σ := si_Σ) (HΣ' := si_wfE) (t := iv_False))
                  (iv_vdef_False si_Σ [] localenv_nil, sri_vdef_rel_isType)) as h.
    exact (h, fst (isType_tLetInE (Σ := si_Σ) (HΣ' := si_wfE)) h).
  Qed.

  (** *** Helpers of [sr_red1E]: projections, constructors, branches *)

  (** At the projection of the record [R] of [iv_Σ].
      INSTANCE IMPOSSIBLE: the conclusion mdecl = mdecl' /\ idecl = idecl' /\ cdecl = cdecl' compares the declarations that the two premises find for the same names (the inductive p.(proj_ind) and its constructor 0); declared_minductive is list membership, but under the wfE premise the environment's names are fresh, so the two finds agree (declared_inductive_to_gen, then declared_inductive_inj): in every well-formed environment the two sides are equal *)
  Lemma declared_projection_declared_constructorE_inst :
    iv_mdecl = iv_mdecl /\ iv_idecl = iv_idecl /\ iv_cdecl = iv_cdecl.
  Proof.
    exact (declared_projection_declared_constructorE (Σ := iv_Σ) (wfΣ := iv_wfE)
             iv_declared_projection iv_declared_constructor).
  Qed.

  (** At the projection of the record [R] of [iv_Σ].
      INSTANCE IMPOSSIBLE: under the wfE premise the inductive of a declared projection satisfies on_projections (on_declared_projectionE), whose field on_projs_noidx is #|ind_indices| = 0; so in every well-formed environment the conclusion #|ind_indices idecl| = 0 restates that field, for every declared projection *)
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
      INSTANCE NONDEGEN PCUICSREtaInstances.on_constructor_wf_argsE_inst_nondeg
      TARGET PCUICSREta.on_constructor_wf_argsE *)
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

  (** At the constructor [jc] of [J@{i}] of [PCUICEtaIdxEnv], with the universe instances [[Set]]
      ([ji_u0]) and [[a]] ([ji_u1]) and the premise [ji_cmp].
      INSTANCE IMPOSSIBLE: the conclusion compares the universe instances of a fully applied constructor, which global_variance_gen (PCUICEquality) compares AllIrrelevant when ind_variance = Some _ and AllEqual when ind_variance = None; by cmp_opt_variance the conclusion is then #|u| = #|u'| (which u = u' satisfies too) or, for a non-cumulative inductive, the premise itself (also AllEqual), so no instance relates two universe instances beyond its premise *)
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

  (** INSTANCE IMPOSSIBLE: the only premise is x = y, and Σ and Γ carry no premise at all, so every instance, in every environment and context, compares a term with itself
      TARGET PCUICSREta.conv_refl'E *)
  Definition conv_refl'E_inst : JoinE si_Σ [] Conv iv_False iv_False :=
    PCUICSREta.conv_refl'E (Σ := si_Σ) (Γ := []) eq_refl.

  (** INSTANCE IMPOSSIBLE: a Reflexive instance with no premise (Σ is any environment, with no wf premise), so every instance relates a context to itself *)
  Definition conv_context_reflE_inst := conv_context_reflE si_Σ sri_Γz.

  (** *** Helpers of [sr_red1E]: spines and substitutions *)

  (** The spine has a let, so its substitution is not the reversed instance; [Δ'] ([y → x]) uses
      both the let [y] and the assumption [x]; [expand_lets] moves [Δ']; and the substituted
      declaration is not [∀P:Prop. P], the entry of [sri_sL]. *)
  Lemma spine_subst_inst_substE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\
    noccur_between 0 1 sri_y_to_x = false /\ noccur_between 1 1 sri_y_to_x = false /\
    expand_lets_ctx sri_ΔL [vass si_na sri_y_to_x] <> [vass si_na sri_y_to_x] /\
    subst_context sri_sL 0 [vass si_na sri_y_to_x] <> [vass si_na iv_False].
  Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_substE_inst_nondeg *)
  Definition spine_subst_inst_substE_inst :=
    spine_subst_inst_substE (Δ := sri_ΔL) (Δ' := [vass si_na sri_y_to_x]) sri_spineL.

  (** As above, for the term [y → x]. *)
  Lemma spine_subst_inst_subst_termE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\
    noccur_between 0 1 sri_y_to_x = false /\ noccur_between 1 1 sri_y_to_x = false /\
    expand_lets sri_ΔL sri_y_to_x <> sri_y_to_x /\ subst sri_sL 0 sri_y_to_x <> iv_False.
  Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_subst_termE_inst_nondeg *)
  Definition spine_subst_inst_subst_termE_inst :=
    spine_subst_inst_subst_termE (Δ := sri_ΔL) (Δ' := sri_y_to_x) sri_spineL.

  (** As above, below one more binder ([k = 1]): [y] is [tRel 1] and [x] is [tRel 3] in
      [lift0 1 sri_y_to_x]. *)
  Lemma spine_subst_inst_subst_kE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\
    noccur_between 1 1 (lift0 1 sri_y_to_x) = false /\ noccur_between 2 1 (lift0 1 sri_y_to_x) = false /\
    expand_lets_k_ctx sri_ΔL 1 [vass si_na (lift0 1 sri_y_to_x)] <> [vass si_na (lift0 1 sri_y_to_x)] /\
    subst_context sri_sL 1 [vass si_na (lift0 1 sri_y_to_x)] <> [vass si_na iv_False].
  Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_subst_kE_inst_nondeg *)
  Definition spine_subst_inst_subst_kE_inst :=
    spine_subst_inst_subst_kE (Δ := sri_ΔL) (k := 1) (Δ' := [vass si_na (lift0 1 sri_y_to_x)]) sri_spineL.

  (** As above, for the term [lift0 1 sri_y_to_x] at [k = 1]. *)
  Lemma spine_subst_inst_subst_term_kE_inst_nondeg :
    sri_sL <> List.rev [iv_False] /\
    noccur_between 1 1 (lift0 1 sri_y_to_x) = false /\ noccur_between 2 1 (lift0 1 sri_y_to_x) = false /\
    expand_lets_k sri_ΔL 1 (lift0 1 sri_y_to_x) <> lift0 1 sri_y_to_x /\
    subst sri_sL 1 (lift0 1 sri_y_to_x) <> iv_False.
  Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_inst_subst_term_kE_inst_nondeg *)
  Definition spine_subst_inst_subst_term_kE_inst :=
    spine_subst_inst_subst_term_kE (Δ := sri_ΔL) (k := 1) (Δ' := lift0 1 sri_y_to_x) sri_spineL.

  (** The instance is not empty: the conclusion types a term. *)
  Lemma spine_subst_wt_termsE_inst_nondeg : [iv_False] <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.spine_subst_wt_termsE_inst_nondeg *)
  Definition spine_subst_wt_termsE_inst := spine_subst_wt_termsE (inst := [iv_False]) sri_spineL.

  (** Skipping one entry drops the let [y := x] of [sri_ΔL] and keeps the assumption [x : Prop]; of
      the substitution [sri_sL] it keeps neither all nor nothing. *)
  Lemma wf_subslet_skipnE_inst_nondeg :
    skipn 1 sri_sL <> sri_sL /\ skipn 1 sri_sL <> [] /\
    firstn 1 sri_ΔL = [vdef si_na (tRel 0) si_P] /\ skipn 1 sri_ΔL = [vass si_na si_P].
  Proof. split; [|split; [|split]]; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.wf_subslet_skipnE_inst_nondeg *)
  Definition wf_subslet_skipnE_inst := wf_subslet_skipnE (s := sri_sL) (Δ := sri_ΔL) (n := 1) sri_wf_subsletL.

  (** The two substitutions differ, and so do the two compared terms [T] and [U]. Each substituted
      result is not the substituted term ([T{0 := (λx:Prop. x) (∀P:Prop. P)}] is not
      [(λx:Prop. x) (∀P:Prop. P)], [U{0 := ∀P:Prop. P}] is not [∀P:Prop. P]), and [U] moves when
      [s] is replaced by [s']. *)
  Lemma substitution_ws_cumul_pb_subst_convE_inst_nondeg :
    [sri_A] <> [iv_False] /\ sri_id_x_to_x <> sri_x_to_x /\
    subst0 [sri_A] sri_id_x_to_x <> sri_A /\ subst0 [iv_False] sri_x_to_x <> iv_False /\
    subst0 [sri_A] sri_x_to_x <> subst0 [iv_False] sri_x_to_x.
  Proof. repeat split; intros h; vm_compute in h; discriminate h. Qed.

  (** [s = [(λx:Prop. x) (∀P:Prop. P)]] and [s' = [∀P:Prop. P]], one β step apart
      ([sri_terms_beta]); [T = (λy:Prop. y) (x → x)] ([sri_id_x_to_x]) and [U = x → x]
      ([sri_x_to_x]), one β step apart in [x : Prop] ([sri_ws_id_x_to_x]). The conclusion relates
      [T{0 := (λx:Prop. x) (∀P:Prop. P)}] and [U{0 := ∀P:Prop. P}].
      INSTANCE NONDEGEN PCUICSREtaInstances.substitution_ws_cumul_pb_subst_convE_inst_nondeg *)
  Lemma substitution_ws_cumul_pb_subst_convE_inst :
    si_Σ ;;; [] ⊢E subst0 [sri_A] sri_id_x_to_x ≤ subst0 [iv_False] sri_x_to_x.
  Proof.
    exact (substitution_ws_cumul_pb_subst_convE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := [])
             (s := [sri_A]) (s' := [iv_False]) (T := sri_id_x_to_x) (U := sri_x_to_x)
             sri_subslet_A sri_wf_subslet sri_terms_beta sri_ws_id_x_to_x).
  Qed.

  (** *** Helpers of [sr_red1E]: contexts and types *)

  (** The context added below is not empty. *)
  Lemma isType_weakenE_inst_nondeg : [vdef si_na iv_False si_P] <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.isType_weakenE_inst_nondeg
      TARGET PCUICSREta.isType_weakenE *)
  Definition isType_weakenE_inst :=
    PCUICSREta.isType_weakenE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := [vdef si_na iv_False si_P])
      (iv_wf_vdef si_Σ [] localenv_nil) sri_A_isType.

  (** Expanding the let [z := ∀P:Prop. P] below [w : z → z] moves [z → z] ([sri_z_to_z]) and
      [w]'s type [z → z] ([sri_x_to_x]), and neither result is the let's value [∀P:Prop. P]. *)
  Lemma isType_expand_letsE_inst_nondeg :
    expand_lets_k [vdef si_na iv_False si_P] #|[vass si_na sri_x_to_x]| sri_z_to_z <> sri_z_to_z /\
    expand_lets_k [vdef si_na iv_False si_P] #|[vass si_na sri_x_to_x]| sri_z_to_z <> iv_False /\
    expand_lets_ctx [vdef si_na iv_False si_P] [vass si_na sri_x_to_x] <> [vass si_na sri_x_to_x] /\
    expand_lets_ctx [vdef si_na iv_False si_P] [vass si_na sri_x_to_x] <> [vass si_na iv_False].
  Proof. repeat split; intros h; vm_compute in h; discriminate h. Qed.

  (** Expanding the let [z := ∀P:Prop. P] in [z → z] ([sri_z_to_z_isType]), below [w : z → z].
      INSTANCE NONDEGEN PCUICSREtaInstances.isType_expand_letsE_inst_nondeg *)
  Definition isType_expand_letsE_inst :=
    isType_expand_letsE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := [vdef si_na iv_False si_P])
      (Δ := [vass si_na sri_x_to_x]) (T := sri_z_to_z) sri_z_to_z_isType.

  (** The extended substitution of the let [z := ∀P:Prop. P], at depth one below [w : z → z],
      moves [z → z] ([sri_z_to_z]) and [w]'s type [z → z] ([sri_x_to_x]), and neither result is the
      let's value [∀P:Prop. P]. *)
  Lemma isType_subst_extended_substE_inst_nondeg :
    subst (extended_subst [vdef si_na iv_False si_P] 0) #|[vass si_na sri_x_to_x]| sri_z_to_z <> sri_z_to_z /\
    subst (extended_subst [vdef si_na iv_False si_P] 0) #|[vass si_na sri_x_to_x]| sri_z_to_z <> iv_False /\
    subst_context (extended_subst [vdef si_na iv_False si_P] 0) 0 [vass si_na sri_x_to_x] <>
      [vass si_na sri_x_to_x] /\
    subst_context (extended_subst [vdef si_na iv_False si_P] 0) 0 [vass si_na sri_x_to_x] <>
      [vass si_na iv_False].
  Proof. repeat split; intros h; vm_compute in h; discriminate h. Qed.

  (** The extended substitution of the let [z := ∀P:Prop. P] in [z → z] ([sri_z_to_z_isType]),
      below [w : z → z].
      INSTANCE NONDEGEN PCUICSREtaInstances.isType_subst_extended_substE_inst_nondeg *)
  Definition isType_subst_extended_substE_inst :=
    isType_subst_extended_substE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := [vdef si_na iv_False si_P])
      (Δ := [vass si_na sri_x_to_x]) (T := sri_z_to_z) sri_z_to_z_isType.

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

  (** The argument lists before and after the step differ, and so do the instantiated types of
      the second entry [f] at the two first arguments (the type of [f] depends on [x]). *)
  Lemma ctx_inst_mergeE_inst_nondeg :
    [sri_A; sri_idA] <> [iv_False; sri_idA] /\
    subst_telescope [sri_A] 0 (skipn 1 sri_Δf) <> subst_telescope [iv_False] 0 (skipn 1 sri_Δf).
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** The telescope [x : Prop, f : x → x] ([sri_Δf]) instantiated by
      [(λx:Prop. x) (∀P:Prop. P)] and [λz:(λx:Prop. x) (∀P:Prop. P). z] ([sri_idA]), with the
      closed step [sri_cr1] of the first argument to [∀P:Prop. P] as the [OnOne2] premise and
      [subject_reduction1E] as the reduction premise. The argument lists differ, and so do [f]'s
      instantiated types ([ctx_inst_mergeE_inst_nondeg]).
      INSTANCE NONDEGEN PCUICSREtaInstances.ctx_inst_mergeE_inst_nondeg *)
  Lemma ctx_inst_mergeE_inst : ctx_instE si_Σ [] [iv_False; sri_idA] sri_Δf.
  Proof.
    have ha := iv_app_typed si_Σ [] localenv_nil.
    apply (ctx_inst_mergeE (Σ := si_Σ) (wfΣ := si_wfE) [] [sri_A; sri_idA] [iv_False; sri_idA] sri_Δf).
    - exact sri_wf_Δf.
    - constructor; [|constructor; [|constructor]].
      + intros u r. exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) ha (closed_red1_red1 r)).
      + intros u r. exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) sri_idA_typed (closed_red1_red1 r)).
    - constructor; [exact ha|constructor; [exact sri_idA_typed|constructor]].
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

  (** The step is between open terms, so the lift moves both its source and its target. *)
  Lemma weakening_closed_red1_cb_inst_nondeg : lift 1 0 sri_id_x <> sri_id_x /\ lift 1 0 (tRel 0) <> tRel 0.
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

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

  (** [x → x] with [(λx:Prop. x) (∀P:Prop. P)] for [x] is not [(λx:Prop. x) (∀P:Prop. P)], [x → x]
      with [∀P:Prop. P] for [x] is not [∀P:Prop. P], and the two substituted terms differ. *)
  Lemma closed_red_red_subst0_cb_inst_nondeg :
    subst0 [sri_A] sri_x_to_x <> subst0 [iv_False] sri_x_to_x /\
    subst0 [sri_A] sri_x_to_x <> sri_A /\ subst0 [iv_False] sri_x_to_x <> iv_False.
  Proof. split; [|split]; intros h; vm_compute in h; discriminate h. Qed.

  (** The substitutions [[(λx:Prop. x) (∀P:Prop. P)]] and [[∀P:Prop. P]], related by the closed
      reduction [red1_red (sri_beta [])], substituted for [x] into [sri_x_to_x] ([x → x] in
      [x : Prop]).
      INSTANCE NONDEGEN PCUICSREtaInstances.closed_red_red_subst0_cb_inst_nondeg *)
  Lemma closed_red_red_subst0_cb_inst :
    closed_red si_Σ [] (subst0 [sri_A] sri_x_to_x) (subst0 [iv_False] sri_x_to_x).
  Proof.
    apply (closed_red_red_subst0_cb (Σ := si_Σ) (Γ := []) (Δ := [vass si_na si_P]) (s := [sri_A])
             (s' := [iv_False]) (b := sri_x_to_x));
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

  (** The spine [[1; 3]] is not empty, so the per-argument part of the lemma's conclusion is not
      vacuous. *)
  Lemma prim_app_typing_invE_inst_nondeg : map term_of_lit [LInt 1%uint63; LInt 3%uint63] <> [].
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** INSTANCE NONDEGEN PCUICSREtaInstances.prim_app_typing_invE_inst_nondeg *)
  Definition prim_app_typing_invE_inst :=
    prim_app_typing_invE (Σ := Σ_po) (wfΣ := iv_po_wfE) (args := map term_of_lit [LInt 1%uint63; LInt 3%uint63])
      Σ_po_registers sri_land_app_typed ltac:(cbn; lia).

  (** The spine [[1]] is not empty, and it is shorter than the tags [[primInt; primInt]] of
      [land]: the hypothesis of the second part of the lemma's conclusion holds. *)
  Lemma typing_spine_prim_argsE_inst_nondeg :
    map term_of_lit [LInt 1%uint63] <> [] /\ #|map term_of_lit [LInt 1%uint63]| < #|[primInt; primInt]|.
  Proof. split; [intros h; vm_compute in h; discriminate h|cbn; lia]. Qed.

  (** The spine [[1]] of the partial application [land 1 : int → int] ([sri_land_1_typed]), from
      [inversion_mkAppsE] and [inversion_ConstE]. The spine is not empty and shorter than the
      tags ([typing_spine_prim_argsE_inst_nondeg]).
      INSTANCE NONDEGEN PCUICSREtaInstances.typing_spine_prim_argsE_inst_nondeg *)
  Lemma typing_spine_prim_argsE_inst :
    (forall i a t, nth_error (map term_of_lit [LInt 1%uint63]) i = Some a -> nth_error [primInt; primInt] i = Some t ->
       ∑ A ty_a, [× PCUICPrimOpType.prim_tag_type po_retro t = Some ty_a,
                   Σ_po ;;; [] |-E a : A & Σ_po ;;; [] ⊢E A = ty_a]) ×
    (#|map term_of_lit [LInt 1%uint63]| < #|[primInt; primInt]| ->
       ∑ na A B, Σ_po ;;; [] ⊢E tProd na A B ≤ tImpl sri_int sri_int).
  Proof.
    destruct (inversion_mkAppsE (Σ := Σ_po) (wfΣ := iv_po_wfE) sri_land_1_typed) as [A [hA sp]].
    destruct (inversion_ConstE Σ_po iv_po_wfE hA) as (decl & _ & hd & _ & hle).
    assert (ed : decl = po_land_body).
    { destruct hd as [e|[e|[]]]; [injection e as ->; reflexivity|cbv in e; congruence]. }
    subst decl.
    exact (typing_spine_prim_argsE (Σ := Σ_po) (wfΣ := iv_po_wfE) (r := po_retro) (tags := [primInt; primInt])
             (res := sri_int) (T := tImpl sri_int sri_int) (args := map term_of_lit [LInt 1%uint63]) po_land_ty A
             eq_refl hle ltac:(cbn; lia) sp).
  Qed.

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

  (** At the primitive type [int] of [Σ_po].
      INSTANCE IMPOSSIBLE: the target's proof only unpacks and repacks its own premises (PCUICSREta.v:857-867): a case split on the tag t, the premise t <> primArray to discard primArray, the three fields of the premise primitive_invariants t d (the declared type is Set, d has no body, d is monomorphic), and the typing constructor typeE_Const on the premises wf_localE Σ Γ and declared_constant Σ kn d; so in every environment and context the conclusion isTypeE Σ Γ (tConst kn []) is the premises put together by one constructor, and no instance exercises more than its own premises *)
  Lemma isType_prim_tag_constantE_inst : isTypeE Σ_po [] sri_int.
  Proof.
    apply (isType_prim_tag_constantE (Σ := Σ_po) (wfΣ := iv_po_wfE) (t := primInt) (kn := po_int_kn)
             (d := po_int_body) localenv_nil);
      [discriminate|exact iv_po_declared_int|split; reflexivity].
  Qed.

  (** [land] is declared in [Σ_po] with the type [po_land_ty], which is [int → int → int]: the
      argument types build a product, which is not the result type [int]. *)
  Lemma isType_prim_arg_typesE_inst_nondeg :
    declared_constant Σ_po po_land_kn po_land_body /\ cst_type po_land_body = po_land_ty /\
    po_land_ty = tImpl sri_int (tImpl sri_int sri_int) /\ po_land_ty <> sri_int.
  Proof.
    split; [exact Σ_po_declared_land|split; [reflexivity|split; [reflexivity|]]].
    intros h; vm_compute in h; discriminate h.
  Qed.

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
