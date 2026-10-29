(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICSREta] (row T1)

  **The forecast classes are section variables.** Every lemma of [PCUICSREta] that uses a forecast
  fact takes the forecast classes as premises: T2a's [ValForecastCopy10/14/15/16]
  ([PCUICValidityEta]) and [SRForecastCopy10/12/14/15/16/18] ([PCUICSREta]). No instance of a class
  exists before its copy lands, so the instances below live in section [SRInstances], whose
  [Context] holds the ten classes, and APPLY the lemmas there. Everything else each instance needs
  (the environment, its [wfE], every typing derivation, every reduction step) is proved here or in
  [PCUICInversionEtaInstances], with no class.

  **The environments** ([PCUICCumulativitySpecEtaClosureInstances], [PCUICEtaPrimOpInstance],
  [PCUICInversionEtaInstances]):
  - [si_Σ]: [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE];
  - [Σ_po]: [int : Set], [land : int -> int -> int] registered as [Int63land], the primitive
    integers on [int], with [iv_po_wfE];
  - [iv_Σ]: [CoInductive R (A : Prop) : Prop := mkR { f : A }], with [iv_wfE];
  - [sri_c_Σ] (here): [Definition c : Prop := ∀P:Prop. P], with [sri_c_wf]/[sri_c_wfE];
  - [sri_arr_Σ] (here): [int : Set] and [array : Type@{u} -> Type@{u}] registered as the primitive
    integers and arrays, with [sri_arr_wf]/[sri_arr_wfE].

  **Coverage of the 17 premise lemmas of [sr_red1E].** Each [sr_red1E_<rule>] is APPLIED to
  concrete arguments in [sr_red1E_<rule>_inst]: a concrete derivation with that head, and every
  induction-hypothesis premise discharged by [sr_red1E] at the concrete sub-derivations
  ([sri_SR], [sri_Pj], [sri_conj], [sri_PΓ], [sri_glob]). "Step" means the instance applies the
  lemma's conclusion to that concrete closed step; "vacuous" means the term has no reduct, so the
  instance states the lemma's conclusion as such.

  | premise lemma | instance | why non-degenerate |
  |---|---|---|
  | [sr_red1E_Pj] | [sr_red1E_Pj_inst] | [z := (λx:Prop. x) (∀P:Prop. P) : Prop]; its term steps (β) |
  | [sr_red1E_ctx] | [sr_red1E_ctx_inst] | context [z : (λx. x) (∀P. P)] steps to [z : ∀P. P]; [All_local_env_over] on a transparent [wf_localE] |
  | [sr_red1E_Rel] | [sr_red1E_Rel_inst] | δ of the let-bound [z := ∀P:Prop. P] |
  | [sr_red1E_Sort] | [sr_red1E_Sort_inst] | IMPOSSIBLE (normal form): [red1] has no rule with [tSort] as the redex |
  | [sr_red1E_Prod] | [sr_red1E_Prod_inst] | the domain [(λx. x) (∀P. P)] steps |
  | [sr_red1E_Lambda] | [sr_red1E_Lambda_inst] | the domain of [λz:(λx. x) (∀P. P). z] steps |
  | [sr_red1E_LetIn] | [sr_red1E_LetIn_inst] | ζ on [let z : Prop := ∀P. P in z] |
  | [sr_red1E_App] | [sr_red1E_App_inst] | β on [(λx:Prop. x) (∀P:Prop. P)] |
  | [sr_red1E_Const] | [sr_red1E_Const_inst] | δ of [c := ∀P:Prop. P] in [sri_c_Σ] (a defined constant; [wf] proved: [sri_c_wf]) |
  | [sr_red1E_Ind] | [sr_red1E_Ind_inst] | IMPOSSIBLE (normal form): no [red1] rule with [tInd] as the redex |
  | [sr_red1E_Construct] | [sr_red1E_Construct_inst] | IMPOSSIBLE (normal form): no [red1] rule with [tConstruct] as the redex |
  | [sr_red1E_Case] | [sr_red1E_Case_inst] | ι on [match c x with c => c x end] |
  | [sr_red1E_Proj] | [sr_red1E_Proj_inst] | [f (mkR (∀P. P) z)] steps to [z] |
  | [sr_red1E_Fix] | [sr_red1E_Fix_inst] | body step [λx. (λy. y) x ⇝ λx. x] of [fix f (x : I (∀P. P)) := …] ([fix_red_body]) |
  | [sr_red1E_CoFix] | [sr_red1E_CoFix_inst] | body step [mkR (∀P. P) ((λy. y) z) ⇝ mkR (∀P. P) z] ([cofix_red_body]) |
  | [sr_red1E_Prim] | [sr_red1E_Prim_inst] | the array literal [[| (λx:int. x) 1 | 1 : int |]] in [sri_arr_Σ] steps by [array_red_val] (β on its element) |
  | [sr_red1E_Cumul] | [sr_red1E_Cumul_inst] | conversion by η ([k g ≤ k (λx. g x)], [cumul_eta_l]), then β |

  None of the 17 is left uncovered. 14 take a real step. The other 3 (Sort, Ind, Construct) are
  IMPOSSIBLE: [red1] has no rule whose redex has that head, so no reduct exists and the conclusion
  can only be vacuous.

  **Non-degeneracy.** Each subject-reduction instance takes a real reduction step of a term with a
  real typing derivation. The steps: β ([sr_red1E_beta_inst]), ζ ([subject_reduction1E_zeta_inst]),
  ι on a [match] ([subject_reduction1E_iota_inst]), fixpoint unfolding
  ([subject_reduction1E_fix_inst]), a β step in a declaration of the context
  ([subject_reduction_ctxE_inst]), β in a type ([type_reductionE_inst], [isType_redE_inst]) and
  in the domain of an arity ([isWfArity_red1E_inst]). [subject_reduction1E_eta_inst] reduces a term
  whose typing derivation goes through an η step: in [g : Prop → Prop, k : (Prop → Prop) → Prop,
  y : k g], the redex [(λz:Prop. y) (∀P:Prop. P)] is typed at [k (λx:Prop. g x)] because [y] is
  ([iv_rel_typed], a [typeE_Cumul] whose conversion is [cumul_eta_l]). *)

From Stdlib Require Import ssreflect ssrbool PrimInt63.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping
     PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICOnOne PCUICTyping
     PCUICCases PCUICCasesContexts PCUICEquality PCUICReduction PCUICConfluence PCUICWellScopedCumulativity
     PCUICPrimitiveRed PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions
     PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICWeakeningTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaPrimOpInstance
     PCUICInversionEta PCUICInversionEtaInstances PCUICValidityEta PCUICSREta.
From MetaRocq.PCUIC Require PCUICSR.
From MetaRocq.PCUIC Require PCUICWfUniverses.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Pieces, without any class *)

(** [(λx:Prop. x) (∀P:Prop. P)], a β-redex of type [Prop], and its step. *)
Definition sri_A : term := tApp iv_id iv_False.

Lemma sri_beta (Γ : context) : red1 si_Σ Γ sri_A iv_False.
Proof. exact (red_beta si_Σ Γ si_na si_P (tRel 0) iv_False). Qed.

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

(** [z := ∀P:Prop. P : Prop ⊢ z : Prop]. *)
Lemma sri_vdef_rel_isType : isTypeE si_Σ ([] ,, vdef si_na iv_False si_P) (tRel 0).
Proof.
  exact (has_sort_isTypeE sProp
           (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) (iv_wf_vdef si_Σ [] localenv_nil) eq_refl)).
Qed.

Lemma sri_rel_isType : isTypeE si_Σ [vass si_na si_P] (tRel 0).
Proof.
  exact (has_sort_isTypeE sProp (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P si_Σ [] localenv_nil) eq_refl)).
Qed.

Lemma sri_False_isType : isTypeE si_Σ [] iv_False.
Proof. exact (has_sort_isTypeE sProp (iv_False_typed si_Σ [] localenv_nil)). Qed.

(** A substitution and a spine: [(∀P:Prop. P)] for [x : Prop]. *)
Lemma sri_subslet : subsletE si_Σ [] [iv_False] [vass si_na si_P].
Proof. constructor; [constructor|exact (iv_False_typed si_Σ [] localenv_nil)]. Qed.

Lemma sri_wf_subslet : wf_subsletE si_Σ [] [iv_False] [vass si_na si_P].
Proof. split; [exact (iv_wf_P si_Σ [] localenv_nil)|exact sri_subslet]. Qed.

Lemma sri_spine : spine_substE si_Σ [] [iv_False] [iv_False] [vass si_na si_P].
Proof.
  constructor.
  - constructor.
  - exact (iv_wf_P si_Σ [] localenv_nil).
  - change [iv_False] with ([] ++ [iv_False]) at 1. constructor. constructor.
  - exact sri_subslet.
Qed.

Lemma sri_terms_refl : ws_cumul_pbE_terms si_Σ [] [iv_False] [iv_False].
Proof.
  constructor; [|constructor].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) (pb := Conv) [] iv_False sri_False_isType).
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

Lemma sri_land_isType : isTypeE Σ_po [] po_land_ty.
Proof. destruct sri_land_ty_typed as [s hl]. exact (has_sort_isTypeE s hl). Qed.

Lemma sri_po_on_result : on_prim_op_result Σ_po SInt.
Proof. exists po_int_kn, po_int_body. split; [reflexivity|exact iv_po_declared_int|split; reflexivity]. Qed.

Lemma sri_tag_declared : prim_op_tag_declared Σ_po primInt.
Proof. exists po_int_kn, po_int_body. split; [reflexivity|exact iv_po_declared_int|split; reflexivity]. Qed.

(** *** Pieces for the direct instances of the 17 premise lemmas *)

(** [z : (λx:Prop. x) (∀P:Prop. P)] with a TRANSPARENT [wf_localE] derivation, so that
    [All_local_env_over] can be built on it ([sr_red1E_ctx_inst]). *)
Definition sri_wfz_tu : lift_typing typingE si_Σ [] (j_vass si_na sri_A) :=
  iv_vass si_Σ [] si_na sri_A sProp (iv_app_typed si_Σ [] localenv_nil) eq_refl.

Definition sri_wfz : wf_localE si_Σ sri_Γz.
Proof. apply localenv_cons_abs; [constructor|exact sri_wfz_tu]. Defined.

(** ι as a closed step. *)
Lemma sri_iota_cr1 : closed_red1 si_Σ iv_Γ1 iv_match (iota_red 1 iv_mp [tRel 0] iv_br).
Proof. split; [reflexivity|reflexivity|exact sri_iota_red]. Qed.

(** [k g] in [iv_Γk], and the η-typed redex typed first at [k g] (the [Cumul] instance then
    moves it to [k (λx:Prop. g x)] by [iv_spec_eta]). *)
Lemma sri_kg_typed : si_Σ ;;; iv_Γk |-E iv_kg : si_P.
Proof. exact (weakeningE si_Σ iv_Γkg [vass si_na (tApp (tRel 0) (tRel 1))] _ _ si_wfE iv_wf_Γk iv_kg0_typed). Qed.

Lemma sri_eta_redex_kg : si_Σ ;;; iv_Γk |-E sri_eta_redex : iv_kg.
Proof.
  have w := iv_wf_P si_Σ iv_Γk iv_wf_Γk.
  have hy : si_Σ ;;; iv_Γk ,, vass si_na si_P |-E tRel 1 : lift0 1 iv_kg.
  { exact (weakeningE si_Σ iv_Γk [vass si_na si_P] (tRel 0) iv_kg si_wfE w iv_y_typed). }
  have hk : si_Σ ;;; iv_Γk ,, vass si_na si_P |-E lift0 1 iv_kg : tSort sProp.
  { exact (weakeningE si_Σ iv_Γk [vass si_na si_P] iv_kg si_P si_wfE w sri_kg_typed). }
  have hP := iv_P_typed si_Σ iv_Γk iv_wf_Γk.
  exact (typeE_App _ _ (tLambda si_na si_P (tRel 1)) si_na si_P (lift0 1 iv_kg) _ iv_False
           (typeE_Prod _ _ si_na si_P (lift0 1 iv_kg) _ sProp (iv_vass_s si_Σ iv_Γk si_na si_P _ hP eq_refl) hk)
           (typeE_Lambda _ _ si_na si_P (tRel 1) (lift0 1 iv_kg) (iv_vass si_Σ iv_Γk si_na si_P _ hP eq_refl) hy)
           (iv_False_typed si_Σ iv_Γk iv_wf_Γk)).
Qed.

(** [mkR (∀P:Prop. P) z : R (∀P:Prop. P)] in [z : ∀P:Prop. P], whose projection [f] steps to [z]. *)
Definition sri_mkRz : term := mkApps (tConstruct iv_ind 0 []) [iv_False; tRel 0].

Lemma sri_mkRz_typed : iv_Σ ;;; iv_Γc |-E sri_mkRz : mkApps (tInd (proj_ind iv_proj) []) [iv_False].
Proof.
  have hF := iv_False_typed iv_Σ iv_Γc iv_wf_Γc.
  have wF := iv_wf_vass iv_Σ iv_Γc iv_fna iv_False sProp iv_wf_Γc hF eq_refl.
  exact (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
           (Sort.sort_of_product sProp sProp) (tRel 0)
           (typeE_Prod _ _ iv_fna iv_False iv_RF sProp sProp
              (iv_vass_s iv_Σ iv_Γc iv_fna iv_False sProp hF eq_refl) (iv_RF_typed _ wF))
           (iv_mkRF_typed iv_Γc iv_wf_Γc)
           (typeE_Rel _ _ 0 (vass si_na iv_False) iv_wf_Γc eq_refl)).
Qed.

(** *** An environment with a defined constant: [Definition c : Prop := ∀P:Prop. P], for δ *)

Definition sri_c_kn : kername := (MPfile ["SRInst"], "c").
Definition sri_c_decl : constant_body :=
  {| cst_type := si_P; cst_body := Some iv_False; cst_universes := Monomorphic_ctx;
     cst_relevance := Relevant |}.
Definition sri_c_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(sri_c_kn, ConstantDecl sri_c_decl)];
     retroknowledge := Retroknowledge.empty |}.
Definition sri_c_Σ : global_env_ext := (sri_c_env, Monomorphic_ctx).

(** The body, in the empty environment the declaration is checked in (base typing). *)
Lemma sri_c_body_typed : si_Σ0 ;;; [] |- iv_False : si_P.
Proof.
  exact (type_Prod _ _ si_na si_P (tRel 0) (Sort.super sProp) sProp
           (si_vass_s [] si_na si_P _ (si_P_typed [] si_wf_nil) eq_refl)
           (type_Rel _ _ 0 (vass si_na si_P) (si_wf_P [] si_wf_nil) eq_refl)).
Qed.

(** [si_wf]'s proof, with the constant for the declaration. *)
Lemma sri_c_wf : wf sri_c_env.
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
    + cbn. split; [exact sri_c_body_typed|]. exists (Sort.super sProp). repeat split.
      exact (si_P_typed [] si_wf_nil).
    + cbn. intros op h; discriminate h.
Qed.

Definition sri_c_wfE : wfE sri_c_env := wf_incl_E sri_c_wf.

Lemma sri_c_declared : declared_constant sri_c_Σ sri_c_kn sri_c_decl.
Proof. now left. Qed.

(** *** A fixpoint with a β-redex in its body: [fix f (x : I (∀P. P)) := (λy. y) x] *)

Definition sri_idIF : term := tLambda si_na iv_IF (tRel 0).
Definition sri_fbody : term := tLambda si_na iv_IF (tApp sri_idIF (tRel 0)).
Definition sri_mfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_fix_ty; dbody := sri_fbody; rarg := 0 |}].

Lemma sri_idIF_typed (Γ : context) (h : wf_localE si_Σ Γ) : si_Σ ;;; Γ |-E sri_idIF : iv_fix_ty.
Proof.
  exact (typeE_Lambda _ _ si_na iv_IF (tRel 0) iv_IF (iv_vass si_Σ Γ si_na iv_IF sProp (iv_IF_typed Γ h) eq_refl)
           (typeE_Rel _ _ 0 (vass si_na iv_IF) (iv_wf_IF Γ h) eq_refl)).
Qed.

Lemma sri_fbody_typed : si_Σ ;;; iv_Γf |-E sri_fbody : lift0 1 iv_fix_ty.
Proof.
  have wx := iv_wf_IF iv_Γf iv_wf_Γf.
  have happ : si_Σ ;;; iv_Γf ,, vass si_na iv_IF |-E tApp sri_idIF (tRel 0) : iv_IF.
  { exact (typeE_App _ _ sri_idIF si_na iv_IF iv_IF _ (tRel 0) (iv_fix_ty_typed _ wx) (sri_idIF_typed _ wx)
             (typeE_Rel _ _ 0 (vass si_na iv_IF) wx eq_refl)). }
  exact (typeE_Lambda _ _ si_na iv_IF (tApp sri_idIF (tRel 0)) iv_IF
           (iv_vass si_Σ iv_Γf si_na iv_IF sProp (iv_IF_typed iv_Γf iv_wf_Γf) eq_refl) happ).
Qed.

Lemma sri_fix_guard : fix_guard si_Σ [] sri_mfix.
Proof.
  change (guard_cl Fix si_Σ [] sri_mfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma sri_wf_fix : wf_fixpointE si_Σ [] sri_mfix.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_fix_ty. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

(** The body step [λx. (λy. y) x ⇝ λx. x], as a step of the fixpoint: its reduct is [iv_mfix]. *)
Lemma sri_fix_body_cr1 : closed_red1 si_Σ [] (tFix sri_mfix 0) (tFix iv_mfix 0).
Proof.
  split; [reflexivity|reflexivity|].
  apply fix_red_body. constructor. split; [|reflexivity]. cbn.
  apply abs_red_r. exact (red_beta _ _ si_na iv_IF (tRel 0) (tRel 0)).
Qed.

(** *** A cofixpoint with a β-redex in its body: [cofix f := mkR (∀P. P) ((λy. y) z)] *)

Definition sri_idF : term := tLambda si_na iv_False (tRel 0).
Definition sri_cbody : term := tApp (tApp (tConstruct iv_ind 0 []) iv_False) (tApp sri_idF (tRel 1)).
Definition sri_cmfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_RF; dbody := sri_cbody; rarg := 0 |}].

Lemma sri_idF_typed (Γ : context) (h : wf_localE iv_Σ Γ) : iv_Σ ;;; Γ |-E sri_idF : tProd si_na iv_False iv_False.
Proof.
  have hF := iv_False_typed iv_Σ Γ h.
  exact (typeE_Lambda _ _ si_na iv_False (tRel 0) iv_False (iv_vass iv_Σ Γ si_na iv_False sProp hF eq_refl)
           (typeE_Rel _ _ 0 (vass si_na iv_False) (iv_wf_vass iv_Σ Γ si_na iv_False sProp h hF eq_refl) eq_refl)).
Qed.

Lemma sri_cbody_typed : iv_Σ ;;; iv_Γcf |-E sri_cbody : lift0 1 iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ iv_Γcf iv_wf_Γcf.
  have wF := iv_wf_vass iv_Σ iv_Γcf si_na iv_False sProp iv_wf_Γcf hF eq_refl.
  have harg : iv_Σ ;;; iv_Γcf |-E tApp sri_idF (tRel 1) : iv_False.
  { exact (typeE_App _ _ sri_idF si_na iv_False iv_False (Sort.sort_of_product sProp sProp) (tRel 1)
             (typeE_Prod _ _ si_na iv_False iv_False sProp sProp
                (iv_vass_s iv_Σ iv_Γcf si_na iv_False sProp hF eq_refl) (iv_False_typed iv_Σ _ wF))
             (sri_idF_typed iv_Γcf iv_wf_Γcf)
             (typeE_Rel _ _ 1 (vass si_na iv_False) iv_wf_Γcf eq_refl)). }
  have wF' := iv_wf_vass iv_Σ iv_Γcf iv_fna iv_False sProp iv_wf_Γcf hF eq_refl.
  exact (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
           (Sort.sort_of_product sProp sProp) (tApp sri_idF (tRel 1))
           (typeE_Prod _ _ iv_fna iv_False iv_RF sProp sProp
              (iv_vass_s iv_Σ iv_Γcf iv_fna iv_False sProp hF eq_refl) (iv_RF_typed _ wF'))
           (iv_mkRF_typed iv_Γcf iv_wf_Γcf) harg).
Qed.

Lemma sri_cofix_guard : cofix_guard iv_Σ iv_Γc sri_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ iv_Γc sri_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma sri_wf_cofix : wf_cofixpointE iv_Σ iv_Γc sri_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_RF. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

(** The body step [mkR (∀P. P) ((λy. y) z) ⇝ mkR (∀P. P) z]: the reduct is [iv_cmfix]. *)
Lemma sri_cofix_body_cr1 : closed_red1 iv_Σ iv_Γc (tCoFix sri_cmfix 0) (tCoFix iv_cmfix 0).
Proof.
  split; [reflexivity|reflexivity|].
  apply cofix_red_body. constructor. split; [|reflexivity]. cbn.
  apply app_red_r. exact (red_beta _ _ si_na iv_False (tRel 0) (tRel 1)).
Qed.

(** *** An environment with the primitive arrays registered, for [sr_red1E_Prim]

  [int : Set] (as in [Σ_po]) and [array : Type@{u} -> Type@{u}], polymorphic in one level with
  the primitive invariants of [primArray] ([array_uctx]), registered as the array type. *)

Definition sri_arr_kn : kername := (MPfile ["SRInst"], "array").
Definition sri_s : sort := sType (Universe.make' (Level.lvar 0)).
Definition sri_arr_decl : constant_body :=
  {| cst_type := tImpl (tSort sri_s) (tSort sri_s); cst_body := None;
     cst_universes := Polymorphic_ctx array_uctx; cst_relevance := Relevant |}.
Definition sri_arr_retro : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := Some po_int_kn;
     Retroknowledge.retro_float64 := None;
     Retroknowledge.retro_string := None;
     Retroknowledge.retro_array := Some sri_arr_kn;
     Retroknowledge.retro_ops := [];
     Retroknowledge.retro_bool := None |}.
Definition sri_arr_pre : global_env :=
  {| universes := po_univs; declarations := [(po_int_kn, ConstantDecl po_int_body)];
     retroknowledge := sri_arr_retro |}.
Definition sri_arr_env : global_env :=
  {| universes := po_univs;
     declarations := [(sri_arr_kn, ConstantDecl sri_arr_decl); (po_int_kn, ConstantDecl po_int_body)];
     retroknowledge := sri_arr_retro |}.
Definition sri_arr_Σ : global_env_ext := (sri_arr_env, Monomorphic_ctx).

Lemma sri_arr_retro_wf : Retroknowledge.wf_retro sri_arr_retro.
Proof.
  constructor; cbn.
  - constructor.
  - intros c [].
  - unfold Retroknowledge.types_distinct, Retroknowledge.disjoint_opt; cbn;
      repeat split; intros c H1 H2; cbv in H1, H2; congruence.
  - intros i [=].
Qed.

(** [po_udecl_ok]'s proof, for the polymorphic context [array_uctx] (level [lvar 0], no
    constraint). *)
Lemma sri_arr_udecl_ok : on_udecl po_univs (Polymorphic_ctx array_uctx).
Proof.
  repeat split; cbn.
  - intros l Hl Hg. apply LevelSetFact.mem_1 in Hl, Hg.
    destruct l as [|s|n]; vm_compute in Hl, Hg; discriminate.
  - intros i; rewrite ConstraintSetFact.empty_iff //.
  - red. rewrite /univs_ext_constraints /=. unshelve eexists.
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros c hc. apply ConstraintSetFact.union_iff in hc as [hc|hc]; inversion hc.
  - apply consistent_extension_on_empty.
Qed.

Lemma sri_arr_wfs : wf_sort (sri_arr_pre, Polymorphic_ctx array_uctx) sri_s.
Proof.
  simpl. intros l hin%LevelExprSet.singleton_spec. subst l. simpl.
  apply LevelSetFact.mem_2. vm_compute. reflexivity.
Qed.

(** [array]'s type [Type@{u} -> Type@{u}], under its universe context (base typing). *)
Lemma sri_arr_ty_typed :
  (sri_arr_pre, Polymorphic_ctx array_uctx) ;;; [] |- tImpl (tSort sri_s) (tSort sri_s)
    : tSort (Sort.sort_of_product (Sort.super sri_s) (Sort.super sri_s)).
Proof.
  have hs : forall Γ, wf_local (sri_arr_pre, Polymorphic_ctx array_uctx) Γ ->
      (sri_arr_pre, Polymorphic_ctx array_uctx) ;;; Γ |- tSort sri_s : tSort (Sort.super sri_s).
  { intros Γ h. apply type_Sort; [exact h|exact sri_arr_wfs]. }
  have hj : lift_typing typing (sri_arr_pre, Polymorphic_ctx array_uctx) []
              (j_vass_s sri_iA (tSort sri_s) (Sort.super sri_s)).
  { split; [exact tt|]. exists (Sort.super sri_s). split; [exact (hs [] localenv_nil)|].
    split; reflexivity. }
  have w1 : wf_local (sri_arr_pre, Polymorphic_ctx array_uctx) [vass sri_iA (tSort sri_s)].
  { constructor; [constructor|]. eapply lift_sorting_forget_univ, hj. }
  unfold tImpl. apply type_Prod; [exact hj|]. exact (hs _ w1).
Qed.

(** [Σ_po_wf]'s proof, with the array type in place of [land]. *)
Lemma sri_arr_wf : wf sri_arr_env.
Proof.
  split; [exact po_univs_ok|]. split; [exact sri_arr_retro_wf|].
  cbn. constructor.
  - constructor; [constructor|].
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - econstructor.
    + constructor; [intros [=]|constructor].
    + exact sri_arr_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.sort_of_product (Sort.super sri_s) (Sort.super sri_s)).
      repeat split. exact sri_arr_ty_typed.
    + cbn. intros op hop. discriminate hop.
Qed.

Definition sri_arr_wfE : wfE sri_arr_env := wf_incl_E sri_arr_wf.

Lemma sri_arr_declared : declared_constant sri_arr_Σ sri_arr_kn sri_arr_decl.
Proof. now left. Qed.

Lemma sri_arr_int_declared : declared_constant sri_arr_Σ po_int_kn po_int_body.
Proof. right; left; reflexivity. Qed.

Lemma sri_arr_int_typed (Γ : context) (h : wf_localE sri_arr_Σ Γ) :
  sri_arr_Σ ;;; Γ |-E sri_int : tSort (sType (Universe.make' Level.lzero)).
Proof. exact (typeE_Const _ _ po_int_kn [] po_int_body h sri_arr_int_declared eq_refl). Qed.

Lemma sri_arr_one_typed (Γ : context) (h : wf_localE sri_arr_Σ Γ) :
  sri_arr_Σ ;;; Γ |-E tPrim (prim_int 1%uint63) : sri_int.
Proof.
  refine (typeE_Prim sri_arr_Σ Γ (prim_int 1%uint63) po_int_kn po_int_body h eq_refl sri_arr_int_declared _ _).
  - split; reflexivity.
  - constructor.
Qed.

(** [(λx:int. x) 1 : int], the array element that steps. *)
Definition sri_arr_idint : term := tLambda sri_iA sri_int (tRel 0).
Definition sri_arr_redex : term := tApp sri_arr_idint (tPrim (prim_int 1%uint63)).

Lemma sri_arr_redex_typed (Γ : context) (h : wf_localE sri_arr_Σ Γ) : sri_arr_Σ ;;; Γ |-E sri_arr_redex : sri_int.
Proof.
  have hi := sri_arr_int_typed Γ h.
  have w := iv_wf_vass sri_arr_Σ Γ sri_iA sri_int _ h hi eq_refl.
  have hi' := sri_arr_int_typed _ w.
  exact (typeE_App _ _ sri_arr_idint sri_iA sri_int sri_int _ (tPrim (prim_int 1%uint63))
           (typeE_Prod _ _ sri_iA sri_int sri_int _ _ (iv_vass_s sri_arr_Σ Γ sri_iA sri_int _ hi eq_refl) hi')
           (typeE_Lambda _ _ sri_iA sri_int (tRel 0) sri_int (iv_vass sri_arr_Σ Γ sri_iA sri_int _ hi eq_refl)
              (typeE_Rel _ _ 0 (vass sri_iA sri_int) w eq_refl))
           (sri_arr_one_typed Γ h)).
Qed.

(** The array literal [[| v | 1 : int |]] at level [Set]. *)
Definition sri_arr (v : term) : array_model term :=
  {| array_level := Level.lzero; array_type := sri_int; array_default := tPrim (prim_int 1%uint63);
     array_value := [v] |}.
Definition sri_arr_p (v : term) : prim_val := (primArray; primArrayModel (sri_arr v)).

Section SRInstances.

  (** The forecast classes: section variables (see the header). *)
  Context {V10 : ValForecastCopy10} {V14 : ValForecastCopy14} {V15 : ValForecastCopy15}
    {V16 : ValForecastCopy16} {F10 : SRForecastCopy10}
    {F12 : SRForecastCopy12} {F14 : SRForecastCopy14} {F15 : SRForecastCopy15}
    {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}.

  (** *** [sr_red1E] and its corollaries *)

  (** [sr_red1E] (through [env_propE_typing]) at β, with [typing_closed_red1E] for the step. *)
  Lemma sr_red1E_beta_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    have ht := iv_app_typed si_Σ [] localenv_nil.
    pose proof (env_propE_typing sr_red1E si_Σ si_wfE [] _ _ ht) as h.
    unfold SR_red1E in h.
    exact (h iv_False (typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) ht (sri_beta []))).
  Qed.

  (** β on a term typed through η. *)
  Lemma subject_reduction1E_eta_inst : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta.
  Proof.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) sri_eta_redex_typed
             (red_beta si_Σ iv_Γk si_na si_P (tRel 1) iv_False)).
  Qed.

  (** ζ: [let z : Prop := ∀P:Prop. P in z] ⇝ [∀P:Prop. P]. *)
  Lemma subject_reduction1E_zeta_inst : si_Σ ;;; [] |-E iv_False : tLetIn si_na iv_False si_P si_P.
  Proof.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) (iv_let_typed si_Σ [] localenv_nil)
             (red_zeta si_Σ [] si_na iv_False si_P (tRel 0))).
  Qed.

  (** ι on the [match] of [PCUICInversionEtaInstances]. *)
  Lemma subject_reduction1E_iota_inst : si_Σ ;;; iv_Γ1 |-E iv_disc : iv_match_ty.
  Proof.
    rewrite -sri_iota_reduct.
    exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) iv_match_typed sri_iota_red).
  Qed.

  (** Fixpoint unfolding. *)
  Lemma subject_reduction1E_fix_inst :
    si_Σ ;;; [] |-E mkApps (tLambda si_na iv_IF (tRel 0)) [sri_cF] : iv_IF.
  Proof. exact (subject_reduction1E (Σ := si_Σ) (wfΣ := si_wfE) sri_fix_app_typed sri_fix_red). Qed.

  Lemma subject_reductionE_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    exact (subject_reductionE si_Σ [] sri_A iv_False si_P si_wfE (iv_app_typed si_Σ [] localenv_nil)
             (red1_red _ _ _ _ (sri_beta []))).
  Qed.

  Lemma subject_reduction1_closedE_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    have ht := iv_app_typed si_Σ [] localenv_nil.
    exact (subject_reduction1_closedE si_Σ [] sri_A iv_False si_P si_wfE ht
             (typing_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) ht (sri_beta []))).
  Qed.

  Lemma subject_reduction_closedE_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    have ht := iv_app_typed si_Σ [] localenv_nil.
    exact (subject_reduction_closedE si_Σ [] sri_A iv_False si_P si_wfE ht
             (typing_closed_redE (Σ := si_Σ) (wfΣ := si_wfE) ht (red1_red _ _ _ _ (sri_beta [])))).
  Qed.

  (** *** Reduction of the type *)

  Lemma type_reductionE_inst : si_Σ ;;; sri_Γz |-E tRel 0 : iv_False.
  Proof.
    exact (type_reductionE (Σ := si_Σ) (wfΣ := si_wfE) sri_z_typed (red1_red _ _ _ _ (sri_beta sri_Γz))).
  Qed.

  Lemma type_reduction_closedE_inst : si_Σ ;;; sri_Γz |-E tRel 0 : iv_False.
  Proof.
    exact (type_reduction_closedE (Σ := si_Σ) (wfΣ := si_wfE) sri_z_typed
             (typing_closed_redE (Σ := si_Σ) (wfΣ := si_wfE) (iv_app_typed si_Σ sri_Γz sri_wf_Γz)
                (red1_red _ _ _ _ (sri_beta sri_Γz)))).
  Qed.

  (** *** Section [SRContextE] *)

  Lemma isType_red1E_inst : isTypeE si_Σ [] iv_False.
  Proof. exact (isType_red1E (Σ := si_Σ) (wfΣ := si_wfE) sri_A_isType (sri_beta [])). Qed.

  Lemma isType_redE_inst : isTypeE si_Σ [] iv_False.
  Proof. exact (isType_redE (Σ := si_Σ) (wfΣ := si_wfE) sri_A_isType (red1_red _ _ _ _ (sri_beta []))). Qed.

  Lemma isWfArity_red1E_inst : isWfArityE si_Σ [] (tProd si_na iv_False si_P).
  Proof. exact (isWfArity_red1E (Σ := si_Σ) (wfΣ := si_wfE) sri_arity_wf sri_arity_red). Qed.

  Lemma isWfArity_redE_inst : isWfArityE si_Σ [] (tProd si_na iv_False si_P).
  Proof. exact (isWfArity_redE (Σ := si_Σ) (wfΣ := si_wfE) sri_arity_wf (red1_red _ _ _ _ sri_arity_red)). Qed.

  (** A β step in the declaration of the variable that the term is. *)
  Lemma subject_reduction_ctxE_inst : si_Σ ;;; [vass si_na iv_False] |-E tRel 0 : sri_A.
  Proof.
    exact (subject_reduction_ctxE (Σ := si_Σ) (wfΣ := si_wfE) sri_Γz [vass si_na iv_False] (tRel 0) sri_A
             sri_red_ctx sri_z_typed).
  Qed.

  Lemma wf_local_red1E_inst : wf_localE si_Σ [vass si_na iv_False].
  Proof. exact (wf_local_red1E (Σ := si_Σ) (wfΣ := si_wfE) sri_red_ctx sri_wf_Γz). Qed.

  Lemma wf_local_redE_inst : wf_localE si_Σ [vass si_na iv_False].
  Proof.
    exact (wf_local_redE (Σ := si_Σ) (wfΣ := si_wfE) (PCUICSR.red1_red_ctx si_Σ _ _ sri_red_ctx) sri_wf_Γz).
  Qed.

  (** [let z : Prop := ∀P:Prop. P, w : z] gives [w : ∀P:Prop. P]. *)
  Lemma wf_local_subst1E_inst : wf_localE si_Σ ([] ,,, subst_context [iv_False] 0 [vass si_na (tRel 0)]).
  Proof.
    apply (wf_local_subst1E (Σ := si_Σ) (wfΣ := si_wfE) [] si_na iv_False si_P [vass si_na (tRel 0)]).
    have wd := iv_wf_vdef si_Σ [] localenv_nil.
    exact (iv_wf_vass si_Σ ([] ,, vdef si_na iv_False si_P) si_na (tRel 0) sProp wd
             (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) wd eq_refl) eq_refl).
  Qed.

  Lemma wf_local_isType_nthE_inst :
    ∑ s, si_Σ ;;; iv_Γk |-E lift0 1 (tApp (tRel 0) (tRel 1)) : tSort s.
  Proof.
    exact (wf_local_isType_nthE (Σ := si_Σ) (wfΣ := si_wfE) iv_Γk 0 (vass si_na (tApp (tRel 0) (tRel 1)))
             iv_wf_Γk eq_refl).
  Qed.

  (** *** [isType_tLetInE], both directions, at [let z : Prop := ∀P:Prop. P in z] *)

  Lemma isType_tLetInE_inst :
    isTypeE si_Σ [] (tLetIn si_na iv_False si_P (tRel 0)) ×
    (lift_typing typingE si_Σ [] (j_vdef si_na iv_False si_P) ×
     isTypeE si_Σ ([] ,, vdef si_na iv_False si_P) (tRel 0)).
  Proof.
    (* [pose proof], not ssreflect's [have :=], which would abstract the forecast-class holes
       instead of resolving them from the section's [Context]. *)
    pose proof (snd (isType_tLetInE (Σ := si_Σ) (HΣ' := si_wfE))
                  (iv_vdef_False si_Σ [] localenv_nil, sri_vdef_rel_isType)) as h.
    exact (h, fst (isType_tLetInE (Σ := si_Σ) (HΣ' := si_wfE)) h).
  Qed.

  (** *** Helpers of [sr_red1E]: projections, constructors, branches *)

  Lemma declared_projection_declared_constructorE_inst :
    iv_mdecl = iv_mdecl /\ iv_idecl = iv_idecl /\ iv_cdecl = iv_cdecl.
  Proof.
    exact (declared_projection_declared_constructorE (Σ := iv_Σ) (wfΣ := iv_wfE)
             iv_declared_projection iv_declared_constructor).
  Qed.

  Lemma declared_projection_indicesE_inst : #|ind_indices iv_idecl| = 0.
  Proof. exact (declared_projection_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_projection). Qed.

  (** [R (∀P:Prop. P)] is a type: its parameter spine. *)
  Definition isType_mkApps_Ind_proj_invE_inst :=
    isType_mkApps_Ind_proj_invE (Σ := iv_Σ) (Γ := []) (u := []) (pars := [iv_False]) iv_wfE
      iv_declared_projection (has_sort_isTypeE sProp (iv_RF_typed [] localenv_nil)).

  Definition on_constructor_wf_argsE_inst :=
    on_constructor_wf_argsE (Σ := si_Σ) (wfΣ := si_wfE) (u := []) si_declared_constructor eq_refl.

  Definition on_constructor_closed_indicesE_inst :=
    on_constructor_closed_indicesE (Σ := si_Σ) (wfΣ := si_wfE) si_declared_constructor.

  Definition on_constructor_wf_arities_pars_argsE_inst :=
    on_constructor_wf_arities_pars_argsE (Σ := si_Σ) (wfΣ := si_wfE) si_declared_constructor.

  Definition on_constructor_closed_indices_instE_inst :=
    on_constructor_closed_indices_instE (Σ := si_Σ) (wfΣ := si_wfE) (u := []) si_declared_constructor eq_refl.

  Lemma cmp_global_instance_cstr_irrelevantE_inst :
    cmp_global_instance si_Σ.1 (compare_universe si_Σ) Conv (ConstructRef si_ind 0)
      (ind_npars si_mdecl + context_assumptions (cstr_args si_cdecl)) [] [].
  Proof.
    apply (cmp_global_instance_cstr_irrelevantE (Σ := si_Σ) (wfΣ := si_wfE) si_declared_constructor).
    first [exact (si_cumul_Ind_univ Cumul _) | apply cmp_global_instance_refl; tc
          | (red; apply cmp_global_instance_refl; tc)].
  Qed.

  (** The branch of the [match] of [PCUICInversionEtaInstances]. *)
  Lemma wf_pre_case_branch_contextE_inst :
    wf_localE si_Σ (iv_Γ1 ,,, pre_case_branch_context si_ind si_mdecl (pparams iv_mp) (puinst iv_mp) si_cdecl).
  Proof.
    exact (wf_pre_case_branch_contextE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γ1) (p := iv_mp) (br := iv_br)
             si_declared_inductive iv_wf_br eq_refl iv_wf_Γ1).
  Qed.

  Lemma inst_case_branch_context_eqE_inst :
    eq_context_upto_names (inst_case_branch_context iv_mp iv_br)
      (pre_case_branch_context si_ind si_mdecl (pparams iv_mp) (puinst iv_mp) si_cdecl).
  Proof.
    apply (inst_case_branch_context_eqE (Σ := si_Σ) (wfΣ := si_wfE) (p := iv_mp) (br := iv_br) (ind := si_ind)
             (cdecl := si_cdecl) (proj1 si_declared_inductive) eq_refl).
    constructor.
  Qed.

  Definition conv_refl'E_inst : JoinE si_Σ [] Conv iv_False iv_False :=
    conv_refl'E (Σ := si_Σ) (Γ := []) eq_refl.

  Definition conv_context_reflE_inst := conv_context_reflE si_Σ sri_Γz.

  (** *** Helpers of [sr_red1E]: spines and substitutions *)

  Definition spine_subst_inst_substE_inst := spine_subst_inst_substE (Δ' := [vass si_na (tRel 0)]) sri_spine.
  Definition spine_subst_inst_subst_termE_inst := spine_subst_inst_subst_termE (Δ' := tRel 0) sri_spine.
  Definition spine_subst_inst_subst_kE_inst :=
    spine_subst_inst_subst_kE (k := 1) (Δ' := [vass si_na (tRel 1)]) sri_spine.
  Definition spine_subst_inst_subst_term_kE_inst := spine_subst_inst_subst_term_kE (k := 1) (Δ' := tRel 1) sri_spine.
  Definition spine_subst_wt_termsE_inst := spine_subst_wt_termsE sri_spine.
  Definition subsletE_open_terms_inst := subsletE_open_terms (Σ := si_Σ) (wfΣ := si_wfE) sri_subslet.
  Definition wf_subslet_skipnE_inst := wf_subslet_skipnE (n := 1) sri_wf_subslet.

  Lemma substitution_ws_cumul_pbE_subslet_inst : si_Σ ;;; [] ⊢E iv_False ≤ iv_False.
  Proof.
    have hr := isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) (pb := Cumul) [vass si_na si_P] (tRel 0)
                 sri_rel_isType.
    exact (substitution_ws_cumul_pbE_subslet (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Γ'' := []) sri_subslet hr).
  Qed.

  Lemma substitution_ws_cumul_pb_subst_convE_inst : si_Σ ;;; [] ⊢E iv_False ≤ iv_False.
  Proof.
    have hr := isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) (pb := Cumul) [vass si_na si_P] (tRel 0)
                 sri_rel_isType.
    exact (substitution_ws_cumul_pb_subst_convE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := [])
             sri_subslet sri_wf_subslet sri_terms_refl hr).
  Qed.

  (** *** Helpers of [sr_red1E]: contexts and types *)

  Definition isType_weakenE_inst :=
    isType_weakenE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (iv_wf_vdef si_Σ [] localenv_nil) sri_A_isType.

  (** Expanding the let [z := ∀P:Prop. P]. *)
  Definition isType_expand_letsE_inst :=
    isType_expand_letsE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := [vdef si_na iv_False si_P]) (Δ := []) sri_vdef_rel_isType.

  Definition isType_subst_extended_substE_inst :=
    isType_subst_extended_substE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := [vdef si_na iv_False si_P]) (Δ := [])
      sri_vdef_rel_isType.

  (** [X (∀P:Prop. P)] in the arities context becomes [I (∀P:Prop. P)]. *)
  Definition isType_subst_aritiesE_inst :=
    isType_subst_aritiesE (Σ := si_Σ) (wfΣ := si_wfE) (u := []) (Γ := []) si_declared_inductive eq_refl
      sri_Ia_isType.

  Lemma conv_context_smash_endE_inst :
    ws_cumul_ctx_pbE Conv si_Σ ([] ,,, smash_context [] [vdef si_na iv_False si_P])
      ([] ,,, smash_context [] [vdef si_na iv_False si_P]).
  Proof.
    have wd := iv_wf_vdef si_Σ [] localenv_nil.
    apply (conv_context_smash_endE (Σ := si_Σ) (wfΣ := si_wfE) [] [vdef si_na iv_False si_P]
             [vdef si_na iv_False si_P] wd wd).
    exact (ws_cumul_ctx_pbE_refl (Σ := si_Σ) _ (wf_local_closed_contextE (Σ := si_Σ) (wfΣ := si_wfE) wd)).
  Qed.

  (** *** Helpers of [sr_red1E]: closed reductions *)

  Definition closed_red1_it_mkLambda_or_LetIn_cb_inst :=
    closed_red1_it_mkLambda_or_LetIn_cb (Σ := si_Σ) (Γ := []) (Δ := [vass si_na si_P])
      (sri_cr1 ([] ,,, [vass si_na si_P]) eq_refl).

  Definition closed_red1_mkApps_left_cb_inst :=
    closed_red1_mkApps_left_cb (Σ := si_Σ) (ts := [iv_False]) (sri_cr1 [] eq_refl) eq_refl.

  Definition weakening_closed_red1_cb_inst :=
    weakening_closed_red1_cb (Σ := si_Σ) (Γ := []) (Γ' := []) (Γ'' := [vass si_na si_P])
      (sri_cr1 ([] ,,, []) eq_refl) eq_refl.

  (** The return clause [(λx:Prop. x) (∀P:Prop. P)] steps; so does the type of the branch. *)
  Lemma closed_red1_case_branch_type_cb_inst :
    let cb := case_branch_type si_ind si_mdecl si_idecl iv_mp iv_br sri_A 0 si_cdecl in
    let cb' := case_branch_type si_ind si_mdecl si_idecl iv_mp iv_br iv_False 0 si_cdecl in
    closed_red1 si_Σ (iv_Γ1 ,,, cb.1) cb.2 cb'.2.
  Proof.
    exact (closed_red1_case_branch_type_cb (Σ := si_Σ) (Γ := iv_Γ1) (ret := sri_A) (ret' := iv_False)
             (ind := si_ind) (mdecl := si_mdecl) (idecl := si_idecl) (k := 0) (cdecl := si_cdecl)
             (br := iv_br) (p := iv_mp) iv_wf_br eq_refl eq_refl (sri_cr1 iv_Γ1 eq_refl)).
  Qed.

  Lemma closed_red_red_subst0_cb_inst : closed_red si_Σ [] (subst0 [sri_A] (tRel 0)) (subst0 [iv_False] (tRel 0)).
  Proof.
    apply (closed_red_red_subst0_cb (Σ := si_Σ) (Δ := [vass si_na si_P])); [reflexivity| |repeat constructor|reflexivity].
    constructor; [|constructor].
    split; [reflexivity|reflexivity|exact (red1_red _ _ _ _ (sri_beta []))].
  Qed.

  Lemma red1_it_mkLambda_or_LetIn_ctx_cb_inst :
    red1 si_Σ [] (it_mkLambda_or_LetIn sri_Γz (tRel 0)) (it_mkLambda_or_LetIn [vass si_na iv_False] (tRel 0)).
  Proof.
    apply (red1_it_mkLambda_or_LetIn_ctx_cb (Σ := si_Σ) [] sri_Γz [vass si_na iv_False] (tRel 0)).
    constructor. split; [reflexivity|exact (sri_beta _)].
  Qed.

  Definition wt_closed_red1E_inst :=
    wt_closed_red1E (Σ := si_Σ) (wfΣ := si_wfE) (si_P; iv_app_typed si_Σ [] localenv_nil) (sri_beta []).

  (** *** [case_nondep_predicate_convE]: two different discriminees, one return clause that does not
      use it ([match] of [PCUICInversionEtaInstances]: [I x] for any discriminee). *)

  Definition case_nondep_predicate_convE_inst :=
    case_nondep_predicate_convE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := iv_Γ1) (ci := iv_ci) (mdecl := si_mdecl)
      (idecl := si_idecl) (p := iv_mp) (indices := []) (c := iv_disc) (c' := tRel 0) (ps := sProp)
      eq_refl iv_pret_typed eq_refl eq_refl eq_refl eq_refl.

  (** *** Primitive operations, in [Σ_po]: [land 1 3 ⇝ 1] *)

  Lemma sr_prim_opE_inst : Σ_po ;;; [] |-E tPrim (prim_int 1%uint63) : sri_int.
  Proof.
    exact (sr_prim_opE (Σ := Σ_po) (wfΣ := iv_po_wfE) (r := RInt 1%uint63) sri_land_app_typed
             Σ_po_registers Σ_po_declared_land po_land_1_3 eq_refl).
  Qed.

  Definition prim_app_typing_invE_inst :=
    prim_app_typing_invE (Σ := Σ_po) (wfΣ := iv_po_wfE) Σ_po_registers sri_land_app_typed ltac:(cbn; lia).

  Definition prim_op_head_typeE_inst :=
    prim_op_head_typeE (Σ := Σ_po) (wfΣ := iv_po_wfE) (Γ := []) (u := []) localenv_nil Σ_po_declared_land
      eq_refl Σ_po_registers
      (isType_ws_cumul_pbE_refl (Σ := Σ_po) (wfΣ := iv_po_wfE) (pb := Cumul) [] po_land_ty sri_land_isType).

  Lemma readback_typedE_inst : Σ_po ;;; [] |-E tPrim (prim_int 1%uint63) : sri_int.
  Proof.
    exact (readback_typedE (Σ := Σ_po) (wfΣ := iv_po_wfE) (s := SInt) (r := RInt 1%uint63) localenv_nil eq_refl
             sri_po_on_result eq_refl).
  Qed.

  Lemma isType_prim_shape_typeE_inst : isTypeE Σ_po [] sri_int.
  Proof.
    exact (isType_prim_shape_typeE (Σ := Σ_po) (wfΣ := iv_po_wfE) (s := SInt) localenv_nil eq_refl
             sri_po_on_result).
  Qed.

  Lemma isType_prim_tag_constantE_inst : isTypeE Σ_po [] sri_int.
  Proof.
    apply (isType_prim_tag_constantE (Σ := Σ_po) (wfΣ := iv_po_wfE) (t := primInt) (kn := po_int_kn)
             (d := po_int_body) localenv_nil);
      [discriminate|exact iv_po_declared_int|split; reflexivity].
  Qed.

  (** [int -> int -> int], the type of [land], from [int]. *)
  Lemma isType_prim_arg_typesE_inst : isTypeE Σ_po [] po_land_ty.
  Proof.
    apply (isType_prim_arg_typesE (Σ := Σ_po) (wfΣ := iv_po_wfE) (tags := [primInt; primInt]) (res := sri_int)
             localenv_nil).
    - intros t [<-|[<-|[]]]; discriminate.
    - constructor; [exact sri_tag_declared|constructor; [exact sri_tag_declared|constructor]].
    - reflexivity.
    - exact isType_prim_shape_typeE_inst.
  Qed.

  (** The spine of [land 1 3], from [inversion_mkAppsE] and [inversion_ConstE]. *)
  Lemma typing_spine_prim_arg_typesE_inst : Σ_po ;;; [] ⊢E sri_int ≤ sri_int.
  Proof.
    destruct (inversion_mkAppsE (Σ := Σ_po) (wfΣ := iv_po_wfE) sri_land_app_typed) as [A [hA sp]].
    destruct (inversion_ConstE Σ_po iv_po_wfE hA) as (decl & _ & hd & _ & hle).
    assert (ed : decl = po_land_body).
    { destruct hd as [e|[e|[]]]; [injection e as ->; reflexivity|cbv in e; congruence]. }
    subst decl.
    exact (typing_spine_prim_arg_typesE (Σ := Σ_po) (wfΣ := iv_po_wfE) (r := po_retro) (tags := [primInt; primInt])
             (res := sri_int) (ls := [LInt 1%uint63; LInt 3%uint63]) po_land_ty A eq_refl hle eq_refl sp).
  Qed.

  (** *** The 17 premise lemmas of [sr_red1E], each applied directly

    Each [sr_red1E_<rule>_inst] applies [sr_red1E_<rule>] to a concrete derivation with that
    head; every premise is proved here: the typing and judgment premises by concrete
    derivations, the induction-hypothesis premises ([P], [Pj], [PΓ], the global [Pj]) by
    [sr_red1E] at those sub-derivations ([sri_SR], [sri_Pj], [sri_conj], [sri_PΓ], [sri_glob]).
    Where the term has a reduct, the instance then applies the lemma's conclusion to a concrete
    closed step (the header's table). *)

  (* The environment is [(Σ, ud)], so that the [wfE] argument (stated over [Σ : global_env]) fixes
     [Σ] by unification at the call sites. *)
  Lemma sri_SR {Σ : global_env} {ud : universes_decl} (wfΣ : wfE Σ) {Γ t T} (h : (Σ, ud) ;;; Γ |-E t : T) :
    forall u, closed_red1 (Σ, ud) Γ t u -> (Σ, ud) ;;; Γ |-E u : T.
  Proof. exact (env_propE_typing sr_red1E (Σ, ud) wfΣ Γ t T h). Qed.

  Lemma sri_PΓ {Σ : global_env} {ud : universes_decl} (wfΣ : wfE Σ) {Γ t T} (h : (Σ, ud) ;;; Γ |-E t : T) :
    wf_localE (Σ, ud) Γ ×
    (forall Γ' Δ' Δ, Γ = Γ' ,,, Δ' ->
       OnOne2_local_env (fun Δ : context => on_one_decl (closed_red1 (Σ, ud) (Γ' ,,, Δ))) Δ' Δ ->
       wf_local_relE (Σ, ud) Γ' Δ).
  Proof. exact (sr_red1E (Σ, ud) wfΣ Γ t T h).2.1. Qed.

  Lemma sri_glob {Σ : global_env} {ud : universes_decl} (wfΣ : wfE Σ) {Γ t T} (h : (Σ, ud) ;;; Γ |-E t : T) :
    on_global_env cumulSpecE0
      (fun Σ Γ j => lift_typing0 (fun t T => Σ ;;; Γ |-E t : T × (forall u, closed_red1 Σ Γ t u -> Σ ;;; Γ |-E u : T)) j)
      Σ.
  Proof. exact (sr_red1E (Σ, ud) wfΣ Γ t T h).1. Qed.

  Lemma sri_Pj {Σ : global_env} {ud : universes_decl} (wfΣ : wfE Σ) {Γ j} (h : lift_typing typingE (Σ, ud) Γ j) :
    lift_typing0 (fun t T => (Σ, ud) ;;; Γ |-E t : T × (forall u, closed_red1 (Σ, ud) Γ t u -> (Σ, ud) ;;; Γ |-E u : T)) j.
  Proof. apply lift_typing_impl with (1 := h) => t T ht. split; [exact ht|exact (sri_SR wfΣ ht)]. Qed.

  Lemma sri_conj {Σ : global_env} {ud : universes_decl} (wfΣ : wfE Σ) {Γ j} (h : lift_typing typingE (Σ, ud) Γ j) :
    lift_typing_conj (typingE (Σ, ud)) (fun Γ t T => forall u, closed_red1 (Σ, ud) Γ t u -> (Σ, ud) ;;; Γ |-E u : T) Γ j.
  Proof. apply lift_typing_impl with (1 := h) => t T ht. split; [exact ht|exact (sri_SR wfΣ ht)]. Qed.

  (** Premise 1, the judgement predicate: [let z : Prop := (λx:Prop. x) (∀P:Prop. P)]; its term
      component then steps. *)
  Lemma sr_red1E_Pj_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    pose (hj := iv_vdef si_Σ [] si_na sri_A si_P _ (iv_app_typed si_Σ [] localenv_nil)
                  (iv_P_typed si_Σ [] localenv_nil) eq_refl).
    pose proof (sr_red1E_Pj si_Σ si_wfE [] (j_vdef si_na sri_A si_P) (sri_conj si_wfE hj)) as h.
    exact (h.1.2 iv_False (sri_cr1 [] eq_refl)).
  Qed.

  (** Premise 2, contexts: [z : (λx:Prop. x) (∀P:Prop. P)]; the context steps to [z : ∀P:Prop. P]. *)
  Lemma sr_red1E_ctx_inst : wf_local_relE si_Σ [] [vass si_na iv_False].
  Proof.
    refine ((sr_red1E_ctx si_Σ si_wfE sri_Γz sri_wfz _ _).2 [] sri_Γz [vass si_na iv_False] eq_refl _).
    - unfold sri_wfz. econstructor; [constructor|]. exact (sri_SR si_wfE sri_wfz_tu.2.π2.1).
    - apply localenv_cons_abs; [constructor|exact (sri_Pj si_wfE sri_wfz_tu)].
    - constructor. split; [reflexivity|exact (sri_cr1 ([] ,,, []) eq_refl)].
  Qed.

  (** Premise 3, variables: δ of the let-bound [z := ∀P:Prop. P]. *)
  Lemma sr_red1E_Rel_inst : si_Σ ;;; [vdef si_na iv_False si_P] |-E lift0 1 iv_False : lift0 1 si_P.
  Proof.
    pose (wd := iv_wf_vdef si_Σ [] localenv_nil).
    pose (ht := typeE_Rel _ _ 0 (vdef si_na iv_False si_P) wd eq_refl).
    refine (sr_red1E_Rel si_Σ si_wfE _ wd 0 (vdef si_na iv_False si_P) eq_refl (sri_PΓ si_wfE ht) _ _).
    split; [reflexivity|reflexivity|exact (red_rel si_Σ [vdef si_na iv_False si_P] 0 iv_False eq_refl)].
  Qed.

  (** Premise 4, sorts: [Prop] is a normal form, no reduct exists; the conclusion is vacuous. *)
  Lemma sr_red1E_Sort_inst :
    forall u, closed_red1 si_Σ [] (tSort sProp) u -> si_Σ ;;; [] |-E u : tSort (Sort.super sProp).
  Proof.
    exact (sr_red1E_Sort si_Σ si_wfE [] localenv_nil sProp
             (sri_PΓ si_wfE (iv_P_typed si_Σ [] localenv_nil)) ltac:(cbn; trivial)).
  Qed.

  (** Premise 5, products: the domain [(λx:Prop. x) (∀P:Prop. P)] steps. *)
  Lemma sr_red1E_Prod_inst :
    si_Σ ;;; [] |-E tProd si_na iv_False si_P : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
  Proof.
    pose (lt := iv_vass_s si_Σ [] si_na sri_A sProp (iv_app_typed si_Σ [] localenv_nil) eq_refl).
    pose (hb := iv_P_typed si_Σ sri_Γz sri_wf_Γz).
    refine (sr_red1E_Prod si_Σ si_wfE [] localenv_nil si_na sri_A si_P sProp (Sort.super sProp)
              (sri_PΓ si_wfE (iv_app_typed si_Σ [] localenv_nil)) lt (sri_Pj si_wfE lt) hb (sri_SR si_wfE hb) _ _).
    split; [reflexivity|reflexivity|exact sri_arity_red].
  Qed.

  (** Premise 6, λ-abstractions: the domain of [λz:(λx:Prop. x) (∀P:Prop. P). z] steps. *)
  Lemma sr_red1E_Lambda_inst : si_Σ ;;; [] |-E tLambda si_na iv_False (tRel 0) : tProd si_na sri_A sri_A.
  Proof.
    pose (lt := iv_vass si_Σ [] si_na sri_A sProp (iv_app_typed si_Σ [] localenv_nil) eq_refl).
    refine (sr_red1E_Lambda si_Σ si_wfE [] localenv_nil si_na sri_A (tRel 0) sri_A
              (sri_PΓ si_wfE (iv_app_typed si_Σ [] localenv_nil)) lt (sri_Pj si_wfE lt) sri_z_typed
              (sri_SR si_wfE sri_z_typed) _ _).
    split; [reflexivity|reflexivity|exact (abs_red_l _ _ si_na sri_A iv_False (tRel 0) (sri_beta []))].
  Qed.

  (** Premise 7, let-ins: ζ on [let z : Prop := ∀P:Prop. P in z]. *)
  Lemma sr_red1E_LetIn_inst : si_Σ ;;; [] |-E iv_False : tLetIn si_na iv_False si_P si_P.
  Proof.
    pose (wd := iv_wf_vdef si_Σ [] localenv_nil).
    pose (hb := typeE_Rel _ _ 0 (vdef si_na iv_False si_P) wd eq_refl).
    refine (sr_red1E_LetIn si_Σ si_wfE [] localenv_nil si_na iv_False si_P (tRel 0) (lift0 1 si_P)
              (sri_PΓ si_wfE (iv_P_typed si_Σ [] localenv_nil)) (iv_vdef_False si_Σ [] localenv_nil)
              (sri_Pj si_wfE (iv_vdef_False si_Σ [] localenv_nil)) hb (sri_SR si_wfE hb) _ _).
    split; [reflexivity|reflexivity|exact (red_zeta _ _ si_na iv_False si_P (tRel 0))].
  Qed.

  (** Premise 8, applications: β on [(λx:Prop. x) (∀P:Prop. P)]. *)
  Lemma sr_red1E_App_inst : si_Σ ;;; [] |-E iv_False : si_P.
  Proof.
    pose (hP := iv_PP_typed si_Σ [] localenv_nil).
    pose (hid := iv_id_typed si_Σ [] localenv_nil).
    pose (hF := iv_False_typed si_Σ [] localenv_nil).
    exact (sr_red1E_App si_Σ si_wfE [] localenv_nil iv_id si_na si_P si_P iv_False iv_sPP
             (sri_PΓ si_wfE hF) hP (sri_SR si_wfE hP) hid (sri_SR si_wfE hid) hF (sri_SR si_wfE hF)
             _ (sri_cr1 [] eq_refl)).
  Qed.

  (** Premise 9, constants: δ of [c := ∀P:Prop. P] in [sri_c_Σ]. *)
  Lemma sr_red1E_Const_inst : sri_c_Σ ;;; [] |-E subst_instance [] iv_False : subst_instance [] (cst_type sri_c_decl).
  Proof.
    pose (ht := typeE_Const sri_c_Σ [] sri_c_kn [] sri_c_decl localenv_nil sri_c_declared eq_refl).
    refine (sr_red1E_Const sri_c_Σ sri_c_wfE [] localenv_nil sri_c_kn [] sri_c_decl
              (sri_glob sri_c_wfE ht) (sri_PΓ sri_c_wfE ht) sri_c_declared eq_refl _ _).
    split; [reflexivity|reflexivity|exact (red_delta _ _ sri_c_kn sri_c_decl iv_False sri_c_declared [] eq_refl)].
  Qed.

  (** Premises 10 and 11, inductives and constructors: normal forms, no reduct exists ([red1] has
      no rule for [tInd] or [tConstruct]); the conclusions are vacuous. *)
  Lemma sr_red1E_Ind_inst :
    forall u, closed_red1 si_Σ [] (tInd si_ind []) u -> si_Σ ;;; [] |-E u : subst_instance [] (ind_type si_idecl).
  Proof.
    pose (h := iv_ind_typed [] localenv_nil).
    exact (sr_red1E_Ind si_Σ si_wfE [] localenv_nil si_ind [] si_mdecl si_idecl si_declared_inductive
             (sri_glob si_wfE h) (sri_PΓ si_wfE h) eq_refl).
  Qed.

  Lemma sr_red1E_Construct_inst :
    forall u, closed_red1 si_Σ [] (tConstruct si_ind 0 []) u ->
      si_Σ ;;; [] |-E u : type_of_constructor si_mdecl si_cdecl (si_ind, 0) [].
  Proof.
    pose (h := iv_cstr_typed [] localenv_nil).
    exact (sr_red1E_Construct si_Σ si_wfE [] localenv_nil si_ind 0 [] si_mdecl si_idecl si_cdecl
             si_declared_constructor (sri_glob si_wfE h) (sri_PΓ si_wfE h) eq_refl).
  Qed.

  (** Premise 12, case analyses: ι on the [match] of [PCUICInversionEtaInstances]. *)
  Lemma sr_red1E_Case_inst : si_Σ ;;; iv_Γ1 |-E iv_disc : iv_match_ty.
  Proof.
    rewrite -sri_iota_reduct.
    refine (sr_red1E_Case si_Σ si_wfE iv_Γ1 iv_wf_Γ1 iv_ci iv_mp iv_disc [iv_br] [] sProp si_mdecl si_idecl
              si_declared_inductive (sri_glob si_wfE iv_disc_typed) (sri_PΓ si_wfE iv_disc_typed) eq_refl
              (alpha_eq_reflexive (pcontext iv_mp)) iv_wf_mp eq_refl iv_wf_pctx iv_pret_typed
              (sri_SR si_wfE iv_pret_typed) (sri_PΓ si_wfE iv_pret_typed) _ eq_refl _
              iv_disc_typed (sri_SR si_wfE iv_disc_typed) eq_refl _ _ _ sri_iota_cr1).
    - reflexivity.
    - econstructor; [|constructor]. split; [exact iv_x_typed|exact (sri_SR si_wfE iv_x_typed)].
    - constructor; [exact iv_wf_br|constructor].
    - constructor; [|constructor]. split; [constructor|]. cbv zeta. split; [|split].
      + exact (sri_PΓ si_wfE iv_br_typed).
      + split; [exact iv_br_typed|exact (sri_SR si_wfE iv_br_typed)].
      + split; [exact iv_bty_typed|exact (sri_SR si_wfE iv_bty_typed)].
  Qed.

  (** Premise 13, projections: [f (mkR (∀P:Prop. P) z)] steps to [z]. *)
  Lemma sr_red1E_Proj_inst : iv_Σ ;;; iv_Γc |-E tRel 0 : iv_False.
  Proof.
    refine (sr_red1E_Proj iv_Σ iv_wfE iv_Γc iv_wf_Γc iv_proj sri_mkRz [] iv_mdecl iv_idecl iv_cdecl iv_pdecl
              iv_declared_projection [iv_False] (sri_glob iv_wfE sri_mkRz_typed) (sri_PΓ iv_wfE sri_mkRz_typed)
              sri_mkRz_typed (sri_SR iv_wfE sri_mkRz_typed) eq_refl _ _).
    split; [reflexivity|reflexivity|exact (red_proj iv_Σ iv_Γc iv_proj [iv_False; tRel 0] [] (tRel 0) eq_refl)].
  Qed.

  (** Premise 14, fixpoints: the body step of [fix f (x : I (∀P. P)) := (λy. y) x]. *)
  Lemma sr_red1E_Fix_inst : si_Σ ;;; [] |-E tFix iv_mfix 0 : iv_fix_ty.
  Proof.
    pose (lt := iv_vass si_Σ [] si_na iv_fix_ty _ (iv_fix_ty_typed [] localenv_nil) eq_refl).
    pose (lb := iv_vdef si_Σ iv_Γf si_na sri_fbody (lift0 1 iv_fix_ty) _ sri_fbody_typed
                  (iv_fix_ty_typed iv_Γf iv_wf_Γf) eq_refl).
    refine (sr_red1E_Fix si_Σ si_wfE [] localenv_nil sri_mfix 0 _ sri_fix_guard eq_refl
              (sri_PΓ si_wfE sri_fbody_typed) _ _ _ _ sri_wf_fix _ sri_fix_body_cr1).
    - constructor; [exact lt|constructor].
    - constructor; [exact (sri_Pj si_wfE lt)|constructor].
    - constructor; [exact lb|constructor].
    - constructor; [exact (sri_Pj si_wfE lb)|constructor].
  Qed.

  (** Premise 15, cofixpoints: the body step of [cofix f := mkR (∀P. P) ((λy. y) z)]. *)
  Lemma sr_red1E_CoFix_inst : iv_Σ ;;; iv_Γc |-E tCoFix iv_cmfix 0 : iv_RF.
  Proof.
    pose (lt := iv_vass iv_Σ iv_Γc si_na iv_RF sProp (iv_RF_typed iv_Γc iv_wf_Γc) eq_refl).
    pose (lb := iv_vdef iv_Σ iv_Γcf si_na sri_cbody (lift0 1 iv_RF) sProp sri_cbody_typed
                  (iv_RF_typed iv_Γcf iv_wf_Γcf) eq_refl).
    refine (sr_red1E_CoFix iv_Σ iv_wfE iv_Γc iv_wf_Γc sri_cmfix 0 _ sri_cofix_guard eq_refl
              (sri_PΓ iv_wfE sri_cbody_typed) _ _ _ _ sri_wf_cofix _ sri_cofix_body_cr1).
    - constructor; [exact lt|constructor].
    - constructor; [exact (sri_Pj iv_wfE lt)|constructor].
    - constructor; [exact lb|constructor].
    - constructor; [exact (sri_Pj iv_wfE lb)|constructor].
  Qed.

  (** Premise 16, primitive values: the array literal [[| (λx:int. x) 1 | 1 : int |]] steps by the
      array congruence [array_red_val] (β on its element). *)
  Lemma sr_red1E_Prim_inst :
    sri_arr_Σ ;;; [] |-E tPrim (sri_arr_p (tPrim (prim_int 1%uint63))) : prim_type (sri_arr_p sri_arr_redex) sri_arr_kn.
  Proof.
    pose (wlu := PCUICWfUniverses.wf_sort_type0 sri_arr_Σ : wf_universe sri_arr_Σ (Universe.make' Level.lzero)).
    pose (hty := sri_arr_int_typed [] localenv_nil).
    pose (hdef := sri_arr_one_typed [] localenv_nil).
    pose (hval := sri_arr_redex_typed [] localenv_nil).
    refine (sr_red1E_Prim sri_arr_Σ sri_arr_wfE [] localenv_nil (sri_arr_p sri_arr_redex) sri_arr_kn sri_arr_decl
              (sri_PΓ sri_arr_wfE hdef) eq_refl sri_arr_declared _ _ _ _ _).
    - split; reflexivity.
    - econstructor; [exact wlu|exact hty|exact hdef|constructor; [exact hval|constructor]].
    - econstructor; [exact wlu|exact (sri_SR sri_arr_wfE hty)|exact (sri_SR sri_arr_wfE hdef)|].
      constructor; [exact (sri_SR sri_arr_wfE hval)|constructor].
    - split; [reflexivity|reflexivity|].
      exact (array_red_val _ _ (sri_arr sri_arr_redex) [tPrim (prim_int 1%uint63)]
               ltac:(constructor; exact (red_beta _ _ sri_iA sri_int (tRel 0) (tPrim (prim_int 1%uint63))))).
  Qed.

  (** Premise 17, the conversion rule, at the η step: [(λz:Prop. y) (∀P:Prop. P) : k g] and
      [k g ≤ k (λx:Prop. g x)] ([iv_spec_eta], a [cumul_eta_l] step); the redex then steps. *)
  Lemma sr_red1E_Cumul_inst : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta.
  Proof.
    refine (sr_red1E_Cumul si_Σ si_wfE iv_Γk iv_wf_Γk sri_eta_redex iv_kg iv_keta sProp
              (sri_PΓ si_wfE iv_y_typed) sri_eta_redex_kg (sri_SR si_wfE sri_eta_redex_kg)
              iv_keta_typed (sri_SR si_wfE iv_keta_typed) iv_spec_eta _ _).
    split; [reflexivity|reflexivity|exact (red_beta si_Σ iv_Γk si_na si_P (tRel 1) iv_False)].
  Qed.

End SRInstances.
