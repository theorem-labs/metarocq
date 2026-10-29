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
    integers on [int], with [iv_po_wfE].

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
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICCasesContexts PCUICEquality PCUICReduction PCUICConfluence PCUICWellScopedCumulativity
     PCUICPrimitiveRed PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions
     PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICWeakeningTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaPrimOpInstance
     PCUICInversionEta PCUICInversionEtaInstances PCUICValidityEta PCUICSREta.
From MetaRocq.PCUIC Require PCUICSR.

Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.
Local Notation " Σ ;;; Γ ⊢E t = u " := (ws_cumul_pbE Conv Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  =  u") : type_scope.

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

End SRInstances.
