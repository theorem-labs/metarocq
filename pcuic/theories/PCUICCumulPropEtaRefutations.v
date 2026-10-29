(* Distributed under the terms of the MIT license. *)

(** * Refutations for the E copy of [PCUICCumulProp] (row T6)

  Each theorem takes a form that is FALSE over η as a hypothesis and derives [False]. They are
  kept on purpose, never removed as dead code: they are the counterexamples behind the choices
  of [PCUICCumulPropEta]. Every witness is typable over [typingE] in an environment proved
  [wf] and [wfE] (and [wf_ext]/[wf_extE] where the refuted form asks for it), except where
  said otherwise.

  - **The η rule of [cumul_propE] is necessary** (base [cumul_prop] kept as the target):
    - [cumul_pb_cumul_prop_baseE_false]: base [cumul_pb_cumul_prop] ([PCUICCumulProp.v:238])
      over [ws_cumul_pbE]. Witness ([PCUICWsCumulEtaCtx], [rf_witness_typed]): in the context
      [f : Prop → Prop], [λx:Prop. f x] and [f], related by one η step, both of type
      [Prop → Prop], both [red1]-normal; [eq_term_prop] never relates a λ and a variable.
    - [typing_leq_term_prop_baseE_false]: base [typing_leq_term_prop] ([:1243]) over [typingE]
      and [wfE], with base [cumul_prop] as conclusion, under [prop_sub_type = false] as base's
      section asks. Witness ([tw_witness_typed]): in the context
      [G : (Prop → Prop) → Prop, F : Prop → Prop, x : G F], the variable [x] has type [G F]
      ([typeE_Rel]) and type [G (λy:Prop. F y)] ([typeE_Cumul], one η step); [t = t' = x] are
      related by [compare_term]; the two types are [red1]-normal and not [eq_term_prop]-related.
  - **Reduct comparisons are false over η** (the [cumul_propE] forms of base's
    reduct-and-compare statements):
    - [cumul_prop_altE_false]: the left-to-right half of base [cumul_prop_alt] ([:248]) for
      [cumul_propE]. Witness: the pair of [cumul_pb_cumul_prop_baseE_false].
    - [cumul_prop_argsE_false]: base [cumul_prop_args] ([:639]) for [cumul_propE], at the
      singleton lists of the same pair.
  - **[cumul_ind_confluence]** ([:45]), over [ws_cumul_pbE] with its raw reduct
    [A ⇝ mkApps (tInd ind v') l'']: [cumul_ind_confluenceE_false] (the untyped E form) and
    [cumul_ind_confluenceE_typed_false] (the same with [A] well typed). Witness
    ([PCUICEtaIndInvRefutations]): [A := λx:Set. I@{a} x], typed at [Set → Set], related to
    [I@{a}] by one η step, [red1]-normal, never a spine. [A] is not typed at a SORT, so the
    form with [isTypeE Σ Γ A] is not refuted here; [cumul_ind_confluence] is DROPPED
    ([PCUICCumulPropEta] header). *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta
     PCUICWellScopedCumulativity PCUICConversion PCUICCumulProp
     PCUICEtaDefs PCUICEtaCanon PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaCtx
     PCUICEtaIndInvRefutations PCUICCumulPropEta.

(** ** [λx:Prop. f x] and [f] *)

Lemma rf_cumul_propE : rf_Σ ;;; rf_Γ |-E rf_t ~~ tRel 0.
Proof. exact (cumul_pb_cumul_propE rf_Σ rf_Γ Conv rf_t (tRel 0) rf_premise). Qed.

(** The two terms have no common reduct related by [eq_term_prop]. *)
Lemma rf_no_eq_term_prop_reducts (Σ : global_env_ext) nf nf' :
  Σ ;;; rf_Γ ⊢ rf_t ⇝ nf -> Σ ;;; rf_Γ ⊢ tRel 0 ⇝ nf' -> eq_term_prop Σ 0 nf nf' -> False.
Proof.
  intros r r' e.
  have e1 := rt_from_normal _ _ _ (rf_t_normal Σ) (clrel_rel r).
  have e2 := rt_from_normal _ _ _ (rf_f_normal Σ) (clrel_rel r').
  subst nf nf'. depelim e.
Qed.

(** **Refuted:** base [cumul_pb_cumul_prop] ([PCUICCumulProp.v:238]) over [ws_cumul_pbE], with
    base [cumul_prop] kept as the conclusion. Base has no environment premise; neither has
    this form. *)
Theorem cumul_pb_cumul_prop_baseE_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (Γ : context) (pb : conv_pb) (A B : term),
     ws_cumul_pbE pb Σ Γ A B -> cumul_prop Σ Γ A B) -> False.
Proof.
  intros H.
  have h := H default_checker_flags rf_Σ rf_Γ Conv rf_t (tRel 0) rf_premise.
  apply (cumul_prop_alt (wfΣ := @wf_empty_global_env default_checker_flags)) in h
    as (nf & nf' & [r r' e]).
  exact (rf_no_eq_term_prop_reducts rf_Σ nf nf' r r' e).
Qed.

(** **Refuted:** the left-to-right half of base [cumul_prop_alt] ([PCUICCumulProp.v:248]) for
    [cumul_propE] (base: [{wfΣ : wf Σ}]; here [wfE Σ]). Its right-to-left half is
    [into_cumul_propE_red]. *)
Theorem cumul_prop_altE_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (T U : term),
     Σ ;;; Γ |-E T ~~ U ->
     ∑ nf nf', [× Σ ;;; Γ ⊢ T ⇝ nf, Σ ;;; Γ ⊢ U ⇝ nf' & eq_term_prop Σ 0 nf nf']) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags rf_Σ (wf_incl_E (@wf_empty_global_env default_checker_flags))
              rf_Γ rf_t (tRel 0) rf_cumul_propE) as (nf & nf' & [r r' e]).
  exact (rf_no_eq_term_prop_reducts rf_Σ nf nf' r r' e).
Qed.

(** The empty environment is [wf_ext] at the monomorphic context. *)
Lemma cpr_on_udecl_empty {cf : checker_flags} : on_udecl (universes empty_global_env) Monomorphic_ctx.
Proof.
  split; [|split; [|split]].
  - intros x Hx. exfalso. eapply LevelSet.empty_spec. exact Hx.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists {| valuation_mono := fun _ => 1%positive; valuation_poly := fun _ => 0 |}.
    intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma cpr_wf_ext_empty {cf : checker_flags} : wf_ext (empty_global_env, Monomorphic_ctx).
Proof. split; [exact (@wf_empty_global_env cf)|exact cpr_on_udecl_empty]. Qed.

(** **Refuted:** base [cumul_prop_args] ([PCUICCumulProp.v:639]) for [cumul_propE] (base:
    [{wfΣ : wf_ext Σ}]; here [wf_extE Σ]). *)
Theorem cumul_prop_argsE_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf_extE Σ) (Γ : context) (args args' : list term),
     All2 (cumul_propE Σ Γ) args args' ->
     ∑ nf nf', [× All2 (closed_red Σ Γ) args nf, All2 (closed_red Σ Γ) args' nf' &
       All2 (eq_term_prop Σ 0) nf nf']) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags rf_Σ (wf_ext_incl_E cpr_wf_ext_empty) rf_Γ [rf_t] [tRel 0]
              (All2_cons rf_cumul_propE All2_nil)) as (nf & nf' & [r r' e]).
  depelim r. depelim r'. depelim e.
  exact (rf_no_eq_term_prop_reducts rf_Σ _ _ c c0 e).
Qed.

(** ** A variable typed at [G F] and at [G (λy:Prop. F y)] *)

Section TLTWitness.

  Context {cf : checker_flags}.

  Definition tw_Σ : global_env_ext := (empty_global_env, Monomorphic_ctx).
  Definition tw_na : aname := mkBindAnn nAnon Relevant.
  Definition tw_P : term := tSort sProp.
  (** [Prop → Prop] and [(Prop → Prop) → Prop]. *)
  Definition tw_PP : term := tProd tw_na tw_P tw_P.
  Definition tw_PPP : term := tProd tw_na tw_PP tw_P.
  (** [G : (Prop → Prop) → Prop, F : Prop → Prop, x : G F], innermost first. *)
  Definition tw_Γ : context := [vass tw_na (tApp (tRel 1) (tRel 0)); vass tw_na tw_PP; vass tw_na tw_PPP].
  (** [G F] and [G (λy:Prop. F y)] in [tw_Γ]. *)
  Definition tw_GF : term := tApp (tRel 2) (tRel 1).
  Definition tw_etaF : term := tLambda tw_na tw_P (tApp (tRel 2) (tRel 0)).
  Definition tw_Geta : term := tApp (tRel 2) tw_etaF.

  Lemma tw_P_typed (Γ : context) : wf_localE tw_Σ Γ -> tw_Σ ;;; Γ |-E tw_P : tSort (Sort.super sProp).
  Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

  Lemma tw_P_vass (Γ : context) : wf_localE tw_Σ Γ -> lift_typing typingE tw_Σ Γ (j_vass tw_na tw_P).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (tw_P_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma tw_PP_typed (Γ : context) : wf_localE tw_Σ Γ ->
    tw_Σ ;;; Γ |-E tw_PP : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
  Proof.
    intros h. unfold tw_PP. apply typeE_Prod.
    - split; [exact tt|]. exists (Sort.super sProp).
      split; [exact (tw_P_typed Γ h)|]. split; reflexivity.
    - apply tw_P_typed. apply localenv_cons_abs; [exact h|exact (tw_P_vass Γ h)].
  Qed.

  Lemma tw_PP_vass (Γ : context) : wf_localE tw_Σ Γ -> lift_typing typingE tw_Σ Γ (j_vass tw_na tw_PP).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
    split; [exact (tw_PP_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma tw_PPP_typed (Γ : context) : wf_localE tw_Σ Γ ->
    tw_Σ ;;; Γ |-E tw_PPP : tSort (Sort.sort_of_product
      (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (Sort.super sProp)).
  Proof.
    intros h. unfold tw_PPP. apply typeE_Prod.
    - split; [exact tt|]. exists (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
      split; [exact (tw_PP_typed Γ h)|]. split; reflexivity.
    - apply tw_P_typed. apply localenv_cons_abs; [exact h|exact (tw_PP_vass Γ h)].
  Qed.

  Lemma tw_wf_G : wf_localE tw_Σ [vass tw_na tw_PPP].
  Proof.
    apply localenv_cons_abs; [constructor|].
    split; [exact tt|].
    exists (Sort.sort_of_product (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (Sort.super sProp)).
    split; [exact (tw_PPP_typed [] localenv_nil)|]. split; [exact I|reflexivity].
  Qed.

  Lemma tw_wf_GF : wf_localE tw_Σ [vass tw_na tw_PP; vass tw_na tw_PPP].
  Proof. apply localenv_cons_abs; [exact tw_wf_G|exact (tw_PP_vass _ tw_wf_G)]. Qed.

  (** [G F : Prop] in [F, G]. *)
  Lemma tw_xty_typed : tw_Σ ;;; [vass tw_na tw_PP; vass tw_na tw_PPP] |-E tApp (tRel 1) (tRel 0) : tw_P.
  Proof.
    exact (typeE_App _ _ (tRel 1) tw_na tw_PP tw_P _ (tRel 0) (tw_PPP_typed _ tw_wf_GF)
             (typeE_Rel _ _ 1 (vass tw_na tw_PPP) tw_wf_GF eq_refl)
             (typeE_Rel _ _ 0 (vass tw_na tw_PP) tw_wf_GF eq_refl)).
  Qed.

  Lemma tw_wf_Γ : wf_localE tw_Σ tw_Γ.
  Proof.
    apply localenv_cons_abs; [exact tw_wf_GF|].
    split; [exact tt|]. exists sProp.
    split; [exact tw_xty_typed|]. split; [exact I|reflexivity].
  Qed.

  (** [x : G F]. *)
  Lemma tw_x_GF : tw_Σ ;;; tw_Γ |-E tRel 0 : tw_GF.
  Proof. exact (typeE_Rel _ _ 0 (vass tw_na (tApp (tRel 1) (tRel 0))) tw_wf_Γ eq_refl). Qed.

  Lemma tw_etaF_typed : tw_Σ ;;; tw_Γ |-E tw_etaF : tw_PP.
  Proof.
    have w : wf_localE tw_Σ (tw_Γ ,, vass tw_na tw_P) :=
      localenv_cons_abs tw_wf_Γ (tw_P_vass tw_Γ tw_wf_Γ).
    unfold tw_etaF, tw_PP. apply typeE_Lambda; [exact (tw_P_vass tw_Γ tw_wf_Γ)|].
    exact (typeE_App _ _ (tRel 2) tw_na tw_P tw_P _ (tRel 0) (tw_PP_typed _ w)
             (typeE_Rel _ _ 2 (vass tw_na tw_PP) w eq_refl)
             (typeE_Rel _ _ 0 (vass tw_na tw_P) w eq_refl)).
  Qed.

  (** [G (λy:Prop. F y) : Prop]. *)
  Lemma tw_Geta_typed : tw_Σ ;;; tw_Γ |-E tw_Geta : tSort sProp.
  Proof.
    exact (typeE_App _ _ (tRel 2) tw_na tw_PP tw_P _ tw_etaF (tw_PPP_typed _ tw_wf_Γ)
             (typeE_Rel _ _ 2 (vass tw_na tw_PPP) tw_wf_Γ eq_refl) tw_etaF_typed).
  Qed.

  (** [G F ≤ G (λy:Prop. F y)]: congruence and the symmetric of one [cumul_eta_l] step. *)
  Lemma tw_spec : cumulSpecE tw_Σ tw_Γ tw_GF tw_Geta.
  Proof.
    unfold cumulSpecE, tw_GF, tw_Geta, tw_etaF.
    apply cumulE_App; [apply cumulE_Refl|].
    apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
  Qed.

  (** [x : G (λy:Prop. F y)]. *)
  Lemma tw_x_Geta : tw_Σ ;;; tw_Γ |-E tRel 0 : tw_Geta.
  Proof. exact (typeE_Cumul _ _ (tRel 0) tw_GF tw_Geta sProp tw_x_GF tw_Geta_typed tw_spec). Qed.

  Lemma tw_witness_typed :
    [× wf_ext tw_Σ, wfE tw_Σ, wf_localE tw_Σ tw_Γ,
       tw_Σ ;;; tw_Γ |-E tRel 0 : tw_GF & tw_Σ ;;; tw_Γ |-E tRel 0 : tw_Geta].
  Proof.
    split; [exact cpr_wf_ext_empty|exact (wf_incl_E (@wf_empty_global_env cf))
           |exact tw_wf_Γ|exact tw_x_GF|exact tw_x_Geta].
  Qed.

  (** Both types are [red1]-normal, in any environment. *)
  Lemma tw_Rel_normal (Σ : global_env) n v :
    n < 3 -> red1 Σ tw_Γ (tRel n) v -> False.
  Proof.
    intros hn H. inv_red H.
    match goal with e : option_map decl_body _ = _ |- _ =>
      destruct n as [|[|[|n]]]; cbn in e; try discriminate e; lia end.
  Qed.

  Lemma tw_GF_normal (Σ : global_env) v : red1 Σ tw_Γ tw_GF v -> False.
  Proof.
    unfold tw_GF. intros H. inv_red H.
    all: eapply tw_Rel_normal; [|eassumption]; lia.
  Qed.

  Lemma tw_etaF_body_normal (Σ : global_env) v :
    red1 Σ (tw_Γ ,, vass tw_na tw_P) (tApp (tRel 2) (tRel 0)) v -> False.
  Proof.
    intros H. inv_red H.
    - match goal with h : red1 _ _ (tRel 2) _ |- _ => inv_red h end.
      match goal with e : option_map decl_body _ = _ |- _ => cbn in e; discriminate e end.
    - eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma tw_Geta_normal (Σ : global_env) v : red1 Σ tw_Γ tw_Geta v -> False.
  Proof.
    unfold tw_Geta. intros H. inv_red H.
    - eapply tw_Rel_normal; [|eassumption]; lia.
    - revert H. unfold tw_etaF. revert x.
      apply red_normal_lam; [intros w; apply red_normal_Sort|intros w; apply tw_etaF_body_normal].
  Qed.

End TLTWitness.

(** Checker flags with [prop_sub_type = false], the premise of base's section. *)
Definition cpr_flags : checker_flags :=
  {| check_univs := true; prop_sub_type := false; indices_matter := false;
     lets_in_constructor_types := true |}.

(** **Refuted:** base [typing_leq_term_prop] ([PCUICCumulProp.v:1243]) over [typingE] and
    [wfE], with base [cumul_prop] kept as the conclusion. *)
Theorem typing_leq_term_prop_baseE_false :
  (forall (cf : checker_flags), prop_sub_type = false ->
   forall (Σ : global_env_ext) (Γ : context) (t t' T T' : term),
     wfE Σ.1 -> Σ ;;; Γ |-E t : T -> on_udecl Σ.1 Σ.2 -> Σ ;;; Γ |-E t' : T' ->
     forall (pb : conv_pb) (n : nat), compare_term_napp Σ Σ pb n t' t -> cumul_prop Σ Γ T T') -> False.
Proof.
  intros H.
  have wfE0 : @wfE cpr_flags tw_Σ := wf_incl_E (@wf_empty_global_env cpr_flags).
  have h := H cpr_flags eq_refl tw_Σ tw_Γ (tRel 0) (tRel 0) tw_Geta tw_GF wfE0 tw_x_Geta
              cpr_on_udecl_empty tw_x_GF Conv 0 (eq_term_upto_univ_refl _ _ _ _ _ _ _ _ _ (tRel 0)).
  apply (cumul_prop_alt (wfΣ := @wf_empty_global_env cpr_flags)) in h as (nf & nf' & [r r' e]).
  have e1 := rt_from_normal _ _ _ (tw_Geta_normal tw_Σ) (clrel_rel r).
  have e2 := rt_from_normal _ _ _ (tw_GF_normal tw_Σ) (clrel_rel r').
  subst nf nf'. depelim e.
  match goal with h : eq_term_upto_univ_napp _ _ _ _ _ tw_etaF (tRel 1) |- _ => depelim h end.
Qed.

(** ** [cumul_ind_confluence], refuted over [ws_cumul_pbE] *)

Lemma ir_not_spine (Σ : global_env) ind u l : red Σ [] ir_T (mkApps (tInd ind u) l) -> False.
Proof.
  intros r. have e := rt_from_normal _ _ _ (ir_T_normal Σ) r.
  exact (mkApps_Ind_not_Lambda _ _ _ _ _ _ e).
Qed.

(** **Refuted:** base [cumul_ind_confluence] ([PCUICCumulProp.v:45]) over [ws_cumul_pbE] and
    [wfE] (base: [{wfΣ : wf Σ}], untyped). *)
Theorem cumul_ind_confluenceE_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (A : term)
     (ind : inductive) (u v : Instance.t) (l l' : list term),
     ws_cumul_pbE Cumul Σ Γ A (mkApps (tInd ind u) l) ->
     ws_cumul_pbE Cumul Σ Γ A (mkApps (tInd ind v) l') ->
     ∑ v' l'',
       [× Σ ;;; Γ ⊢ A ⇝ (mkApps (tInd ind v') l''),
          ws_cumul_pbE_terms Σ Γ l l'',
          ws_cumul_pbE_terms Σ Γ l' l'',
          cmp_ind_universes Σ ind #|l| v' u &
          cmp_ind_universes Σ ind #|l'| v' v]) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags iu_Σ (wf_incl_E iu_wf) [] ir_T iu_ind [iu_a] [iu_a] [] []
              (ir_premise_r Cumul) (ir_premise_r Cumul)) as (v' & l'' & [r _ _ _ _]).
  exact (ir_not_spine iu_Σ _ _ _ (clrel_rel r)).
Qed.

(** **Refuted:** the same with [A] well typed (any type). The witness [λx:Set. I@{a} x] has type
    [Set → Set], not a sort: the form with [isTypeE Σ Γ A] is NOT refuted. *)
Theorem cumul_ind_confluenceE_typed_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (A T : term)
     (ind : inductive) (u v : Instance.t) (l l' : list term),
     Σ ;;; Γ |-E A : T ->
     ws_cumul_pbE Cumul Σ Γ A (mkApps (tInd ind u) l) ->
     ws_cumul_pbE Cumul Σ Γ A (mkApps (tInd ind v) l') ->
     ∑ v' l'',
       [× Σ ;;; Γ ⊢ A ⇝ (mkApps (tInd ind v') l''),
          ws_cumul_pbE_terms Σ Γ l l'',
          ws_cumul_pbE_terms Σ Γ l' l'',
          cmp_ind_universes Σ ind #|l| v' u &
          cmp_ind_universes Σ ind #|l'| v' v]) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags iu_Σ (wf_incl_E iu_wf) [] ir_T iu_arity iu_ind [iu_a] [iu_a] [] []
              ir_T_typedE (ir_premise_r Cumul) (ir_premise_r Cumul)) as (v' & l'' & [r _ _ _ _]).
  exact (ir_not_spine iu_Σ _ _ _ (clrel_rel r)).
Qed.
