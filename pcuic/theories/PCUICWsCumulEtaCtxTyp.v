(* Distributed under the terms of the MIT license. *)

(** * Typed facts for [ws_cumul_pbE], over [typingE]

  The E counterparts of the typed lemmas of base [PCUICWellScopedCumulativity],
  [PCUICConversion] and [PCUICContextConversion] that the E copies of the typing
  infrastructure use. Typing is [typingE] ([PCUICTypingEta]); the environment
  premise is [wfE Σ] where base assumes [wf Σ]. A type is
  [on_type (lift_typing typingE) Σ Γ T], base's [isType] over [typingE].

  - [wt_cumul_pbE]: base's [wt_cumul_pb] record, two types and their join
    [JoinE] (base: [cumulAlgo_gen]); [wt_cumul_pbE_ws_cumul_pbE] scopes it.
  - [isType_ws_cumul_pbE_refl].
  - [subst_instance_ws_cumul_ctx_pbE]: a well-formed context at two equal
    universe instances.
  - Iterated β-reduction: [red_betas0_cb], [red_betas_cb] (base's [red_betas0],
    [red_betas] under [ClosedBodies Σ] in place of [wf Σ]), [red_betas_typedE],
    [conv_betasE].
  - [context_cumulativity_wf_appE].

  None of these uses validity: each reads only the scoping that typing gives
  ([wf_local_closed_contextE], [subject_is_open_termE], [subject_closedE]).

**The hypotheses are satisfiable:** [wfE Σ] by any well-formed environment
  ([wf_incl_E]); [ClosedBodies Σ] by [wfE_ClosedBodies]; the typing premises by
  the sort [Prop] in a well-formed context; every [JoinE] premise by reflexivity.
  Instances: [PCUICWsCumulEtaCtxInstances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICSigmaCalculus PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICConversion PCUICContextConversion
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICClosed PCUICClosedTyp PCUICContextSubst
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICClosedBodies.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** Well-typed conversion *)

Record wt_cumul_pbE {cf} (pb : conv_pb) Σ (Γ : context) T U :=
  { wt_cumul_pbE_dom : on_type (lift_typing typingE) Σ Γ T;
    wt_cumul_pbE_codom : on_type (lift_typing typingE) Σ Γ U;
    wt_cumul_pbE_eq : JoinE Σ Γ pb T U }.

Arguments wt_cumul_pbE_dom {cf pb Σ Γ T U}.
Arguments wt_cumul_pbE_codom {cf pb Σ Γ T U}.
Arguments wt_cumul_pbE_eq {cf pb Σ Γ T U}.

Section Typed.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  Lemma on_typeE_scoped {Γ T} :
    on_type (lift_typing typingE) Σ Γ T -> is_closed_context Γ × is_open_term Γ T.
  Proof.
    intros H. split.
    - exact (wf_local_closed_contextE (lift_typingE_wf_local H)).
    - destruct H as (_ & s & Hs & _). exact (subject_is_open_termE Hs).
  Qed.

  (** Base [isType_ws_cumul_pb_refl], under [wfE Σ] in place of [wf Σ]. *)
  Lemma isType_ws_cumul_pbE_refl {pb} Γ T :
    on_type (lift_typing typingE) Σ Γ T -> ws_cumul_pbE pb Σ Γ T T.
  Proof.
    intros H. destruct (on_typeE_scoped H) as [hΓ hT].
    exact (ws_cumul_pbE_refl hΓ hT).
  Qed.

  (** Base [wt_cumul_pb_ws_cumul_pb], under [wfE Σ] in place of [wf Σ]. *)
  Lemma wt_cumul_pbE_ws_cumul_pbE {pb Γ T U} :
    wt_cumul_pbE pb Σ Γ T U -> ws_cumul_pbE pb Σ Γ T U.
  Proof.
    move=> [] dom codom equiv.
    destruct (on_typeE_scoped dom) as [hΓ hT].
    destruct (on_typeE_scoped codom) as [_ hU].
    exact (into_ws_cumul_pbE equiv hΓ hT hU).
  Qed.

  (** Base [subst_instance_ws_cumul_ctx_pb], under [wfE Σ] in place of [wf Σ]. *)
  Lemma subst_instance_ws_cumul_ctx_pbE {Δ u u'} pb :
    wf_localE Σ (subst_instance u Δ) ->
    cmp_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
    ws_cumul_ctx_pbE pb Σ (subst_instance u Δ) (subst_instance u' Δ).
  Proof.
    move=> wf equ.
    pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
    induction Δ as [|d Δ IH] in wf |- *.
    - constructor.
    - rewrite !subst_instance_cons. constructor.
      + apply IH. rewrite subst_instance_cons in wf. depelim wf; assumption.
      + pose proof (wf_local_closed_contextE (wfΣ := wfΣ) wf) as hcl.
        rewrite subst_instance_cons on_free_vars_ctx_snoc in hcl.
        move/andP: hcl => [hcl hd].
        unfold ws_cumul_declsE.
        destruct d as [na [b|] ty]; move: hd; rewrite /on_free_vars_decl /test_decl /=.
        * move=> /andP [hb hty]. constructor; [reflexivity| |].
          -- apply ws_cumul_pb_incl_E; constructor; [exact hcl|exact hb| |].
             ++ move: hb; rewrite !on_free_vars_subst_instance; exact id.
             ++ eapply eq_term_upto_univ_subst_instance; try typeclasses eauto; auto.
          -- apply ws_cumul_pb_incl_E; constructor; [exact hcl|exact hty| |].
             ++ move: hty; rewrite !on_free_vars_subst_instance; exact id.
             ++ destruct pb; cbn; eapply eq_term_upto_univ_subst_instance; try typeclasses eauto; auto.
        * move=> hty. constructor; [reflexivity|].
          apply ws_cumul_pb_incl_E; constructor; [exact hcl|exact hty| |].
          -- move: hty; rewrite !on_free_vars_subst_instance; exact id.
          -- destruct pb; cbn; eapply eq_term_upto_univ_subst_instance; try typeclasses eauto; auto.
  Qed.

End Typed.

Set Warnings "-uniform-inheritance".
Coercion wt_cumul_pbE_ws_cumul_pbE : wt_cumul_pbE >-> ws_cumul_pbE.
Set Warnings "uniform-inheritance".

(** ** Iterated β-reduction *)

Section IteratedBetaReduction.
  Context `{cf : checker_flags}.

  (** Base [red_betas0], under [ClosedBodies Σ] in place of [wf Σ]: the proof is
      base's, with [substitution_untyped_red_cb] for [substitution_untyped_red]. *)
  Lemma red_betas0_cb (Σ : global_env_ext) (cbΣ : ClosedBodies Σ) Γ (Δ : context) l t t' :
    #|l| = context_assumptions Δ ->
    closedn #|Γ,,, Δ| t ->
    closed_ctx (Γ ,,, Δ) ->
    PCUICReduction.red Σ.1 (Γ ,,, Δ) t t' ->
    PCUICReduction.red Σ.1 Γ (mkApps (it_mkLambda_or_LetIn Δ t) l) (subst0 (List.rev l) (expand_lets Δ t')).
  Proof.
    elim: Δ t t' l=> [|[na[a|]ty] ls ih] /= t t' l.
    - move=> /length_nil -> * /=.
      rewrite PCUICLiftSubst.subst_empty PCUICSigmaCalculus.expand_lets_nil //.
    - move=> /ih ih0 clt clctx red. rewrite -/([_] ++ _).
      move: (clctx); rewrite Nat.add_0_r => /andP [clctx0 cld].
      rewrite expand_lets_app /= -/(expand_lets ls).
      refine (ih0 _ _ _ _ _)=> //.
      1: apply: PCUICClosed.closedn_mkLambda_or_LetIn=> //.
      rewrite /mkLambda_or_LetIn /= /expand_lets /expand_lets_k /=.
      rewrite PCUICLiftSubst.subst_empty PCUICLiftSubst.lift0_p.
      apply: PCUICReduction.red_step; first exact: PCUICReduction.red_zeta.
      rewrite PCUICLiftSubst.lift0_id.
      refine (substitution_untyped_red_cb (Σ:=Σ) (Γ := Γ,,, ls) (Δ := [_]) (Γ':=nil) (M := t) (N:=t') _ _ _ red).
      + apply: untyped_subslet_def_tip=> //.
      + rewrite -PCUICClosedTyp.is_open_term_closed //.
      + rewrite on_free_vars_ctx_on_ctx_free_vars -PCUICClosedTyp.is_closed_ctx_closed //.
    - move: l=> /snocP [//|/=l x].
      rewrite length_app /= Nat.add_comm PCUICAstUtils.mkApps_app /= => [=] eq.
      move: (eq)=> /ih ih0 clt clctx red.
      move: (clctx); rewrite Nat.add_0_r => /andP [clctx0 cld].
      etransitivity.
      1:{
        apply: PCUICReduction.red_app; last reflexivity.
        apply: ih0.
        + apply: PCUICClosed.closedn_mkLambda_or_LetIn=> //.
        + assumption.
        + apply: red_abs_alt; first reflexivity; eassumption.
      }
      apply: PCUICReduction.red_step=> /=; first apply: PCUICReduction.red_beta.
      set t0 := (t in PCUICReduction.red _ _ t _).
      set t1 := (t in PCUICReduction.red _ _ _ t).
      have -> // : t0 = t1.
      rewrite {}/t0 {}/t1.
      rewrite /subst1 -PCUICLiftSubst.subst_app_simpl -(rev_app_distr _ [x]).
      f_equal; rewrite -/([_]++ls) expand_lets_app /= /expand_lets.
      rewrite {-1}/expand_lets_k /=subst_rel0_lift_id //.
  Qed.

  (** Base [red_betas], under [ClosedBodies Σ] in place of [wf Σ]. *)
  Lemma red_betas_cb (Σ : global_env_ext) (cbΣ : ClosedBodies Σ) Γ (Δ : context) l t :
    #|l| = context_assumptions Δ ->
    closedn #|Γ,,, Δ| t ->
    closed_ctx (Γ ,,, Δ) ->
    PCUICReduction.red Σ.1 Γ (mkApps (it_mkLambda_or_LetIn Δ t) l) (subst0 (mk_ctx_subst Δ l) t).
  Proof.
    move=> eql.
    move: (mk_ctx_subst_spec (eq_sym eql))=> /(context_subst_subst_expand_lets _ _ _ t 0) ->.
    move=> *; apply: (red_betas0_cb Σ cbΣ)=> //.
  Qed.

  (** Base [red_betas_typed], over [typingE] under [wfE Σ] in place of [wf Σ]. *)
  Lemma red_betas_typedE (Σ : global_env_ext) (wfΣ : wfE Σ) Γ (Δ : context) l t T :
    #|l| = context_assumptions Δ ->
    Σ ;;; Γ ,,, Δ |-E t : T ->
    PCUICReduction.red Σ.1 Γ (mkApps (it_mkLambda_or_LetIn Δ t) l) (subst0 (mk_ctx_subst Δ l) t).
  Proof.
    move=> eql ty.
    pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
    apply: (red_betas_cb Σ cbΣ)=> //.
    1: exact (subject_closedE ty).
    exact (closed_wf_localE wfΣ (typingE_wf_local ty)).
  Qed.

  (** Base [conv_betas], into [convSpecE], under [ClosedBodies Σ] in place of
      [wf Σ]. *)
  Lemma conv_betasE (Σ : global_env_ext) (cbΣ : ClosedBodies Σ) Γ Δ l t :
    closedn #|Γ ,,, Δ| t ->
    closed_ctx (Γ ,,, Δ) ->
    forallb (closedn #|Γ|) l ->
    context_assumptions Δ = #|l| ->
    Σ ;;; Γ ⊢ mkApps (it_mkLambda_or_LetIn Δ t) l ≤sE[Conv] subst0 (mk_ctx_subst Δ l) t.
  Proof.
    move=> tws /[dup] ?.
    rewrite PCUICClosed.closedn_ctx_app=> /andP[??] lcl eqlen.
    apply: ws_cumul_pbE_forget_spec.
    apply: red_ws_cumul_pbE.
    constructor.
    - by rewrite -PCUICClosedTyp.is_closed_ctx_closed.
    - rewrite -PCUICClosedTyp.is_open_term_closed PCUICClosed.closedn_mkApps lcl andb_true_r.
      apply: PCUICClosed.closedn_it_mkLambda_or_LetIn => //.
      by rewrite Nat.add_comm -length_app.
    - apply: (red_betas_cb Σ cbΣ) => //; symmetry; assumption.
  Qed.

End IteratedBetaReduction.

(** ** Context cumulativity of a local environment *)

Lemma cumul_decls_reflE {cf : checker_flags} Σ Γ Γ' d : cumul_decls (@JoinE cf) Σ Γ Γ' d d.
Proof. destruct d as [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl. Qed.

(** Base [context_cumulativity_wf_app], over [typingE] and [JoinE]. No premise, as
    in base. *)
Lemma context_cumulativity_wf_appE {cf : checker_flags} Σ Γ Γ' Δ :
  cumul_context (@JoinE cf) Σ Γ' Γ ->
  wf_localE Σ Γ' ->
  All_local_env (fun Γ j =>
    forall Γ' : context,
    cumul_context (@JoinE cf) Σ Γ' Γ -> wf_localE Σ Γ' ->
    (lift_typing0 (fun t T => Σ ;;; Γ' |-E t : T)) j)
    (Γ ,,, Δ) ->
  wf_localE Σ (Γ' ,,, Δ).
Proof.
  intros.
  eapply All_local_env_app => //.
  eapply All_local_env_app_inv in X1 as [].
  eapply All_local_env_impl_ind; tea => /=.
  intros Γ'' j H HT.
  eapply HT. eapply All2_fold_app => //.
  eapply All2_fold_refl. intros. eapply cumul_decls_reflE.
  eapply All_local_env_app; auto.
Qed.
