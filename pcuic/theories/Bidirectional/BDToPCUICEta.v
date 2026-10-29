(* Distributed under the terms of the MIT license.   *)

(** * Bidirectional soundness over the η relations (plan row T6): the E copy of [BDToPCUIC]

  A copy of base [Bidirectional/BDToPCUIC.v] from the landed bidirectional E judgments
  ([BDTypingEta]: [checkingE], [inferingE], ...) to [typingE]: [typing] → [typingE],
  [wf] → [wfE], [wf_local] → [wf_localE], [wf_local_rel] → [wf_local_relE], [isType] →
  [isTypeE], [isTypeRel] → [isTypeRelE], [ctx_inst Σ] → [ctx_instE Σ], the bidirectional
  judgments → their E copies, [env_prop_bd] → [env_prop_bdE]. Nothing else changes in a
  statement; each name takes the suffix [E] (plan [t0-plan.md] §2, D1). Map, base → E:
  [wf_local_rel_subst1] → [wf_local_rel_subst1E]; [wf_rel_weak] → [wf_rel_weakE];
  [wf_local_local_rel] → [wf_local_local_relE]; [bd_wf_local] → [bd_wf_localE];
  [bd_wf_local_rel] → [bd_wf_local_relE]; [ctx_inst_impl] → [ctx_inst_implE];
  [bidirectional_to_pcuic] → [bidirectional_to_pcuicE]; [infering_typing],
  [checking_typing], [infering_sort_typing], [infering_sort_isType],
  [infering_sort_isTypeRel], [einfering_sort_isType], [isTypebd_isType],
  [lift_sorting_lift_typing], [infering_prod_typing], [infering_ind_typing],
  [wf_local_bd_typing], [wf_local_bd_rel_typing], [ctx_inst_bd_typing] → the same name
  with [E]. Base's two untyped lemmas [All2i_prod] and [All_local_env_app_l] mention
  neither typing nor conversion; they are imported from base, not copied.

  ** The comparisons (design points A and B of [BDTypingEta])

  - [checkE_Cumul] compares with [JoinE Σ Γ Cumul], the twin of base's [cumulAlgo]. Base
    turns it into [cumulSpec] with [into_ws_cumul_pb] and the scoping that the typing
    derivations give, then [cumulAlgo_cumulSpec] ([BDToPCUIC.v:418-424]). Here the same
    step is [into_ws_cumul_pbE] (I5's one join, with the scoping from [wf_local_closed_contextE],
    [type_is_open_termE], [subject_is_open_termE]) then [ws_cumul_pbE_forget_spec].
  - [inferE_Case] compares the parameters with [All2 (JoinE Σ Γ Conv)]. Base builds the
    cumulativity of the scrutinee's type from them with [into_ws_cumul_pb] and
    [ws_cumul_pb_mkApps_eq] ([BDToPCUIC.v:264-286]); here with [into_ws_cumul_pbE] and the
    landed congruence [ws_cumul_pbE_Ind] ([PCUICConversionEtaCongr]), whose universe premise
    is the rule's [cmp_ind_universes] as it is.
  - The (co)fixpoint witness is base's reduction witness [wf_fixpoint_red]; [typingE] wants
    [wf_fixpointE]. The bridge is the landed [wf_fixpoint_red_wf_fixpointE] /
    [wf_cofixpoint_red_wf_cofixpointE] ([BDTypingEta]), with the closed context and the
    scoped declared types from the typing of the types.

  ** Proof routes that differ from base (statements do not)

  - Case, the parameters' context: base gets [wf_local Σ (ind_params mdecl)@[u]] from
    [on_minductive_wf_params_indices] and [wf_local_subst_instance_decl]; here it is the field
    [on_minductive_wf_paramsE] of [SRForecastCopy14] (the twin of [PCUICArities.v:633]).
  - Case, the type of the scrutinee's target: base types
    [mkApps (tInd ci (puinst p)) (pparams p ++ indices)] with [type_mkApps_arity],
    [declared_inductive_type_ws_cumul], [on_inductive_inst] and
    [arity_spine_it_mkProd_or_LetIn], three copy lemmas that no forecast class has. Here it is
    the field [isType_mkApps_IndE] of [SRForecastCopy16] (twin of [PCUICInductives.v]
    [isType_mkApps_Ind]) on the spine [ctx_inst_spine_substE] ([ValForecastCopy15]) builds,
    so no forecast is added for them.
  - Base's [Proof using wfΣ] is [Proof.]: the forecast classes are section variables too.

  ** The forecast block

  The lemmas take the forecast classes of T2a and T1 as section [Context]s:
  [ValForecastCopy10/14/15/16] ([PCUICValidityEta]) and [SRForecastCopy10/12/14/15/16/18]
  ([PCUICSREta]); they are imported, never redefined. ONE copy lemma that soundness needs
  is in none of them: base [ctx_inst_app_weak] ([PCUICInductiveInversion.v:3794], copy 18).
  It is the one field of the class [BDForecastCopy18] below, with the base twin's statement.
  [Print Assumptions] in [BDToPCUICEtaInstances] shows every class as an argument.

  ** The checker's facts

  [T6BD_<field>_fit] restates, verbatim, each field of the checker's [T6BD_facts]
  ([safechecker/theories/PCUICTypingEtaHyps.v:222-243] on [wip/etak-k7-2026-10-29] @
  [afb353e4]) and proves it with the lemma here. *)

From Stdlib Require Import Bool List Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping
     PCUICEquality PCUICUnivSubst PCUICClosed PCUICCumulativity PCUICContexts PCUICSpine
     PCUICWellScopedCumulativity PCUICConversion PCUICOnFreeVars PCUICClosedTyp
     PCUICUnivSubstitutionConv PCUICFixWitness BDTyping BDToPCUIC.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningTypEta
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICInversionEta PCUICValidityEta PCUICSREta BDTypingEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

(** ** FORECAST BLOCK *)

(* The braces in the statement record the implicit status of the base twin. *)
Local Set Warnings "-unexpected-implicit-declaration".

(* FORECAST-ONLY: proved by copy 18 (PCUICInductiveInversionEta.v); delete when it lands.
   Text: the base twin, PCUICInductiveInversion.v:3794 [ctx_inst_app_weak], with [wf] → [wfE],
   [wf_local] → [wf_localE], [isType] → [isTypeE], [ctx_inst Σ] → [ctx_instE Σ], the
   cumulativity [Σ ;;; Γ ⊢ _ ≤ _] → [ws_cumul_pbE Cumul]. Not a known-false form: typing
   premises only, under [wfE]. Its base proof reads the universe clause of
   [invert_cumul_ind_ind], which is false over η below the arity
   ([PCUICEtaIndInvRefutations]). Here [isTypeE] of [mkApps (tInd ind u) args] makes [args]
   the full arity, where the landed [invert_cumul_ind_indE] gives the clause:
   [cmp_global_instance_finst] reads the variance of the full arity, as base's comparison
   does once [napp] reaches the arity. The other copy lemmas its base proof uses are the
   checker's [T0_facts] fields [inductive_cumulative_indices] and [ctx_inst_smash] and the
   [SRForecastCopy15] field [ctx_inst_cumulE]. *)
Class BDForecastCopy18 := {
  ctx_inst_app_weakE :
    forall {cf : checker_flags} (Σ : global_env_ext) (wfΣ : wfE Σ.1) (ind : inductive)
      (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
      (isdecl : declared_inductive Σ.1 ind mdecl idecl) (Γ : context) (wfΓ : wf_localE Σ Γ)
      (params args : list term) (u v : Instance.t),
    isTypeE Σ Γ (mkApps (tInd ind u) args) ->
    consistent_instance_ext Σ (ind_universes mdecl) v ->
    ctx_instE Σ Γ params (List.rev (subst_instance v (ind_params mdecl))) ->
    Σ ;;; Γ ⊢E mkApps (tInd ind u) args ≤ mkApps (tInd ind v) (params ++ skipn (ind_npars mdecl) args) ->
    ctx_instE Σ Γ (params ++ skipn (ind_npars mdecl) args)
      (List.rev (subst_instance v (ind_params mdecl ,,, ind_indices idecl)))
}.

Local Set Warnings "unexpected-implicit-declaration".

(** ** End of the FORECAST BLOCK *)

Section BDToPCUICEta.

(* FORECAST-ONLY: one premise per class: T2a's four ([PCUICValidityEta]), T1's six
   ([PCUICSREta]), and this file's one; delete each when its copy lands. *)
Context {V10 : ValForecastCopy10} {V14 : ValForecastCopy14} {V15 : ValForecastCopy15}
  {V16 : ValForecastCopy16} {F10 : SRForecastCopy10}
  {F12 : SRForecastCopy12} {F14 : SRForecastCopy14} {F15 : SRForecastCopy15}
  {F16 : SRForecastCopy16} {F18 : SRForecastCopy18} {B18 : BDForecastCopy18}.

(** Base [wf_local_rel_subst1] ([BDToPCUIC.v:33]). *)
Lemma wf_local_rel_subst1E `{checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Δ Γ na b t Γ' :
      wf_local_relE Σ Δ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local_relE Σ Δ (Γ ,,, subst_context [b] 0 Γ').
Proof.
  induction Γ' as [|d Γ']; [now inversion 1|].
  change (d :: Γ') with (Γ' ,, d).
  destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
  - rewrite subst_context_snoc0. simpl.
    inversion HH; subst; cbn in *.
    change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
    assert (subsletE Σ (Δ ,,, Γ) [b] [vdef na b t]). {
      pose proof (cons_let_defE Σ (Δ ,,, Γ) [] [] na b t) as XX.
      rewrite !subst_empty in XX. apply XX. constructor.
      apply All_local_env_app_l in X. inversion X; subst; cbn in * ; now eapply unlift_TermTyp.
    }
    constructor; cbn; auto.
    1: apply IHΓ' ; exact X.
    apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
    rewrite !app_context_assoc in Hs |- *.
    eapply substitutionE; tea.
  - rewrite subst_context_snoc0. simpl.
    inversion HH; subst; cbn in *.
    change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
    assert (subsletE Σ (Δ ,,, Γ) [b] [vdef na b t]). {
      pose proof (cons_let_defE Σ (Δ ,,, Γ) [] [] na b t) as XX.
      rewrite !subst_empty in XX. apply XX. constructor.
      apply All_local_env_app_l in X. inversion X; subst; cbn in *; now eapply unlift_TermTyp. }
    constructor; cbn; auto.
    1: apply IHΓ' ; exact X.
    apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
    rewrite !app_context_assoc in Hs |- *.
    eapply substitutionE; tea.
Qed.

(** Base [wf_rel_weak] ([BDToPCUIC.v:67]). *)
Lemma wf_rel_weakE `{checker_flags} (Σ : global_env_ext) (wfΣ : wfE Σ) Γ (wfΓ : wf_localE Σ Γ) Γ' :
  wf_localE Σ Γ' -> wf_local_relE Σ Γ Γ'.
Proof.
  induction Γ' as [|[? []] ?].
  - by constructor.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + apply lift_typing_impl with (1 := X0) => // ?? Hs.
      apply weaken_ctxE ; eauto.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + apply lift_typing_impl with (1 := X0) => // ?? Hs.
      apply weaken_ctxE ; eauto.
Qed.

(** Base [wf_local_local_rel] ([BDToPCUIC.v:84]). *)
Lemma wf_local_local_relE `{checker_flags} Σ Γ Γ' : wf_localE Σ (Γ ,,, Γ') -> wf_local_relE Σ Γ Γ'.
Proof.
  intro wfΓ.
  apply All_local_env_app_inv in wfΓ as [_ wfr] => //.
Qed.

Section BDToPCUICTypingE.

  (** We work in a fixed, well-formed global environment*)

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wfE Σ).

  (** The predicates we wish to prove, note the extra well-formedness hypothesis on the context
  and type whenever they are inputs to the algorithm *)

  Let Pinfer Γ t T :=
    wf_localE Σ Γ -> Σ ;;; Γ |-E t : T.

  Let Psort Γ t u :=
    wf_localE Σ Γ -> Σ ;;; Γ |-E t : (tSort u).

  Let Pprod Γ t na A B :=
    wf_localE Σ Γ -> Σ ;;; Γ |-E t : tProd na A B.

  Let Pind Γ ind t u args :=
    wf_localE Σ Γ -> Σ ;;; Γ |-E t : mkApps (tInd ind u) args.

  Let Pcheck Γ t T :=
    wf_localE Σ Γ -> isTypeE Σ Γ T -> Σ ;;; Γ |-E t : T.

  Let PΓ Γ :=
    wf_localE Σ Γ.

  Let PΓ_rel Γ Γ' :=
    wf_localE Σ Γ -> wf_local_relE Σ Γ Γ'.

  Let Pj Γ j :=
    wf_localE Σ Γ -> lift_typing typingE Σ Γ j.

  (** Preliminary lemmas to go from a bidirectional judgement to the corresponding undirected one *)

  (** Base [bd_wf_local] ([BDToPCUIC.v:127]). *)
  Lemma bd_wf_localE Γ (all: wf_local_bdE Σ Γ) :
    All_local_env_over_sorting (checkingE Σ) (infering_sortE Σ)
      (fun Γ _ t T _ => Pcheck Γ t T)
      (fun Γ _ t s _ => Psort Γ t s)
      Γ all ->
    wf_localE Σ Γ.
  Proof using Type.
    intros allo ; induction allo.
    all: constructor; tas.
    all: apply lift_sorting_it_impl with tu => //= Ht; eauto.
    apply Hc; cbn; auto.
    now eapply has_sort_isTypeE, Hs.
  Qed.

  (** Base [bd_wf_local_rel] ([BDToPCUIC.v:141]). *)
  Lemma bd_wf_local_relE Γ (wfΓ : wf_localE Σ Γ) Γ' (all: wf_local_bd_relE Σ Γ Γ') :
    All_local_env_over_sorting
      (fun Δ => checkingE Σ (Γ,,,Δ))
      (fun Δ => infering_sortE Σ (Γ,,,Δ))
      (fun Δ _ t T _ => Pcheck (Γ,,,Δ) t T)
      (fun Δ _ t s _ => Psort (Γ,,,Δ) t s)
      Γ' all ->
    wf_local_relE Σ Γ Γ'.
  Proof using Type.
    intros allo ; induction allo.
    all: constructor; tas.
    all: apply All_local_env_app in IHallo; tas.
    all: apply lift_sorting_it_impl with tu => //= Ht; eauto.
    apply Hc; cbn; auto.
    now eapply has_sort_isTypeE, Hs.
  Qed.

  (** Base [ctx_inst_impl] ([BDToPCUIC.v:158]). *)
  Lemma ctx_inst_implE Γ (wfΓ : wf_localE Σ Γ) (Δ : context) (wfΔ : wf_local_relE Σ Γ (List.rev Δ)) :
    forall args, PCUICTyping.ctx_inst Pcheck Γ args Δ -> ctx_instE Σ Γ args Δ.
  Proof.
    revert wfΔ.
    induction Δ using ctx_length_ind.
    1: intros _ ? d ; inversion_clear d ; constructor.
    intros wfΔ args ctxi ; inversion ctxi.
    - subst d.
      subst.
      assert (isTypeRelE Σ Γ t na.(binder_relevance)).
      {
        eapply All_local_rel_app_inv in wfΔ as [wfd _].
        inversion_clear wfd.
        eassumption.
      }
      apply isTypeRelE_isTypeE in X2 as X2'.
      constructor ; auto.
      apply X ; auto.
      1: by rewrite subst_telescope_length ; reflexivity.
      rewrite -(rev_involutive Γ0) -subst_context_telescope.
      cbn in wfΔ.
      apply All_local_rel_app_inv in wfΔ as [].
      apply wf_local_local_relE.
      eapply substitution_wf_localE ; eauto.
      1: repeat constructor.
      1: rewrite subst_empty ; eauto.
      apply All_local_env_app.
      1: constructor ; eauto.
      eassumption.
    - subst d.
      subst.
      assert (isTypeE Σ Γ t).
      {
        eapply All_local_rel_app_inv in wfΔ as [wfd _].
        inversion_clear wfd.
        now eapply lift_sorting_forget_body, lift_sorting_forget_rel.
      }
      constructor ; auto.
      apply X ; auto.
      1: by rewrite subst_telescope_length ; reflexivity.
      rewrite -(rev_involutive Γ0) -subst_context_telescope.
      rewrite <- app_nil_r.
      eapply wf_local_rel_subst1E.
      cbn in wfΔ |- *.
      eassumption.
  Qed.

  (** The big theorem, proven by mutual induction using the custom induction principle.
      Base [bidirectional_to_pcuic] ([BDToPCUIC.v:206]). *)
  Theorem bidirectional_to_pcuicE : env_prop_bdE Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
  Proof.
    apply bidir_ind_envE.

    - intros. intro.
      apply lift_sorting_it_impl with X.
      2: intros [_ IH]; now apply IH.
      destruct j_term => //=.
      intros [_ IH]; apply IH; tas.
      apply lift_sorting_forget_univ, lift_sorting_forget_rel, lift_sorting_forget_body in X.
      apply lift_sorting_it_impl_gen with X => //.
      intros [_ IH']; now apply IH'.

    - intros. eapply bd_wf_localE. eassumption.

    - intros. intro. eapply bd_wf_local_relE ; eassumption.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.
      apply X2.
      constructor. 1: by auto.
      eapply lift_sorting_forget_univ. now eapply X0.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - red ; intros.
      eapply type_App'E ; auto.
      apply X2 ; auto.
      specialize (X0 X3).
      apply validityE in X0 as (_ & s & X0 & _).
      apply inversion_ProdE in X0 as (s1 & s2 & X0 & _).
      2: done.
      eapply lift_sorting_forget_rel, lift_sorting_forget_univ; eassumption.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - red ; intros ; econstructor ; eauto.

    - intros Γ ci p c brs args u ps mdecl idecl predctx ptm
        hc IHc isdecl hret IHret hnpar heqctx hwfp hcons hpctx IHpctx helim hrel
        hpars IHpars hcofin hcmp hjoin hwfbrs hbrs.
      intro wfΓ.
      pose proof (wfE_ClosedBodies Σ (wfΣ := wfΣ)) as cbΣ.

      assert (cparams : ctx_instE Σ Γ (pparams p) (List.rev (ind_params mdecl)@[puinst p])).
      { apply ctx_inst_implE ; auto.
        rewrite rev_involutive.
        apply wf_rel_weakE ; auto.
        exact (on_minductive_wf_paramsE (wfΣ := wfΣ) (proj1 isdecl) hcons).
      }

      assert (cum : Σ ;;; Γ ⊢E mkApps (tInd ci u) args ≤
        mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) args)).
      {
        pose proof (IHc wfΓ) as hcty.
        pose proof (wf_local_closed_contextE (wfΣ := wfΣ) wfΓ) as clΓ.
        assert (hargs : forallb (is_open_term Γ) args).
        { pose proof (type_is_open_termE (wfΣ := wfΣ) hcty) as h.
          rewrite on_free_vars_mkApps /= in h. exact h. }
        assert (hpo : forallb (is_open_term Γ) (pparams p)).
        {
          eapply All_forallb'.
          1: exact (ctx_inst_closedE Σ Γ _ _ wfΣ cparams).
          intros.
          by rewrite -is_open_term_closed.
        }
        move: hargs.
        rewrite -{1}(firstn_skipn (ci_npar ci) args) forallb_app => /andP [hfirst hskip].
        apply ws_cumul_pbE_Ind; [exact hcmp|exact clΓ|].
        rewrite /ws_cumul_pbE_terms -{1}(firstn_skipn (ci_npar ci) args).
        apply All2_app.
        - eapply All2_impl.
          + eapply All2_All_mix_left; [exact (forallb_All _ _ hfirst)|].
            eapply All2_All_mix_right; [exact (forallb_All _ _ hpo)|].
            exact hjoin.
          + intros x y [hx [hj hy]]. exact (into_ws_cumul_pbE hj clΓ hx hy).
        - exact (WT_refl clΓ hskip).
      }

      assert (cinst : ctx_instE Σ Γ (pparams p ++ skipn (ci_npar ci) args)
        (List.rev (subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)))).
      {
        rewrite -hnpar.
        eapply ctx_inst_app_weakE ; eauto.
        1: eapply (validityE (wfΣ := wfΣ)) ; auto.
        now rewrite hnpar.
      }

      assert (hwfΓΔ : wf_localE Σ (Γ ,,, (ind_params mdecl ,,, ind_indices idecl)@[puinst p])).
      { exact (PCUICWeakeningTypEta.weaken_wf_localE Γ wfΣ wfΓ
                 (on_minductive_wf_params_indices_instE (wfΣ := wfΣ) isdecl (puinst p) hcons)). }
      pose proof (isType_mkApps_IndE (wfΣ := wfΣ) isdecl hcons
                    (ctx_inst_spine_substE (wfΣ := wfΣ) hwfΓΔ cinst)) as hty.
      pose proof (has_sort_isTypeE _ hty) as histy.

      assert (wfpred : wf_localE Σ (Γ ,,, predctx)).
      { exact (wf_case_predicate_contextE (wfΣ := wfΣ) isdecl histy hwfp). }

      eapply typeE_Case.
      + exact isdecl.
      + exact (IHret wfpred).
      + eapply typeE_Cumul; [exact (IHc wfΓ)|exact hty|exact (ws_cumul_pbE_forget_spec (wfΣ := cbΣ) cum)].
      + econstructor; [exact hnpar|exact hwfp|exact hcons|exact wfpred|exact heqctx|exact helim
                      |exact hrel|exact cinst|exact hcofin].
      + econstructor; [exact hwfbrs|].
        eapply All2i_impl.
        1:{ apply All2i_prod ; [exact hbrs|].
            exact (wf_case_branches_types'E (wfΣ := wfΣ) ps (skipn (ci_npar ci) args) brs isdecl histy
                     hwfp (IHret wfpred) hwfbrs heqctx).
        }
        intros i cdecl br ((heq & _ & _ & _ & IHbody) & [_ _ _ hwfbr hsort]).
        split; [exact heq|].
        cbv beta zeta.
        split; [exact hwfbr|split; [|exact hsort]].
        exact (IHbody hwfbr (has_sort_isTypeE _ hsort)).

    - red ; intros ; econstructor ; eauto.

    - red ; intros Γ mfix n decl hguard hnth Htys IHtys Hbods IHbods wffix wfΓ ;
        econstructor ; eauto.

      + clear hguard hnth wffix Htys.
        apply All_impl with (1 := IHtys) => d Hd.
        specialize (Hd wfΓ).
        apply lift_sorting_it_impl with Hd => //.

      + have Htypes : All (fun d => isTypeRelE Σ Γ (dtype d) (dname d).(binder_relevance)) mfix.
        { apply All_impl with (1 := IHtys) => d Hd.
          specialize (Hd wfΓ).
          apply lift_sorting_it_impl with Hd => //.
        }
        have wfΓ' : wf_localE Σ (Γ,,,fix_context mfix) by apply All_mfix_wfE.

        remember (fix_context mfix) as Γ' eqn:e.
        clear hguard hnth wffix e.
        apply All_mix with (1 := Htypes) in IHbods.
        apply All_impl with (1 := IHbods) => d [] isTy Hd.
        specialize (Hd wfΓ').
        apply lift_sorting_it_impl with Hd => //=.

      + eapply (wf_fixpoint_red_wf_fixpointE (cb := wfE_ClosedBodies Σ (wfΣ := wfΣ)));
          [exact (wf_local_closed_contextE (wfΣ := wfΣ) wfΓ)| |exact wffix].
        apply All_impl with (1 := IHtys) => d Hd.
        specialize (Hd wfΓ).
        eapply (PCUICClosedTypEta.isType_is_open_termE (wfΣ := wfΣ)).
        eapply isTypeRelE_isTypeE.
        apply lift_sorting_it_impl with Hd => //.

    - red ; intros Γ mfix n decl hguard hnth Htys IHtys Hbods IHbods wfcofix wfΓ ;
        econstructor ; eauto.

      + clear hguard hnth wfcofix Htys.
        apply All_impl with (1 := IHtys) => d Hd.
        specialize (Hd wfΓ).
        apply lift_sorting_it_impl with Hd => //.

      + have Htypes : All (fun d => isTypeRelE Σ Γ (dtype d) (dname d).(binder_relevance)) mfix.
        { apply All_impl with (1 := IHtys) => d Hd.
          specialize (Hd wfΓ).
          apply lift_sorting_it_impl with Hd => //.
        }
        have wfΓ' : wf_localE Σ (Γ,,,fix_context mfix) by apply All_mfix_wfE.

        remember (fix_context mfix) as Γ' eqn:e.
        clear hguard hnth wfcofix e.
        apply All_mix with (1 := Htypes) in IHbods.
        apply All_impl with (1 := IHbods) => d [] isTy Hd.
        specialize (Hd wfΓ').
        apply lift_sorting_it_impl with Hd => //=.

      + eapply (wf_cofixpoint_red_wf_cofixpointE (cb := wfE_ClosedBodies Σ (wfΣ := wfΣ)));
          [exact (wf_local_closed_contextE (wfΣ := wfΣ) wfΓ)| |exact wfcofix].
        apply All_impl with (1 := IHtys) => d Hd.
        specialize (Hd wfΓ).
        eapply (PCUICClosedTypEta.isType_is_open_termE (wfΣ := wfΣ)).
        eapply isTypeRelE_isTypeE.
        apply lift_sorting_it_impl with Hd => //.

    - red; intros.
      econstructor; eauto.
      depelim X0; try solve [ constructor; eauto ].
      unfold Pcheck in hty, hdef.
      do 2 forward hty; tas. 1: eapply has_sort_isTypeE; now econstructor.
      do 2 forward hdef; tas. 1: now eapply has_sort_isTypeE.
      constructor; eauto.
      eapply All_impl; [eassumption|]. intros x hx. unfold Pcheck in hx.
      apply hx; [assumption|]. now eapply has_sort_isTypeE.

    - intros Γ t T u ht IHt hr wfΓ.
      exact (type_reductionE (wfΣ := wfΣ) (IHt wfΓ) hr).

    - intros Γ t T na A B ht IHt hr wfΓ.
      exact (type_reductionE (wfΣ := wfΣ) (IHt wfΓ) hr).

    - intros Γ ind t T ui args ht IHt hr wfΓ.
      exact (type_reductionE (wfΣ := wfΣ) (IHt wfΓ) hr).

    - intros Γ t T T' ht IHt hj wfΓ isTy.
      destruct isTy as (_ & s & hs & _).
      pose proof (IHt wfΓ) as hT.
      eapply typeE_Cumul; [exact hT|exact hs|].
      exact (ws_cumul_pbE_forget_spec (wfΣ := wfE_ClosedBodies Σ (wfΣ := wfΣ))
               (into_ws_cumul_pbE hj (wf_local_closed_contextE (wfΣ := wfΣ) wfΓ)
                  (type_is_open_termE (wfΣ := wfΣ) hT) (subject_is_open_termE (wfΣ := wfΣ) hs))).
  Qed.

End BDToPCUICTypingE.

(** The user-facing theorems, directly following from the previous one *)

(** Base [infering_typing] ([BDToPCUIC.v:431]). *)
Theorem infering_typingE `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> Σ ;;; Γ |-E t ▹ T -> Σ ;;; Γ |-E t : T.
Proof.
  intros.
  apply bidirectional_to_pcuicE.
  all: assumption.
Qed.

(** Base [checking_typing] ([BDToPCUIC.v:439]). *)
Theorem checking_typingE `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> isTypeE Σ Γ T -> Σ ;;; Γ |-E t ◃ T -> Σ ;;; Γ |-E t : T.
Proof.
  intros wfΓ HT Ht. revert wfΓ HT.
  apply bidirectional_to_pcuicE.
  all: assumption.
Qed.

(** Base [infering_sort_typing] ([BDToPCUIC.v:447]). *)
Theorem infering_sort_typingE `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> Σ ;;; Γ |-E t ▹□ u -> Σ ;;; Γ |-E t : tSort u.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuicE.
  assumption.
Qed.

(** Base [infering_sort_isType] ([BDToPCUIC.v:455]). *)
Theorem infering_sort_isTypeE `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> Σ ;;; Γ |-E t ▹□ u -> isTypeE Σ Γ t.
Proof.
  intros wfΓ Ht.
  repeat (eexists; tea).
  now apply infering_sort_typingE.
Qed.

(** Base [infering_sort_isTypeRel] ([BDToPCUIC.v:463]). *)
Theorem infering_sort_isTypeRelE `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> Σ ;;; Γ |-E t ▹□ u -> isTypeRelE Σ Γ t (relevance_of_sort u).
Proof.
  intros wfΓ Ht.
  repeat (eexists; tea).
  now apply infering_sort_typingE.
Qed.

(** Base [einfering_sort_isType] ([BDToPCUIC.v:471]). *)
Theorem einfering_sort_isTypeE `{checker_flags} (Σ : global_env_ext) Γ t (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> (∑ u, Σ ;;; Γ |-E t ▹□ u) -> isTypeE Σ Γ t.
Proof.
  intros wfΓ [u Ht].
  now eapply infering_sort_isTypeE.
Qed.

(** Base [isTypebd_isType] ([BDToPCUIC.v:478]). *)
Theorem isTypebd_isTypeE `{checker_flags} (Σ : global_env_ext) Γ j (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) j -> isTypeE Σ Γ (j_typ j).
Proof.
  intros wfΓ (_ & s & Hs & _).
  now eapply infering_sort_isTypeE.
Qed.

(** Base [lift_sorting_lift_typing] ([BDToPCUIC.v:485]). *)
Theorem lift_sorting_lift_typingE `{cf : checker_flags} (Σ : global_env_ext) Γ j (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) j -> lift_typing typingE Σ Γ j.
Proof.
  intros wfΓ Hj.
  apply lift_sorting_it_impl with Hj.
  2: intros H; now apply infering_sort_typingE, H.
  destruct j_term => //=.
  intros H; apply checking_typingE; tas.
  now apply isTypebd_isTypeE in Hj.
Qed.

(** Base [infering_prod_typing] ([BDToPCUIC.v:496]). *)
Theorem infering_prod_typingE `{checker_flags} (Σ : global_env_ext) Γ t na A B (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> Σ ;;; Γ |-E t ▹Π (na,A,B) -> Σ ;;; Γ |-E t : tProd na A B.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuicE.
  assumption.
Qed.

(** Base [infering_ind_typing] ([BDToPCUIC.v:504]). *)
Theorem infering_ind_typingE `{checker_flags} (Σ : global_env_ext) Γ t ind u args (wfΣ : wfE Σ) :
wf_localE Σ Γ -> Σ ;;; Γ |-E t ▹{ind} (u,args) -> Σ ;;; Γ |-E t : mkApps (tInd ind u) args.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuicE.
  assumption.
Qed.

(** Base [wf_local_bd_typing] ([BDToPCUIC.v:512]). *)
Theorem wf_local_bd_typingE `{checker_flags} (Σ : global_env_ext) Γ (wfΣ : wfE Σ) :
  wf_local_bdE Σ Γ -> wf_localE Σ Γ.
Proof.
  apply bidirectional_to_pcuicE.
  assumption.
Qed.

(** Base [wf_local_bd_rel_typing] ([BDToPCUIC.v:519]). *)
Theorem wf_local_bd_rel_typingE `{checker_flags} (Σ : global_env_ext) Γ Γ' (wfΣ : wfE Σ) :
  wf_localE Σ Γ -> wf_local_bd_relE Σ Γ Γ' -> wf_local_relE Σ Γ Γ'.
Proof.
  intros.
  now apply bidirectional_to_pcuicE.
Qed.

(** Base [ctx_inst_bd_typing] ([BDToPCUIC.v:526]). *)
Theorem ctx_inst_bd_typingE `{checker_flags} (Σ : global_env_ext) Γ l Δ (wfΣ : wfE Σ) :
  wf_localE Σ (Γ,,,Δ) ->
  PCUICTyping.ctx_inst (checkingE Σ) Γ l (List.rev Δ) ->
  PCUICTyping.ctx_inst (typingE Σ) Γ l (List.rev Δ).
Proof.
  intros wfΓ inl.
  rewrite -(List.rev_involutive Δ) in wfΓ.
  remember (List.rev Δ) as Δ'.
  clear HeqΔ'.
  induction inl in wfΓ |- *.
  - constructor.
  - assert (Σ ;;; Γ |-E i : t).
    {
      rewrite /= app_context_assoc in wfΓ.
      eapply All_local_env_app_inv in wfΓ as [wfΓ _].
      inversion wfΓ ; subst.
      apply isTypeRelE_isTypeE in X0.
      now apply checking_typingE.
    }
    constructor ; tea.
    eapply IHinl.
    rewrite /= app_context_assoc in wfΓ.
    rewrite -subst_context_rev_subst_telescope.
    eapply substitution_wf_localE ; tea.
    constructor.
    1: constructor.
    now rewrite subst_empty.
  - constructor.
    eapply IHinl.
    rewrite /= app_context_assoc in wfΓ.
    rewrite -subst_context_rev_subst_telescope.
    eapply substitution_wf_localE ; tea.
    rewrite -{1}(subst_empty 0 b).
    constructor.
    1: constructor.
    rewrite !subst_empty.
    eapply All_local_env_app_inv in wfΓ as [wfΓ _].
    inversion wfΓ ; subst.
    now eapply unlift_TermTyp.
Qed.

(** ** The checker's [T6BD_facts]

  Each statement is the field's text, verbatim, from [safechecker/theories/PCUICTypingEtaHyps.v]
  ([wip/etak-k7-2026-10-29] @ [afb353e4], lines 222-243); the body is the lemma above. Every
  field has base's statement (the checker's printed form of base's compiled lemma) with the
  relations renamed, so no field differs from its base twin. *)

Definition T6BD_checking_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> isTypeE Σ Γ T -> Σ;;; Γ |-E t ◃ T -> Σ;;; Γ |-E t : T
  := @checking_typingE cf.

Definition T6BD_ctx_inst_bd_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : list context_decl) (l : list term) (Δ : list context_decl) (wfΣ : wfE Σ), wf_localE Σ (Γ,,, Δ) -> PCUICTyping.ctx_inst (checkingE Σ) Γ l (List.rev Δ) -> ctx_instE Σ Γ l (List.rev Δ)
  := @ctx_inst_bd_typingE cf.

Definition T6BD_infering_ind_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (ind : inductive) (u : Instance.t) (args : list term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t : mkApps (tInd ind u) args
  := @infering_ind_typingE cf.

Definition T6BD_infering_prod_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (na : aname) (A : term) (B : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t : tProd na A B
  := @infering_prod_typingE cf.

Definition T6BD_infering_sort_isTypeRel_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹□ u -> isTypeRelE Σ Γ t (relevance_of_sort u)
  := @infering_sort_isTypeRelE cf.

Definition T6BD_infering_sort_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t : tSort u
  := @infering_sort_typingE cf.

Definition T6BD_infering_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t : T
  := @infering_typingE cf.

Definition T6BD_lift_sorting_lift_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (j : judgment) (wfΣ : wfE Σ), wf_localE Σ Γ -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) j -> lift_typing typingE Σ Γ j
  := @lift_sorting_lift_typingE cf.

Definition T6BD_wf_local_bd_rel_typing_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (Γ' : context) (wfΣ : wfE Σ), wf_localE Σ Γ -> wf_local_bd_relE Σ Γ Γ' -> wf_local_relE Σ Γ Γ'
  := @wf_local_bd_rel_typingE cf.

Definition T6BD_wf_rel_weak_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context), wf_localE Σ Γ -> forall (Γ' : context), wf_localE Σ Γ' -> wf_local_relE Σ Γ Γ'
  := @wf_rel_weakE cf.

End BDToPCUICEta.
