(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICPrimitive PCUICLiftSubst PCUICUnivSubst
     PCUICSigmaCalculus PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosed PCUICTyping PCUICCumulativity
     PCUICCumulativitySpec PCUICWellScopedCumulativity PCUICContextSubst PCUICCases PCUICNormal PCUICPosition
     PCUICConversion PCUICFixWitness PCUICWfUniverses PCUICClosedBodies PCUICSpine PCUICWeakeningEnv
     PCUICInductiveInversion PCUICContextConversionTyp PCUICRenameDef
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind
     PCUICEtaA6More PCUICGlobalEnvEta
     PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWsCumulEtaCtx
     PCUICWeakeningTypEta PCUICRenameTypEta PCUICInstDefEta PCUICInstTypEta PCUICCasesWfTypEta PCUICGuardClosureEta
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution PCUICSR PCUICInduction PCUICPositionEta
  PCUICInstConv PCUICContexts PCUICWeakeningConv.
From Stdlib Require Import Program.Equality.

(** * ETAK: the proved rows of the typed facts of the E reduction machine and of the E conversion

  BET-64 EtaCheckerLane, worker EtaIntegrate9, 2026-10-29. EtaHypProve proved these eight hypotheses of
  the E checker (in a file of fork/wip/etak-hypprove-2026-10-29 @ 29c23129 that this branch does not carry), each at
  [wt := welltypedE], [wfP := wf_extE]:
  - the fields [rtf_rel], [rtf_const], [rtf_cofix], [rtf_app_sort], [rtf_app_prod], [rtf_app_prim] of
    [PCUICSafeReduceEta.ReduceTypedFacts] (used by [PCUICSafeReduceEtaBridge.reduce_typed_facts_E]);
  - the fields [ctf_case_brs_length], [ctf_wf_universes] of [PCUICSafeConversionEtaFacts.ConvTypedFacts]
    (used by [PCUICSafeConversionEtaFacts.conv_typed_facts_E]).
  Their lemmas [<field>_proved], and the helpers that [ctf_wf_universes_proved] needs ([univ_*],
  [wf_universes_inst_proved], [typing_wf_universes_proved]), MOVED here from that file
  with the same names and statements. Reason: the E reduction bridge and the E conversion facts build
  their full classes from these lemmas, and this file loads only [pcuic] and [common], not the type
  checker's hypothesis bundle [PCUICTypingEtaHyps]. The registered files tie each lemma to its class field:
  the instances [PCUICSafeReduceEtaBridge.reduce_typed_facts_E] and [PCUICSafeConversionEta.conv_typed_facts_E]
  fill the fields with them, and [PCUICTypingEtaDischarge.reduce_typed_facts_discharged] is built on the first.
  Proof route changed for four lemmas, statement unchanged: [rtf_rel], [rtf_const], [rtf_app_sort] and
  [rtf_app_prod] use the landed E inversions of [PCUICInversionEta] ([inversion_RelE],
  [inversion_ConstE], [inversion_SortE], [inversion_ProdE], same conclusions as the K7 copies they
  replace), and [rtf_app_sort]/[rtf_app_prod] use [PCUICEtaA6.ws_cumul_pbE_Sort_Prod_inv] directly in
  place of K7's wrapper of it.
  No hypothesis (no [Context], no class field); [Print Assumptions] of the eight lemmas at the end. *)

(** ** Fields of [ReduceTypedFacts] ([PCUICSafeReduceEta]) at [wt := welltypedE], [wfP := wf_extE] *)

Lemma rtf_rel_proved {cf : checker_flags} :
  forall Σ Γ n, wf_extE Σ -> welltypedE Σ Γ (tRel n) -> nth_error Γ n <> None.
Proof.
  intros Σ Γ n wfΣ [T h] e.
  destruct (inversion_RelE Σ (wf_extE_wfE Σ wfΣ) h) as [decl [_ [e' _]]].
  rewrite e' in e. discriminate.
Qed.

Lemma rtf_const_proved {cf : checker_flags} :
  forall Σ Γ c u, wf_extE Σ -> welltypedE Σ Γ (tConst c u) ->
    exists decl, declared_constant Σ c decl.
Proof.
  intros Σ Γ c u wfΣ [T h].
  destruct (inversion_ConstE Σ (wf_extE_wfE Σ wfΣ) h) as [decl [_ [d _]]].
  now exists decl.
Qed.

Lemma rtf_cofix_proved {cf : checker_flags} :
  forall Σ Γ mfix idx, wf_extE Σ -> welltypedE Σ Γ (tCoFix mfix idx) ->
    nth_error mfix idx <> None.
Proof.
  intros Σ Γ mfix idx wfΣ [T h] e.
  destruct (inversion_CoFixE Σ (wf_extE_wfE Σ wfΣ) h) as (decl & _ & hn & _).
  rewrite hn in e. discriminate.
Qed.

Lemma rtf_app_sort_proved {cf : checker_flags} :
  forall Σ Γ s a, wf_extE Σ -> welltypedE Σ Γ (tApp (tSort s) a) -> False.
Proof.
  intros Σ Γ s a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  destruct (inversion_AppE Σ wfΣ' h) as (na & A & B & hf & _ & _).
  destruct (inversion_SortE Σ wfΣ' hf) as [_ [_ c]].
  exact (ws_cumul_pbE_Sort_Prod_inv Cumul c).
Qed.

Lemma rtf_app_prod_proved {cf : checker_flags} :
  forall Σ Γ na A B a, wf_extE Σ -> welltypedE Σ Γ (tApp (tProd na A B) a) -> False.
Proof.
  intros Σ Γ na A B a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  destruct (inversion_AppE Σ wfΣ' h) as (na' & A' & B' & hf & _ & _).
  destruct (inversion_ProdE Σ wfΣ' hf) as [s1 [s2 [_ [_ c]]]].
  exact (ws_cumul_pbE_Sort_Prod_inv Cumul c).
Qed.

Lemma rtf_app_prim_proved {cf : checker_flags} :
  forall Σ Γ p a, wf_extE Σ -> welltypedE Σ Γ (tApp (tPrim p) a) -> False.
Proof.
  intros Σ Γ p a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  destruct (inversion_AppE Σ wfΣ' h) as (na & A & B & hf & _ & _).
  destruct (inversion_PrimE Σ wfΣ' hf) as (pt & cd & [_ hpc hdecl hinv _ cc]).
  pose proof wfΣ' as (_ & wfr & _).
  exact (invert_cumul_prim_type_prodE (wfΣ := wfE_ClosedBodies Σ) hdecl hinv
           (prim_op_of_primitive_constant Σ _ _ wfr hpc) cc).
Qed.

(** ** Fields of [ConvTypedFacts] ([PCUICSafeConversionEtaFacts]) at [wt := welltypedE], [wfP := wf_extE] *)

Lemma ctf_case_brs_length_proved {cf : checker_flags} :
  forall Σ Γ ci p c brs, wf_extE Σ -> welltypedE Σ Γ (tCase ci p c brs) ->
      exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|.
Proof.
  intros Σ Γ ci p c brs _ [T h].
  remember (tCase ci p c brs) as t0 eqn:heqt. revert ci p c brs heqt.
  induction h; intros ci' p' c' brs' heqt; try discriminate heqt.
  - injection heqt; intros; subst.
    match goal with H : case_branch_typing _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ hbrs] end.
    exists mdecl, idecl. split; [assumption|]. apply All2i_length in hbrs. lia.
  - match goal with IH : forall ci0 p0 c0 brs0, _ = tCase ci0 p0 c0 brs0 -> _ |- _ =>
      exact (IH _ _ _ _ heqt) end.
Qed.

(** ** The universe facts of [typingE] for [ctf_wf_universes] (helpers [univ_*])

  Transport. Base proves the universe lemmas under a premise [wf Σ] that their proofs read only
  through [on_global_univs Σ.(universes)]. [univ_strip Σ] keeps the universes and the
  retroknowledge of [Σ] and drops the declarations: [wfE Σ] gives base [wf (univ_strip Σ)]
  (no declaration is left to type, [univ_wf_strip]), and every universe notion ([global_levels],
  [global_ext_levels], [wf_universes], [wf_instance], [wf_ctx_universes], [on_udecl_prop]) reads
  only [Σ.(universes)], so it is CONVERTIBLE between [Σ] and [univ_strip Σ]. The base lemma
  applied at [univ_strip Σ] therefore type-checks at [Σ]. *)

Definition univ_strip (Σ : global_env) : global_env :=
  {| universes := Σ.(universes); declarations := []; retroknowledge := Σ.(retroknowledge) |}.

Lemma univ_wf_strip {cf : checker_flags} {Σ : global_env} : wfE Σ -> wf (univ_strip Σ).
Proof.
  intros [onu [onr _]]. split; [exact onu|]. split; [exact onr|]. cbn. constructor.
Qed.

Lemma univ_extends_strip {Σ Σ' : global_env} : extends Σ Σ' -> extends (univ_strip Σ) (univ_strip Σ').
Proof.
  intros [hu _ hr]. split; [exact hu| |exact hr].
  intros c. exists []. reflexivity.
Qed.

(** U_facts [wf_universes_inst] (audit hyp-audit-C.md line 182: syntactic): base
    [PCUICWfUniverses.wf_universes_inst] at [univ_strip Σ.1]. *)
Lemma wf_universes_inst_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} (univs : universes_decl) (t : term) (u : list LevelSet.elt), wfE Σ -> on_udecl_prop Σ.1 univs -> wf_instance Σ u -> wf_universes (Σ.1, univs) t -> wf_universes Σ t@[u].
Proof.
  intros Σ univs t u wfΣ ond wfu wft.
  exact (@PCUICWfUniverses.wf_universes_inst cf (univ_strip Σ.1, Σ.2) univs t u (univ_wf_strip wfΣ) ond wfu wft).
Qed.

(** Helpers for T0 row 36 [typing_wf_universes]: the port of base [PCUICWfUniverses.wf_types]
    over [typingE_ind_env]. *)

Ltac univ_to_prop :=
  repeat match goal with
  | [ H: is_true (?x && ?y) |- _ ] =>
   let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
  end.

Ltac univ_to_wfu :=
  repeat match goal with
  | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_universe_reflect _ x)) in H
  | [ |- is_true (wf_universeb _ ?x) ] => apply (ssrbool.introT (@wf_universe_reflect _ x))
  | [ H: is_true (Sort.on_sort (wf_universeb _) _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_sort_reflect _ x)) in H
  | [ |- is_true (Sort.on_sort (wf_universeb _) _ ?x) ] => apply (ssrbool.introT (@wf_sort_reflect _ x))
  | [ H: is_true (wf_sortb _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_sort_reflect _ x)) in H
  | [ |- is_true (wf_sortb _ ?x) ] => apply (ssrbool.introT (@wf_sort_reflect _ x))
  end.

Ltac univ_specIH :=
  repeat match goal with
  | [ H : on_udecl _ _, H' : on_udecl _ _ -> _ |- _ ] => specialize (H' H)
  end.

Lemma univ_weaken_wf_universes {cf : checker_flags} {Σ Σ' : global_env} φ t :
  wfE Σ -> wfE Σ' -> extends Σ Σ' -> wf_universes (Σ, φ) t -> wf_universes (Σ', φ) t.
Proof.
  intros wfΣ wfΣ' ext.
  exact (@PCUICWfUniverses.weaken_wf_universes cf (univ_strip Σ, φ) (univ_strip Σ') t
    (univ_wf_strip wfΣ) (univ_wf_strip wfΣ') (univ_extends_strip ext)).
Qed.

(** E copy of base [PCUICWfUniverses.wf_universes_weaken] (same proof). *)
Lemma univ_wf_universes_weakenE {cf : checker_flags} :
  weaken_env_prop cumulSpecE0 (lift_typing typingE)
    (fun Σ _ j => option_default (wf_universes Σ) (j_term j) true && wf_universes Σ (j_typ j) && option_default (wf_sortb Σ) (j_univ j) true).
Proof.
  intros Σ Σ' φ wfΣ wfΣ' Hext _ j Hj.
  pose proof (fun t => @univ_weaken_wf_universes cf Σ Σ' φ t wfΣ wfΣ' Hext) as H.
  rtoProp; repeat split; auto.
  1: destruct j_term => //; cbn in *; auto.
  1: destruct j_univ => //; cbn in *; now apply (H (tSort _)).
Qed.

Lemma univ_wf_ctx_universes_closed {cf : checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {univs ctx} :
  on_udecl_prop Σ univs ->
  wf_ctx_universes (Σ, univs) ctx ->
  test_context (closedu #|polymorphic_instance univs|) ctx.
Proof.
  exact (@PCUICWfUniverses.wf_ctx_universes_closed cf (univ_strip Σ) (univ_wf_strip wfΣ) univs ctx).
Qed.

(** Base [PCUICWfUniverses.closed_ind_predicate_context] without its unused premises
    ([wf Σ], [declared_inductive]); same proof. *)
Lemma univ_closed_ind_predicate_context {ind mdecl idecl} :
  test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (ind_params mdecl) ->
  test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (ind_indices idecl) ->
  test_context (closedu #|abstract_instance (ind_universes mdecl)|) (ind_predicate_context ind mdecl idecl).
Proof.
  rewrite /ind_predicate_context; cbn.
  rewrite closedu_mkApps /=.
  rewrite closedu_abstract_instance /= => clpars clinds.
  apply/andP; split.
  * apply closedu_expand_lets_ctx. now rewrite clpars clinds.
  * apply closedu_to_extended_list_k.
    rewrite test_context_app.
    rewrite (closedu_smash_context _ _ clpars).
    apply closedu_expand_lets_ctx => //.
    now rewrite clpars.
Qed.

(** Base [PCUICWfUniverses.closedu_inds] without its unused premise [wf Σ]; same proof. *)
Lemma univ_closedu_inds {ind mdecl} :
  forallb (closedu #|abstract_instance (ind_universes mdecl)|)
    (inds ind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl)).
Proof.
  rewrite /inds.
  induction #|ind_bodies mdecl|; cbn; auto.
  rewrite IHn andb_true_r.
  eapply closedu_abstract_instance.
Qed.

(** The port of base [wf_types]. Inside a module so that the local hypothesis-naming hook
    (the E twin of base's, [PCUICWeakeningEnvTypEta.my_rename_hypE]) ends with the module
    (checked, build u5: after [End univ_WfTypesE], [rename_all_hyps] leaves a [wfE] and a
    [typingE] hypothesis unrenamed, so the parts concatenated after this one are unaffected). The
    script is base's with: [typing_ind_env] → [typingE_ind_env], [declared_*_inv] →
    [declared_*_invE], [wf_universes_weaken] → [univ_wf_universes_weakenE], [wf_universes_inst] →
    [wf_universes_inst_proved], [wf_ctx_universes_closed] / [closed_ind_predicate_context] /
    [closedu_inds] → the [univ_] helpers above. The [typeE_Cumul] case is closed by the preamble's
    [auto] from the two induction hypotheses; the conversion premise is not read. *)
Module univ_WfTypesE.

#[local] Ltac rename_hyp h ht ::= my_rename_hypE h ht.

Theorem univ_wf_typesE {cf : checker_flags} :
  env_propE (fun Σ Γ t T => wf_universes Σ t && wf_universes Σ T)
    (fun Σ _ j => lift_wfbu_term (wf_universes Σ) (wf_sortb Σ) j)
    (fun Σ Γ => wf_ctx_universes Σ Γ).
Proof.
    apply typingE_ind_env; unfold lift_wfbu_term; intros; rename_all_hyps; cbn; rewrite -!/(wf_universes _ _) ;
    univ_specIH; univ_to_prop;
    cbn; auto.

    - eapply MRReflect.introT. 1: apply lift_wfu_wfbu_term.
      apply lift_typing_subjtyp with (1 := X) => //= t T [] _ /andP[] //.

    - apply All_local_env_cst, All_forallb in X0.
      apply forallb_impl with (2 := X0) => [] [na bo ty] _ //= /andP[] //=.

    - rewrite wf_universes_lift.
      eapply forallb_nth_error with (n := n) in H0. rewrite heq_nth_error /= in H0.
      now move/andP: H0.

    - apply/andP; split; univ_to_wfu; cbn ; eauto with pcuic.

    - cbn in *; univ_to_wfu ; eauto with pcuic.
    - rewrite wf_universes_subst. constructor. univ_to_wfu; auto. constructor.
      now move/andP: H1 => [].

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constant_invE _ _ _ _ univ_wf_universes_weakenE wf X H0) as [[_ X0]%andb_and _]%andb_and.
      unshelve eapply declared_constant_to_gen in H0; eauto.
      epose proof (weaken_lookup_on_global_env' Σ.1 _ _ wf H0).
      eapply wf_universes_inst_proved. 2:eauto. all:eauto.
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_inductive_invE univ_wf_universes_weakenE wf X isdecl).
      move/onArity : X0 => /andP[] /andP[] /= _ Hind _.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      eapply wf_universes_inst_proved; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 isdecl)).
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constructor_invE univ_wf_universes_weakenE wf X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_universes_subst.
      { apply wf_universes_inds.
        now eapply consistent_instance_ext_wf. }
      move/on_ctype : onc => /andP[] /andP[] /= _ onc _.
      clear nthe. unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      eapply wf_universes_inst_proved; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 isdecl))).
      now eapply consistent_instance_ext_wf.

    - rewrite wf_universes_mkApps in H6.
      move/andP: H6 => /= [] wfu; rewrite forallb_app.
      move/andP=> [] wfpars wfinds.
      cbn in wfu.
      rewrite wfu /= wfpars wf_universes_mkApps /=
        forallb_app wfinds /= H0 /= !andb_true_r.
      pose proof (declared_inductive_invE univ_wf_universes_weakenE wf X isdecl).
      move:(onArityRed X3) => /andP[] /andP[] /= _ hty _.
      rewrite !wf_universes_it_mkProd_or_LetIn in hty.
      move/and3P: hty => [] wfp wfindis wfisort.
      have ond : on_udecl_prop Σ (ind_universes mdecl).
      { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      }
      eapply univ_wf_ctx_universes_closed in wfp => //.
      eapply univ_wf_ctx_universes_closed in wfindis => //.
      rewrite (consistent_instance_length H2).
      erewrite closedu_compare_decls; tea.
      rewrite univ_closed_ind_predicate_context // /=.
      unfold test_branch.
      apply/andP; split.
      * have wfbrctx : All (fun cdecl =>
          test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (cstr_args cdecl))
          (ind_ctors idecl).
        { pose proof (onConstructors := onConstructors X3).
          clear -wf ond onConstructors.
          red in onConstructors. solve_all. destruct X.
          move : on_ctype => /andP[] /andP[] /= _ wfty _.
          rewrite cstr_eq in wfty.
          rewrite !wf_universes_it_mkProd_or_LetIn in wfty.
          move/and3P: wfty => [] _ clargs _.
          apply univ_wf_ctx_universes_closed in clargs => //. }
        solve_all.
        erewrite closedu_compare_decls; [|tea].
        rewrite /cstr_branch_context.
        eapply closedu_expand_lets_ctx.
        rewrite wfp. eapply closedu_subst_context.
        rewrite a.
        now rewrite univ_closedu_inds.
      * rewrite wf_universes_it_mkLambda_or_LetIn H7 andb_true_r.
        move: H4.
        rewrite /wf_ctx_universes forallb_app => /andP[hctx _].
        apply (MRReflect.introT onctxP).
        solve_all. unfold ondecl, wf_decl_universes, on_decl_universes in *.
        move/andP:H3 => [Hb Ht] //; split; tas.
        now destruct decl_body.

    - rewrite /subst1. rewrite wf_universes_subst.
      constructor => //. eapply All_rev.
      rewrite wf_universes_mkApps in H2.
      move/andP: H2 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_invE univ_wf_universes_weakenE wf X isdecl).
      destruct (declared_inductive_invE); simpl in *.
      destruct ind_ctors as [|cs []] => //.
      destruct ind_cunivs as [|cunivs []] => //;
      destruct X0 as [[[? ?] ?] ?] => //.
      red in o0.
      destruct nth_error eqn:heq => //.
      destruct o0  as [_ ->].
      rewrite wf_universes_mkApps {1}/wf_universes /= -!/(wf_universes _ _)
        wf_universeb_instance_forall in H2.
      move/andP: H2 => [/wf_instanceP wfu wfargs].
      unshelve eapply declared_projection_to_gen in isdecl; eauto.
      eapply (wf_universes_inst_proved (ind_universes mdecl)); eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 (proj1 isdecl)))).
      rewrite wf_universes_subst.
      eapply wf_universes_inds; eauto.
      eapply wf_abstract_instance.
      rewrite wf_universes_subst. apply wf_projs.
      rewrite wf_universes_lift.
      rewrite smash_context_app smash_context_acc in heq.
      autorewrite with len in heq. rewrite nth_error_app_lt in heq.
      autorewrite with len. lia.
      rewrite PCUICSubstitution.nth_error_subst_context in heq.
      autorewrite with len in heq. simpl in heq.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl)) _ _).
      autorewrite with len in H0. simpl in H0. rewrite -> H0 in heq. clear H0.
      autorewrite with len in heq.
      simpl in heq.
      destruct nth_error eqn:hnth; simpl in * => //.
      noconf heq. simpl.
      rewrite wf_universes_subst.
      apply wf_extended_subst.
      move:onArityRed => /andP[] /andP[] /= _ Hs _.
      rewrite !wf_universes_it_mkProd_or_LetIn in Hs.
      now move/andP: Hs => /andP /andP [].
      rewrite wf_universes_lift.
      eapply PCUICWfUniverses.wf_universes_local_ctx_smash in s.
      eapply wf_universes_local_ctx_nth_error in s; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - apply/andP; split; eauto.
      destruct X0; cbn => //.
      rtoProp; intuition eauto. solve_all.
      destruct X0; cbn => //.
      simp prim_type. cbn. rtoProp; intuition.
Qed.

End univ_WfTypesE.

(** T0 row 36 [typing_wf_universes]: base [PCUICWfUniverses.typing_wf_universes] over the port. *)
Lemma typing_wf_universes_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ : context} {t : term} {T : term}, wfE Σ -> Σ;;; Γ |-E t : T -> wf_universes Σ t && wf_universes Σ T.
Proof.
  intros Σ Γ t T wfΣ Hty.
  exact (env_propE_typing univ_WfTypesE.univ_wf_typesE _ wfΣ _ _ _ Hty).
Qed.

(** [ConvTypedFacts.ctf_wf_universes] of EtaConv's [PCUICSafeConversionEtaFacts.v] @ [c7cbbe73] (class not
    in this branch), at [wt := welltypedE], [wfP := wf_extE]: row 36, as the base instance
    [conv_typed_facts_base] does with base [typing_wf_universes]. *)
Lemma ctf_wf_universes_proved {cf : checker_flags} :
  forall Σ Γ t, wf_extE Σ -> welltypedE Σ Γ t -> wf_universes Σ t.
Proof.
  intros Σ Γ t wfΣ [T typ].
  pose proof (typing_wf_universes_proved (Σ := Σ) (fst wfΣ) typ) as h.
  apply andb_prop in h as [h _]. exact h.
Qed.

(** ** No hypothesis: Rocq's primitive-type axioms and [functional_extensionality_dep] at most *)

Print Assumptions rtf_rel_proved.
Print Assumptions rtf_const_proved.
Print Assumptions rtf_cofix_proved.
Print Assumptions rtf_app_sort_proved.
Print Assumptions rtf_app_prod_proved.
Print Assumptions rtf_app_prim_proved.
Print Assumptions ctf_case_brs_length_proved.
Print Assumptions ctf_wf_universes_proved.
