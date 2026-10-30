(* Distributed under the terms of the MIT license.   *)

(** * Strengthening of bidirectional typing over the η relations (plan row T6): the E copy of
    [BDStrengthening]

  A copy of base [Bidirectional/BDStrengthening.v] over the landed bidirectional E judgments
  ([BDTypingEta]): [wf] → [wfE], [wf_local] → [wf_localE], [typing] → [typingE], the
  bidirectional judgments → their E copies, [env_prop_bd] → [env_prop_bdE], [renaming] →
  [renamingE] ([PCUICRenameTypEta]), and the unscoped algorithmic [Σ ;;; Γ |- T <= T']
  ([cumulAlgo]) → [JoinE Σ Γ Cumul T T'] (the canonical I5 join, stream lead's ruling
  2026-10-29 09:26Z, as in [checkingE]). Nothing else changes in a statement; each name takes the
  suffix [E] (plan [t0-plan.md] §2, D1). Map, base → E: [on_free_vars_case_predicate_context],
  [on_free_vars_case_branch_context], [on_free_vars_case_branch_type],
  [bidirectional_on_free_vars], [infering_on_free_vars], [infering_prod_on_free_vars],
  [on_free_vars_type], [rename_mfix_on_ind_red], [rename_telescope], [bidirectional_renaming],
  [typing_renaming_cond_P], [strengthening], [strengthening_type] → the same name with [E].

  Base lemmas NOT copied, because they mention neither typing, conversion nor [wf] (they are
  imported from base [BDStrengthening] and used as they are): [shiftnP_shiftn],
  [on_free_vars_rename], [Alli_impl_le], [addnP_strengthen_lift], [on_ctx_free_vars_strengthenP],
  [on_free_vars_ctx_tip], [on_free_vars_it_mkLambda_or_LetIn], [substP_shiftnP],
  [on_free_vars_subst], [on_free_vars_subst0], [unlift_renaming], [unlift], [lift_unlift],
  [lift_unlift_term], [lift_unlift_context], [closedn_ctx_lift_inv], [urenaming_strengthen].
  ([PCUICEtaStrengthening] declares objects under some of these base names; it is loaded here
  (through [PCUICEtaT8Probe]) but not imported. The same-name pass finds three shared names that
  this file references, [lift_unlift_term], [on_ctx_free_vars_strengthenP] and
  [urenaming_strengthen]; every reference to them is written [BDStrengthening.]-qualified, as in
  the base proof's objects (cross-lane-commitments.md C6, class (A)).)

  ** The renaming of the join (new statements, the E twins of base [conv_renameP] and
  [cumul_renameP])

  Base renames the algorithmic conversion by renaming its [red1] steps ([PCUICRenameConv.v:1118,
  1141]). [JoinE] runs [(R_c ∪ eta1)*] from [canon] on either side and ends in U1': each [R_c]
  step is a [red1] step, renamed by [red1_rename_cb], followed by [canon], which commutes with
  renaming ([canon_rename]); each [eta1] step is renamed by [eta1_rename] (proved here, by the
  induction of [eta1_lift]); the end comparison is stable under any substitution
  ([finst_inst]); the scoping of the intermediate terms is [red1_on_free_vars_cb],
  [canon_on_free_vars] and [eta1_on_free_vars]. This is [JoinE_renameP]; [conv_renamePE] and
  [cumul_renamePE] are it at [Conv] and [Cumul], with base's premises, [ClosedBodies Σ.1] (an
  implicit instance, from [wfE] by [wfE_ClosedBodies]) in place of base's [wf Σ.1] (Class B).

  ** Proof routes that differ from base (statements do not)

  - Reduction facts under [wf Σ] are used under [ClosedBodies Σ]: [red_rename_cb],
    [PCUICClosedTyp.red_on_free_vars_cb]; closedness facts are the [wfE] ones of
    [PCUICClosedTypEta] ([declared_inductive_closed_paramsE], [declared_constructor_closedE],
    [closed_cstr_branch_contextE], ...).
  - [ind_npars mdecl = context_assumptions (ind_params mdecl)]: base reads it from the
    declaration's [onNpars] ([on_declared_minductive], [PCUICInductives.oi], under [wf]); here
    [declared_minductive_ind_nparsE].
  - [strengthening_typeE]: base inverts the cumulativity [T' ≤ tSort s] into a reduct of [T'] by
    [PCUICConversion.ws_cumul_pb_Sort_r_inv] (base confluence). Over η its raw form is false; its
    typed form is T8. Here it is [PCUICEtaT8Probe.T8_Sort_r_two] (with [subject_reductionE]),
    whose premise [T' : tSort _] is the validity of [HT], the typing of the lifted term at [T'],
    in the context of the comparison ([lanes/eta/meta/t8-consumers.md] §3.4,
    [BDStrengthening.v:1110]). Base's [cumulAlgo_cumulSpec]/[ws_cumul_pb_red_r_inv] on the
    reduct is [red_ws_cumul_pbE] then [ws_cumul_pbE_forget_spec].

  ** No forecast class

  [on_free_vars_typeE], [typing_renaming_cond_PE], [strengtheningE] and [strengthening_typeE] use
  soundness, completeness, validity and subject reduction, so they took the forecast class of
  [BDToPCUICEta] (T1's [SRForecastCopy18], copy 18b) as a section [Context] until copy 18b landed
  (frac/eta 3e6b422d); it was deleted after a compiled-form identity check of each field. The
  scoping and renaming lemmas never used one. This file adds no class. *)

From Stdlib Require Import Bool List Arith Lia.
From Stdlib Require String.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICGlobalEnv PCUICOnOne PCUICReduction
  PCUICTactics PCUICCumulativity
  PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICSigmaCalculus PCUICOnFreeVars PCUICClosed PCUICConfluence PCUICSpine PCUICInductiveInversion PCUICParallelReductionConfluence PCUICWellScopedCumulativity PCUICClosed PCUICRenameDef PCUICInstConv PCUICClosedTyp PCUICWeakeningEnvTyp PCUICRenameTyp PCUICRenameConv PCUICGuardCondition PCUICWeakeningConv.
From MetaRocq.PCUIC Require PCUICOnFreeVarsConv.

From MetaRocq.PCUIC Require Import BDTyping BDToPCUIC BDFromPCUIC BDStrengthening.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICEtaDefs PCUICEtaScope
  PCUICEtaCanon PCUICEtaCanonRed PCUICEtaI5 PCUICWsCumulEtaSubst PCUICWellScopedCumulativityEta
  PCUICRenameTypEta PCUICValidityEta PCUICSREta BDTypingEta BDToPCUICEta BDFromPCUICEta.
From MetaRocq.PCUIC Require PCUICEtaT8Probe.

From Stdlib Require Import ssreflect ssrbool.
From Stdlib.Program Require Import Equality.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** One η step under a renaming (syntactic) *)

Lemma eta1_rename t t' : eta1 t t' -> forall f, eta1 (rename f t) (rename f t').
Proof.
  intros H. revert t t' H.
  apply (eta1_ind_all (fun t t' => forall f, eta1 (rename f t) (rename f t'))); intros.
  - change (eta1 (tLambda na (rename f A) (tApp (rename (shiftn 1 f) (lift0 1 t)) (tRel 0))) (rename f t)).
    rewrite (rename_shiftn f 1 t). apply eta_red.
  - cbn. apply abs_eta_l; auto.
  - cbn. apply abs_eta_r; auto.
  - cbn. apply letin_eta_def; auto.
  - cbn. apply letin_eta_ty; auto.
  - cbn. apply letin_eta_body; auto.
  - change (eta1 (tCase ci (rename_predicate f p) (rename f c) (rename_branches f brs))
      (tCase ci (set_pparams (rename_predicate f p) (map (rename f) params')) (rename f c)
        (rename_branches f brs))).
    eapply case_eta_param. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy f).
  - change (eta1 (tCase ci (rename_predicate f p) (rename f c) (rename_branches f brs))
      (tCase ci (set_preturn (rename_predicate f p) (rename (shiftn #|pcontext p| f) preturn'))
        (rename f c) (rename_branches f brs))).
    eapply case_eta_return. cbn. auto.
  - cbn. apply case_eta_discr; auto.
  - change (eta1 (tCase ci (rename_predicate f p) (rename f c) (rename_branches f brs))
      (tCase ci (rename_predicate f p) (rename f c) (rename_branches f brs'))).
    eapply case_eta_brs. induction X; cbn.
    + constructor. destruct p0 as [[He HP] Heq]. split; cbn.
      * rewrite Heq. apply HP.
      * exact Heq.
    + now constructor.
  - cbn. apply proj_eta; auto.
  - cbn. apply app_eta_l; auto.
  - cbn. apply app_eta_r; auto.
  - cbn. apply prod_eta_l; auto.
  - cbn. apply prod_eta_r; auto.
  - cbn. eapply evar_eta. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy f).
  - change (eta1 (tFix (map (map_def (rename f) (rename (shiftn #|mfix0| f))) mfix0) idx)
      (tFix (map (map_def (rename f) (rename (shiftn #|mfix1| f))) mfix1) idx)).
    rewrite (OnOne2_length X). eapply fix_eta_ty.
    set (D := shiftn #|mfix1| f). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - change (eta1 (tFix (map (map_def (rename f) (rename (shiftn #|mfix0| f))) mfix0) idx)
      (tFix (map (map_def (rename f) (rename (shiftn #|mfix1| f))) mfix1) idx)).
    rewrite (OnOne2_length X). eapply fix_eta_body.
    set (D := shiftn #|mfix1| f). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - change (eta1 (tCoFix (map (map_def (rename f) (rename (shiftn #|mfix0| f))) mfix0) idx)
      (tCoFix (map (map_def (rename f) (rename (shiftn #|mfix1| f))) mfix1) idx)).
    rewrite (OnOne2_length X). eapply cofix_eta_ty.
    set (D := shiftn #|mfix1| f). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - change (eta1 (tCoFix (map (map_def (rename f) (rename (shiftn #|mfix0| f))) mfix0) idx)
      (tCoFix (map (map_def (rename f) (rename (shiftn #|mfix1| f))) mfix1) idx)).
    rewrite (OnOne2_length X). eapply cofix_eta_body.
    set (D := shiftn #|mfix1| f). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. eapply array_eta_val. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy f).
  - cbn. eapply array_eta_def; cbn; auto.
  - cbn. eapply array_eta_type; cbn; auto.
Qed.

(** ** The join under a renaming *)

Section JoinERename.

  Context {cf : checker_flags} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ}.

  Lemma RE_renameP P Γ Δ f a b :
    urenaming P Γ Δ f -> on_ctx_free_vars P Γ -> on_free_vars P a ->
    clos_refl_trans (union (R_c Σ Γ) eta1) a b ->
    clos_refl_trans (union (R_c Σ Δ) eta1) (rename f a) (rename f b) × on_free_vars P b.
  Proof.
    intros hf hΓ ha h. apply clos_rt_rt1n_iff in h.
    induction h as [a|a a1 b s _ IH].
    - split; [apply rt_refl|exact ha].
    - have ha1 : on_free_vars P a1.
      { destruct s as [[b0 [hr ->]]|he].
        + apply canon_on_free_vars. exact (red1_on_free_vars_cb hr ha hΓ).
        + exact (eta1_on_free_vars a a1 he P ha). }
      destruct (IH ha1) as [IHr IHo]. split; [|exact IHo].
      eapply rt_trans; [|exact IHr]. apply rt_step.
      destruct s as [[b0 [hr ->]]|he].
      + left. exists (rename f b0). split.
        * exact (red1_rename_cb P Σ Γ Δ a b0 f cbΣ hf ha hr).
        * now rewrite canon_rename.
      + right. now apply eta1_rename.
  Qed.

  (** [JoinE] is stable under a renaming of a [P]-scoped context (see the header). *)
  Lemma JoinE_renameP P Γ Δ f pb t u :
    urenaming P Γ Δ f -> on_ctx_free_vars P Γ -> on_free_vars P t -> on_free_vars P u ->
    JoinE Σ Γ pb t u -> JoinE Σ Δ pb (rename f t) (rename f u).
  Proof.
    intros hf hΓ ht hu (v & v' & hv & hv' & e).
    destruct (RE_renameP P Γ Δ f _ _ hf hΓ (canon_on_free_vars P t ht) hv) as [hv1 _].
    destruct (RE_renameP P Γ Δ f _ _ hf hΓ (canon_on_free_vars P u hu) hv') as [hv1' _].
    exists (rename f v), (rename f v'). rewrite !canon_rename.
    split; [exact hv1|]. split; [exact hv1'|].
    rewrite (rename_inst f v) (rename_inst f v'). now apply finst_inst.
  Qed.

End JoinERename.

(** Base [conv_renameP] ([PCUICRenameConv.v:1118]): [Σ ;;; Γ |- A = B] → [JoinE Σ Γ Conv A B],
    [wf Σ.1] → the instance [ClosedBodies Σ.1] (Class B). *)
Lemma conv_renamePE {cf} {P Σ Γ Δ f A B} {cbΣ : ClosedBodies Σ.1} :
  urenaming P Γ Δ f ->
  on_free_vars P A ->
  on_free_vars P B ->
  on_ctx_free_vars P Γ ->
  JoinE Σ Γ Conv A B ->
  JoinE Σ Δ Conv (rename f A) (rename f B).
Proof. intros hf hA hB hΓ h. exact (JoinE_renameP P Γ Δ f Conv A B hf hΓ hA hB h). Qed.

(** Base [cumul_renameP] ([PCUICRenameConv.v:1141]): [Σ ;;; Γ |- A <= B] → [JoinE Σ Γ Cumul A B],
    [wf Σ.1] → the instance [ClosedBodies Σ.1] (Class B). *)
Lemma cumul_renamePE {cf} {P Σ Γ Δ f A B} {cbΣ : ClosedBodies Σ.1} :
  urenaming P Γ Δ f ->
  on_free_vars P A ->
  on_free_vars P B ->
  on_ctx_free_vars P Γ ->
  JoinE Σ Γ Cumul A B ->
  JoinE Σ Δ Cumul (rename f A) (rename f B).
Proof. intros hf hA hB hΓ h. exact (JoinE_renameP P Γ Δ f Cumul A B hf hΓ hA hB h). Qed.

(** ** Free variables of the case contexts *)

(** Base [on_free_vars_case_predicate_context] ([BDStrengthening.v:166]). *)
Lemma on_free_vars_case_predicate_contextE `{checker_flags} Σ ci mdecl idecl p P :
  wfE Σ ->
  declared_inductive Σ ci mdecl idecl ->
  forallb (on_free_vars P) (pparams p) ->
  wf_predicate mdecl idecl p ->
  eq_context_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  on_free_vars_ctx P (case_predicate_context ci mdecl idecl p).
Proof.
  intros wfΣ decli hpars wfp eqctx.
  rewrite /case_predicate_context /case_predicate_context_gen /pre_case_predicate_context_gen /inst_case_context.
  erewrite <- on_free_vars_map2_cstr_args.
  2: rewrite fold_context_k_length !length_map ; eapply All2_length ; tea.
  apply on_free_vars_ctx_subst_context0.
  2: by rewrite forallb_rev.
  rewrite on_free_vars_ctx_subst_instance List.length_rev.
  apply closedn_ctx_on_free_vars_shift.
  replace #|pparams p| with (context_assumptions (ind_params mdecl)).
  1: eapply PCUICClosed.closed_ind_predicate_context ; [exact decli|].
  1: exact (declared_minductive_closedE (proj1 decli)).
  erewrite wf_predicate_length_pars ; tea.
  now rewrite (declared_minductive_ind_nparsE (proj1 decli)).
Qed.

(** Base [on_free_vars_case_branch_context] ([BDStrengthening.v:190]). *)
Lemma on_free_vars_case_branch_contextE `{checker_flags} {Σ : global_env_ext } {wfΣ : wfE Σ} {P ci mdecl idecl p br cdecl} :
   let brctx := case_branch_context ci.1 mdecl p (forget_types (bcontext br)) cdecl in
   declared_constructor Σ ci mdecl idecl cdecl ->
   wf_predicate mdecl idecl p ->
   wf_branch cdecl br ->
   forallb (on_free_vars P) (pparams p) ->
   on_free_vars_ctx P brctx.
Proof.
  destruct ci as [ind i].
  intros brctx decli wfp wfb havp.
  rewrite /brctx /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
  rewrite -on_free_vars_map2_cstr_args.
  { len. by apply wf_branch_length. }
  eapply on_free_vars_ctx_inst_case_context ; tea.
  1: reflexivity.
  rewrite test_context_k_closed_on_free_vars_ctx -closedn_ctx_on_free_vars.
  erewrite wf_predicate_length_pars ; eauto.
  rewrite (declared_minductive_ind_nparsE (proj1 (proj1 decli))).
  exact (closed_cstr_branch_contextE decli).
Qed.

(** Base [on_free_vars_case_branch_type] ([BDStrengthening.v:243]). *)
Lemma on_free_vars_case_branch_typeE `{checker_flags} {Σ : global_env_ext } {wfΣ : wfE Σ} {P} {ci : case_info} {mdecl idecl p br i cdecl} :
  let predctx := case_predicate_context ci mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx (preturn p) in
  let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
  declared_constructor Σ (ci.(ci_ind),i) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  eq_context_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  wf_branch cdecl br ->
  forallb (on_free_vars P) (pparams p) ->
  on_free_vars (shiftnP #|pcontext p| P) (preturn p) ->
  on_free_vars (shiftnP #|bcontext br| P) brctxty.2.
Proof.
  intros predctx ptm brctxty decli wfp allctx wfb havp havr.
  rewrite /brctxty /case_branch_type /case_branch_type_gen /=.
  rewrite on_free_vars_mkApps.
  apply /andP ; split.
  2: rewrite forallb_app ; apply /andP ; split.
  - erewrite wf_branch_length by eassumption.
    eapply on_free_vars_lift0.
    rewrite addnP_shiftnP /ptm on_free_vars_it_mkLambda_or_LetIn.
    apply /andP ; split.
    + rewrite /predctx.
      eapply on_free_vars_case_predicate_contextE.
      all: tea.
      apply decli.
    + rewrite /predctx.
      rewrite case_predicate_context_length.
      all: eassumption.

  - repeat rewrite !forallb_map.
    epose proof (declared_constructor_closed_indicesE decli).
    eapply forallb_impl ; tea.
    intros.
    rewrite (wf_branch_length wfb).
    apply on_free_vars_subst.
    1: by rewrite forallb_rev.
    rewrite List.length_rev /expand_lets_k -shiftnP_add.
    assert (#|pparams p| = (context_assumptions (subst_instance (puinst p) (ind_params mdecl)))) as ->.
    { rewrite context_assumptions_subst_instance -(declared_minductive_ind_nparsE (proj1 (proj1 decli))).
      now eapply wf_predicate_length_pars. }
    apply on_free_vars_subst.
    + eapply foron_free_vars_extended_subst.
      rewrite on_free_vars_ctx_subst_instance.
      eapply closed_ctx_on_free_vars, declared_inductive_closed_paramsE.
      by eapply decli.
    + rewrite extended_subst_length subst_instance_length context_assumptions_subst_instance.
      rewrite shiftnP_add Nat.add_comm.
      apply on_free_vars_lift_impl.
      rewrite Nat.add_comm.
      apply on_free_vars_subst.
      1:{
        eapply forallb_impl ; [|eapply closed_inds].
        intros ; by apply closed_on_free_vars.
      }
      len.
      rewrite on_free_vars_subst_instance.
      apply closedn_on_free_vars.
      by rewrite Nat.add_comm Nat.add_assoc.

  - rewrite /= andb_true_r on_free_vars_mkApps.
    apply /andP ; split => //.
    rewrite forallb_app.
    apply /andP ; split.
    + rewrite forallb_map.
      eapply forallb_impl ; tea.
      intros.
      by rewrite on_free_vars_lift0 // (wf_branch_length wfb) addnP_shiftnP.
    + rewrite (wf_branch_length wfb).
      by apply on_free_vars_to_extended_list.

Qed.

(** ** Free variables of inferred types *)

Section OnFreeVars.

  Context `{cf : checker_flags} (Σ : global_env_ext) (wfΣ : wfE Σ).

  Let Pinfer Γ t T :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P T.

  Let Psort (Γ : context) (t : term) (u : sort) := True.

  Let Pprod Γ t (na : aname) A B :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.

  Let Pind Γ (ind : inductive) t (u : Instance.t) args :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    All (on_free_vars P) args.

  Let Pcheck (Γ : context) (t : term) (T : term) := True.

  Let Pj (Γ : context) (j : judgment) := True.

  Let PΓ (Γ : context) :=
    True.

  Let PΓ_rel (Γ Γ' : context) := True.

  (** Base [bidirectional_on_free_vars] ([BDStrengthening.v:385]). *)
  Theorem bidirectional_on_free_varsE : env_prop_bdE Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
  Proof using wfΣ.
    apply bidir_ind_envE.

    - constructor.

    - constructor.

    - constructor.

    - intros. red.
      intros P HΓ Hn.
      eapply alli_Alli, Alli_nth_error in HΓ ; tea.
      apply on_free_vars_lift0.
      by move: HΓ => /implyP /(_ Hn) /andP [].

    - easy.
    - easy.
    - intros until bty.
      move => _ _ _ Hbty ? ? /= /andP [] ? ?.
      apply /andP ; split ; tea.
      apply Hbty ; tea.
      rewrite on_ctx_free_vars_snoc.
      apply /andP ; split ; tea.

    - intros until A.
      move => _ _ _ Ht ? ? /= /andP [] ? /andP [] ? ?.
      repeat (apply /andP ; split ; tea).
      apply Ht ; tea.
      rewrite on_ctx_free_vars_snoc.
      repeat (apply /andP ; split ; tea).

    - intros until u.
      move => _ HAB _ _ ? ? /= /andP [] ? ?.
      edestruct HAB ; tea.
      apply on_free_vars_subst1 ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_constant_closed_typeE ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_inductive_closed_typeE ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      eapply declared_constructor_closed_typeE ; tea.

    - intros.
      move => ? ? /= /and5P [] ? ? Hctx ? ?.
      rewrite on_free_vars_mkApps.
      apply /andP ; split.
      + rewrite on_free_vars_it_mkLambda_or_LetIn.
        rewrite test_context_k_closed_on_free_vars_ctx -closedn_ctx_on_free_vars in Hctx.
        apply /andP ; split.
        2: by rewrite case_predicate_context_length.
        eapply on_free_vars_case_predicate_contextE ; eassumption.

      + rewrite forallb_app.
        apply /andP ; split.
        2: by rewrite /= andb_true_r.
        apply All_forallb, All_skipn.
        auto.

    - intros until args.
      move => ? _ ? largs ? ? ?.
      apply on_free_vars_subst0.
      + cbn ; apply /andP ; split ; auto.
        rewrite forallb_rev.
        apply All_forallb.
        auto.
      + eapply closedn_on_free_vars.
        rewrite closedn_subst_instance /= List.length_rev largs.
        eapply declared_projection_closed_typeE ; tea.

    - intros until decl.
      move => ? ndec ? ? ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].

    - intros until decl.
      move => ? ndec ? ? ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].

    - intros. red. intros. destruct X0; cbn => //.
      simp prim_type. cbn in *. solve_all.
    - easy.

    - intros ? ? ? ? ? ? _ HT Hred.
      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply PCUICClosedTyp.red_on_free_vars_cb in Hred ; tea.
      by move: Hred => /= /andP [].
    - intros ? ? ? ? ? ? _ HT Hred.
      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply PCUICClosedTyp.red_on_free_vars_cb in Hred ; tea.
      rewrite on_free_vars_mkApps in Hred.
      by move: Hred => /= /forallb_All.

    - easy.

  Qed.

  (** Base [infering_on_free_vars] ([BDStrengthening.v:500]). *)
  Lemma infering_on_free_varsE P Γ t T :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |-E t ▹ T ->
    on_free_vars P T.
  Proof using wfΣ.
    intros.
    edestruct bidirectional_on_free_varsE as (_&_&_&_&p&_).
    eapply p ; eauto.
  Qed.

  (** Base [infering_prod_on_free_vars] ([BDStrengthening.v:511]). *)
  Lemma infering_prod_on_free_varsE P Γ t na A B :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |-E t ▹Π (na,A,B) ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.
  Proof using wfΣ.
    intros.
    eapply bidirectional_on_free_varsE ; eauto.
  Qed.

End OnFreeVars.

(** Base [rename_mfix_on_ind_red] ([BDStrengthening.v:541]). *)
Lemma rename_mfix_on_ind_redE `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {check ok} P Γ Δ f (mfix : mfixpoint term) :
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  All (fun d => on_free_vars P (dtype d)) mfix ->
  (forall d m, check d = Some m ->
    check (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some m) ->
  mfix_on_ind check (PCUICReduction.red Σ Γ) ok mfix ->
  mfix_on_ind check (PCUICReduction.red Σ Δ) ok
    (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  intros hf hΓ hop hcheck.
  apply (mfix_on_ind_map _ _ _ hop); [|easy].
  intros d m hT [ty [hc hred]].
  exists (rename f ty); split.
  - rewrite map_def_with_type. now apply hcheck.
  - cbn. eapply (red_rename_cb _ _ _ _ _ _ _ (wfE_ClosedBodies Σ)) ; tea.
Qed.

Section BDRenaming.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wfE Σ).

Let Pinfer Γ t T :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |-E rename f t ▹ rename f T.

Let Psort Γ t u :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |-E rename f t ▹□ u.

Let Pprod Γ t na A B :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |-E rename f t ▹Π (na,rename f A,rename (shiftn 1 f) B).

Let Pind Γ ind t u args :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |-E rename f t ▹{ind} (u, map (rename f) args).


Let Pcheck Γ t T :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  on_free_vars P T ->
  Σ ;;; Δ |-E rename f t ◃ rename f T.

Let Pj Γ j :=
  forall P Δ f,
    urenaming P Γ Δ f ->
    on_ctx_free_vars P Γ ->
    lift_sorting
      (fun t T => on_free_vars P t -> on_free_vars P T -> Σ ;;; Δ |-E rename f t ◃ rename f T)
      (fun T u => on_free_vars P T -> Σ ;;; Δ |-E rename f T ▹□ u) j.

Let PΓ := All_local_env Pj.

Let PΓ_rel Γ Γ' :=
  forall P Δ f,
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars_ctx P Γ' ->
  wf_local_bd_relE Σ Δ (rename_context f Γ').

(** Base [rename_telescope] ([BDStrengthening.v:620]). *)
Lemma rename_telescopeE P f Γ Δ tel tys:
  urenaming P Γ Δ f ->
  on_ctx_free_vars P Γ ->
  forallb (on_free_vars P) tys ->
  on_free_vars_ctx P (List.rev tel) ->
  PCUICTyping.ctx_inst Pcheck Γ tys tel ->
  PCUICTyping.ctx_inst (checkingE Σ) Δ (map (rename f) tys) (PCUICSigmaCalculus.rename_telescope f tel).
Proof using Type.
  intros ur hΓ htys htel ins.
  induction ins in Δ, ur, hΓ, htys, htel |- *.
  - constructor.
  - rewrite rename_telescope_cons /=.
    move: htys => /= /andP [] ? ?.
    rewrite /= on_free_vars_ctx_app on_free_vars_ctx_tip /= in htel.
    move : htel => /andP [] ? ?.
    constructor.
    1: eauto.
    rewrite -(rename_subst_telescope _ [_]).
    apply IHins ; tea.
    rewrite -subst_context_subst_telescope.
    apply on_free_vars_ctx_subst_context0.
    1: assumption.
    by rewrite /= andb_true_r.
  - rewrite rename_telescope_cons /=.
    rewrite /= on_free_vars_ctx_app on_free_vars_ctx_tip /= in htel.
    move : htel => /andP [] /andP [] /= ? ? ?.
    constructor.
    rewrite -(rename_subst_telescope _ [_]).
    apply IHins ; tea.
    rewrite -subst_context_subst_telescope.
    apply on_free_vars_ctx_subst_context0.
    1: assumption.
    by rewrite /= andb_true_r.
Qed.

(** Base [bidirectional_renaming] ([BDStrengthening.v:655]). *)
Theorem bidirectional_renamingE : env_prop_bdE Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
Proof using wfΣ.
  apply bidir_ind_envE.

  - intros Γ j Hj P Δ f hf hΓ.
    apply lift_sorting_impl with (1 := Hj) => //; intros ?? [Ht IHt] **.
    all: eapply IHt; eauto.

  - intros Γ _ _ hΓ. red.
    apply All_local_env_impl with (1 := hΓ); clear Γ hΓ.
    intros Γ j Hj P Δ f hf hΓ'.
    apply lift_sorting_impl with (1 := Hj) => //; intros ?? IHt **.
    all: eapply IHt; eauto.

  - intros Γ Γ' _ _ HΓ P Δ f hf hΓ hΓ'.
    apply All_local_env_fold. change (fold_context_k _ ?Γ) with (rename_context f Γ).
    induction HΓ in hΓ' |- * using All_local_rel_ind1. 1: constructor.
    rewrite on_free_vars_ctx_snoc in hΓ'. move/andP: hΓ' => [hΓ'] /andP [onb ont].
    apply All_local_env_snoc; auto.
    eapply urenaming_context in hf ; tea.
    apply lift_sorting_f_it_impl with X => //.
    1: destruct decl_body => //; cbn in onb |- *.
    all: intros IHt; eapply IHt; eauto.
    all: rewrite on_ctx_free_vars_concat hΓ /= on_free_vars_ctx_on_ctx_free_vars //.

  - intros Γ n decl isdecl P Δ f hf hΓ ht.
    eapply hf in isdecl as h => //.
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto.

  - intros. red. intros. cbn in *.
    by constructor.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor.
    { specialize (X0 _ _ _ hf hΓ).
      eapply lift_sorting_f_it_impl with X0 => //= IH. now apply IH. }
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor ; eauto.
    { specialize (X0 _ _ _ hf hΓ).
      eapply lift_sorting_f_it_impl with X0 => //= IH. now apply IH. }
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? /andP [] ? ?.
    econstructor ; eauto.
    { specialize (X0 _ _ _ hf hΓ).
      eapply lift_sorting_f_it_impl with X0 => //= IH. all: now apply IH. }
    eapply X2 ; tea.
    1: by apply urenaming_vdef.
    rewrite on_ctx_free_vars_snoc.
    repeat (apply /andP ; split ; tea).

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    rewrite rename_subst0 ; cbn.
    econstructor ; eauto.
    eapply X2 ; tea.
    eapply infering_prod_on_free_varsE.
    4: eassumption.
    all: assumption.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_constant_closed_typeE ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_inductive_closed_typeE ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= _.
    erewrite rename_closed.
    2: by eapply declared_constructor_closed_typeE ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] on_pars /andP [] ? /andP [] ? /andP [] ? /forallb_All on_brs.
    rewrite rename_mkApps rename_it_mkLambda_or_LetIn map_app map_skipn /=.
    rewrite rename_case_predicate_contextE // case_predicate_context_length // rename_predicate_preturn.
    econstructor ; eauto.
    + eapply X2 ; tea.
      * rewrite -rename_case_predicate_contextE //.
        erewrite <- case_predicate_context_length ; tea.
        apply urenaming_context ; assumption.
      * erewrite <- case_predicate_context_length ; tea.
        rewrite /predctx.
        erewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        rewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply on_free_vars_case_predicate_contextE ; tea.
    + by eapply rename_wf_predicate.
    + rewrite -rename_case_predicate_contextE ; tea.
      eapply X5 ; tea.
      eapply on_free_vars_case_predicate_contextE ; tea.
    + rewrite -[subst_instance _ _](rename_closedn_ctx f 0).
      { pose proof (declared_inductive_closed_paramsE H).
        now rewrite closedn_subst_instance_context. }
      rewrite rename_context_telescope rename_telescope_shiftn0 /=.
      eapply rename_telescopeE ; tea.
      rewrite rev_involutive.
      rewrite on_free_vars_ctx_subst_instance.
      eapply closed_ctx_on_free_vars, declared_inductive_closed_paramsE.
      eassumption.

    + match goal with h : implb _ (on_free_vars _ (preturn p)) = true |- _ => move: h end.
      destruct isCoFinite => //= hnd.
      apply PCUICOnFreeVarsConv.on_free_vars_nondep_rename => //.
      rewrite (wf_predicate_length_pcontext H1); lia.

    + now rewrite length_map.

    + rewrite /= firstn_map.
      eapply bidirectional_on_free_varsE, (All_firstn (n := ci.(ci_npar))) in X ; tea.
      solve_all.
      now eapply conv_renamePE.
    + by apply rename_wf_branches.
    + eapply Forall2_All2 in H7.
      eapply All2i_All2_mix_left in X9; eauto.
      eapply All2i_All_mix_right in X9 ; eauto.
      eapply All2i_nth_hyp in X9.
      eapply All2i_map_right, (All2i_impl X9) => i cdecl br.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
      move=> [Hnth [ [wfbr [eqbctx [wfbctx [IHbctx [Hbod IHbod]]]]] /andP [on_ctx on_bod] ]].
      rewrite test_context_k_closed_on_free_vars_ctx in on_ctx.
      rewrite -(rename_closed_constructor_body mdecl cdecl f).
      { eapply (declared_constructor_closedE (c:=(ci.(ci_ind),i))); eauto.
        split; eauto. }
      split; auto.
      { simpl. rewrite -rename_cstr_branch_context //.
        1:eapply (declared_inductive_closed_paramsE H).
        rewrite rename_closedn_ctx //.
        eapply closed_cstr_branch_contextE.
        now split.
      }
      cbn -[case_branch_type case_predicate_context].
      rewrite case_branch_type_fst.
      rewrite -rename_case_branch_context_gen //.
      2-3:len.
      1:exact (declared_inductive_closed_paramsE H).
      1:rewrite (wf_branch_length wfbr) //.
      1:rewrite (wf_predicate_length_pars H1).
      1:erewrite declared_minductive_ind_nparsE ; eauto; apply H.
      assert (on_free_vars_ctx P brctxty.1).
      { rewrite case_branch_type_fst.
        eapply (@on_free_vars_case_branch_contextE _ _ _ _ (ci.(ci_ind),i)).
        all: tea.
        split.
        all: eassumption.
      }
      set (brctx' := rename_context f _).
      split.
      1: eapply IHbctx ; eauto.
      rewrite rename_case_branch_typeE //.
      eapply IHbod.
      * rewrite case_branch_type_fst /=.
        relativize #|bcontext br| ; [eapply urenaming_context|] ; tea.
        by rewrite case_branch_context_length.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
        relativize (#|bcontext br|).
        1: erewrite on_ctx_free_vars_concat.
        2: rewrite case_branch_type_length //.
        2: erewrite wf_branch_length ; eauto.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
        eapply on_free_vars_case_branch_typeE.
        all: tea.
        split.
        all: assumption.

  - intros. red. move => P Δ f hf hΓ /= ?.
    rewrite rename_subst0 /= rename_subst_instance map_rev List.length_rev.
    erewrite rename_closedn.
    2: rewrite H0 ; eapply declared_projection_closed_typeE ; tea.
    econstructor ; eauto.
    by rewrite length_map.

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply fix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + apply All_mix with (1 := ht) in X0.
      apply All_map, All_impl with (1 := X0).
      move => d [] /andP [] hT hb p.
      specialize (p _ _ _ hf hΓ).
      eapply lift_sorting_it_impl_gen with p => // IHp.
      eapply IHp ; tea.
    + apply All_mix with (1 := ht) in X2.
      apply All_map, All_impl with (1 := X2).
      move => d [] /andP [] hT hb p.
      rewrite /on_def_body !rename_fix_context !rename_context_length -!(fix_context_length mfix) -!rename_shiftn in hb |- *.
      eapply urenaming_context in hf ; tea.
      eapply on_ctx_free_vars_fix_context in hΓ; tea. rewrite -(fix_context_length mfix) in hΓ.
      specialize (p _ _ _ hf hΓ).
      rewrite <-(shiftnP0 P) in hT. eapply on_free_vars_lift_impl in hT. rewrite Nat.add_0_r in hT.
      apply lift_sorting_f_it_impl with p => //= IHp.
      all: eapply IHp ; tea.
    + match goal with H : wf_fixpoint_red _ _ _ |- _ => destruct H as [isl [hr hm]] end.
      have hop : All (fun d => on_free_vars P (dtype d)) mfix.
      { apply (All_impl ht) => d hd. now move: hd => /andP []. }
      split; [|split].
      * rewrite forallb_map. eapply forallb_impl; [|exact isl].
        intros x _ h. now eapply isLambda_rename.
      * rewrite forallb_map. eapply forallb_impl; [|exact hr].
        intros x _ h. now eapply rename_has_rec_arg.
      * eapply rename_mfix_on_ind_redE; tea.
        exact (rename_check_one_fix f mfix).

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply cofix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + apply All_mix with (1 := ht) in X0.
      apply All_map, All_impl with (1 := X0).
      move => d [] /andP [] hT hb p.
      specialize (p _ _ _ hf hΓ).
      eapply lift_sorting_it_impl_gen with p => // IHp.
      eapply IHp ; tea.
    + apply All_mix with (1 := ht) in X2.
      apply All_map, All_impl with (1 := X2).
      move => d [] /andP [] hT hb p.
      rewrite /on_def_body !rename_fix_context !rename_context_length -!(fix_context_length mfix) -!rename_shiftn in hb |- *.
      eapply urenaming_context in hf ; tea.
      eapply on_ctx_free_vars_fix_context in hΓ; tea. rewrite -(fix_context_length mfix) in hΓ.
      specialize (p _ _ _ hf hΓ).
      rewrite <-(shiftnP0 P) in hT. eapply on_free_vars_lift_impl in hT. rewrite Nat.add_0_r in hT.
      apply lift_sorting_f_it_impl with p => //= IHp.
      all: eapply IHp ; tea.
    + eapply rename_mfix_on_ind_redE; tea; [|exact (rename_check_one_cofix f mfix)].
      apply (All_impl ht) => d hd.
      now move: hd => /andP [].

  - intros. red. intros P Δ f hf ht.
    cbn. rewrite rename_prim_type. econstructor; tea; rewrite ?prim_val_tag_map //.
    destruct X0; cbn in *; constructor; cbn; eauto.
    * eapply hty; tea; solve_all.
    * eapply hdef; tea; solve_all.
    * solve_all.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tSort u)).
    eapply (red_rename_cb _ _ _ _ _ _ _ (wfE_ClosedBodies Σ)) ; tea.
    now eapply infering_on_free_varsE.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tProd na A B)).
    eapply (red_rename_cb _ _ _ _ _ _ _ (wfE_ClosedBodies Σ)) ; tea.
    now eapply infering_on_free_varsE.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tInd ind ui)) -rename_mkApps.
    eapply (red_rename_cb _ _ _ _ _ _ _ (wfE_ClosedBodies Σ)) ; tea.
    now eapply infering_on_free_varsE.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    eapply cumul_renamePE ; tea.
    eapply infering_on_free_varsE.
    4: eassumption.
    all: assumption.

Qed.

End BDRenaming.

Section BDStrengtheningEta.

(** Base [on_free_vars_type] ([BDStrengthening.v:523]). *)
Lemma on_free_vars_typeE `{checker_flags} P Σ (wfΣ : wfE Σ.1) Γ t T :
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Γ |-E t : T ->
  ∑ T', on_free_vars P T' × Σ ;;; Γ |-E t : T'.
Proof.
  intros oΓ ot ty.
  assert (wf_localE Σ Γ) by (eapply typingE_wf_local ; tea).
  apply typing_inferingE in ty as [T' []] ; tea.
  exists T' ; split.
  - edestruct bidirectional_on_free_varsE as (_&_&_&_&?&_).
    all: eauto.
  - by apply infering_typingE.
Qed.

(** Base [typing_renaming_cond_P] ([BDStrengthening.v:1025]). *)
Theorem typing_renaming_cond_PE `{checker_flags} {P f Σ Γ Δ t T} {wfΣ : wfE Σ.1} :
  renamingE P Σ Γ Δ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Γ |-E t : T ->
  ∑ T', [× (on_free_vars P T'), (Σ ;;; Γ |-E t : T'), (JoinE Σ Γ Cumul T' T) &
  (Σ ;;; Δ |-E rename f t : rename f T')].
Proof.
  move => [ur wfΔ] fvΓ fvt tyt.
  move: (tyt) => /typingE_wf_local wfΓ.
  move: (tyt) => /typing_inferingE [T' [inf cum]].
  unshelve epose proof (infering_on_free_varsE _ _ _ _ _ _ _ _ inf); eauto.
  pose proof (inf' := inf). apply infering_typingE in inf; eauto.
  exists T'. split; eauto.
  eapply ws_cumul_pbE_forget; eauto.
  eapply bidirectional_renamingE in inf'; eauto.  eapply infering_typingE; eauto.
Qed.

(** Base [strengthening] ([BDStrengthening.v:1043]). *)
Lemma strengtheningE `{cf: checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Γ' Γ'' t T :
  Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |-E lift #|Γ'| #|Γ''| t : T ->
  ∑ T', [× on_free_vars (strengthenP #|Γ''| #|Γ'| xpredT) T',
        (Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |-E lift #|Γ'| #|Γ''|  t : T') ,
        (JoinE Σ (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'') Cumul T' T) &
        (Σ ;;;  Γ ,,, Γ'' |-E t : unlift #|Γ'| #|Γ''| T')].
Proof.
  intros Hty.
  assert (wf_localE Σ Γ) by
    move: Hty => /typingE_wf_local /All_local_env_app_inv [] /All_local_env_app_inv [] //.

  assert (wfΓ'' : wf_localE Σ (Γ ,,, Γ'')).
  { apply All_local_env_app => //.
    erewrite <- (lift_unlift_context Γ'').
    eapply bidirectional_to_pcuicE ; tea.
    rewrite rename_context_lift_context.
    eapply bidirectional_renamingE ; tea.
    - eapply All_local_app_rel, bidirectional_from_pcuicE => //.
      eapply typeE_Prop_wf.
      apply typingE_wf_local in Hty.
      eassumption.
    - eapply (BDStrengthening.urenaming_strengthen _ _ _ []).
    - apply (BDStrengthening.on_ctx_free_vars_strengthenP _ _ []) => //.
      eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
      by apply wf_local_closed_contextE.
    - rewrite -on_free_vars_ctx_lift_context.
      move: Hty => /typingE_wf_local /(closed_wf_localE wfΣ).
      rewrite closedn_ctx_app => /andP [_] /=.
      rewrite app_context_length Nat.add_comm => hΓ''.
      apply closedn_ctx_lift_inv in hΓ''.
      2: easy.
      eapply (@closedn_ctx_on_free_vars_shift _ _ xpredT) in hΓ''.
      rewrite <- shiftnP_xpredT.
      eassumption.
  }

  eapply typing_renaming_cond_PE in Hty as [T' [? ?]]; eauto.
  exists T'. split; eauto.
  - erewrite <- (BDStrengthening.lift_unlift_term t); eauto.
  - split; eauto. eapply BDStrengthening.urenaming_strengthen.
  - move: wfΓ'' => /wf_local_closed_contextE.
    rewrite on_free_vars_ctx_app => /andP [? ?].
    apply BDStrengthening.on_ctx_free_vars_strengthenP.
    all: eapply on_free_vars_ctx_on_ctx_free_vars_xpredT ; eassumption.
  - rewrite on_free_vars_lift -shiftnP_xpredT.
    move: Hty => /subject_closedE.
    len.
    rewrite -[X in _ + X]Nat.add_comm Nat.add_assoc => Ht.
    eapply closedn_lift_inv in Ht.
    2: lia.
    eapply closedn_on_free_vars.
    eassumption.
Qed.

(** Base [strengthening_type] ([BDStrengthening.v:1098]); the inversion of [T' ≤ tSort s] is T8
    (see the header). *)
Lemma strengthening_typeE `{cf: checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Γ' Γ'' t s :
  Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |-E lift #|Γ'| #|Γ''| t : tSort s ->
  ∑ s', Σ ;;; Γ ,,, Γ'' |-E t : tSort s' × leq_sort Σ s' s.
Proof.
  intros H; pose proof (H' := H); eapply strengtheningE in H. destruct H as [T' [? HT Hcumul HT']].
  pose proof (Hcumul' := Hcumul).
  pose proof (type_closedE HT).
  eapply closedn_on_free_vars in H.
  pose proof (type_closedE HT').
  eapply closedn_on_free_vars in H0.
  pose proof (wf_local_closed_contextE (typingE_wf_local H')).
  eapply into_ws_cumul_pbE in Hcumul; eauto.
  destruct (validityE HT) as (_ & sT & HTs & _).
  destruct (PCUICEtaT8Probe.T8_Sort_r_two (Σ := Σ) subject_reductionE _ Cumul T' s sT wfΣ HTs Hcumul)
    as [s' [Hred Hcumul2]].
  eapply closed_red_red in Hred. pose proof (HT'':=HT'). eapply validityE in HT' as (_ & ? & ? & _).
  exists s'; split; [|exact Hcumul2].
  assert (PCUICReduction.red Σ (Γ,,, Γ'') (unlift #|Γ'| #|Γ''| T') (tSort s')).
  { assert (tSort s' = unlift #|Γ'| #|Γ''| (tSort s')) by reflexivity. rewrite H2; clear H2.
    eapply (red_rename_cb _ _ _ _ _ _ _ (wfE_ClosedBodies Σ)). eapply (BDStrengthening.urenaming_strengthen _ _ _ _); eauto.
    2-3: eauto. eapply typingE_wf_local in HT''.
    eapply wf_local_closed_contextE in HT''. revert HT''.
    rewrite on_free_vars_ctx_app => /andP [? ?].
    apply BDStrengthening.on_ctx_free_vars_strengthenP.
    all: eapply on_free_vars_ctx_on_ctx_free_vars_xpredT; eauto.
  }
  eapply typeE_Cumul; eauto. eapply subject_reductionE; eauto.
  assert (liftSort : unlift #|Γ'| #|Γ''| (tSort s') = tSort s') by reflexivity. rewrite <- liftSort; clear liftSort.
  eapply ws_cumul_pbE_forget_spec, red_ws_cumul_pbE, PCUICConversion.into_closed_red; tea.
  all: first [eapply wf_local_closed_contextE, typingE_wf_local; exact HT''
             | eapply type_is_open_termE; exact HT''].
Qed.

End BDStrengtheningEta.
