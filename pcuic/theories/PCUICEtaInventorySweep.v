(* Distributed under the terms of the MIT license. *)

(** * Inventory sweep: forecast obligations that landed theorems already give

  Each lemma below derives one remaining obligation of rows B1, T1, T2 and of the T8
  assembly (a FORECAST-ONLY class field of [PCUICSREta], [PCUICValidityEta],
  [Bidirectional/BDToPCUICEta], [Bidirectional/BDFromPCUICEta], or a pinned statement of
  [PCUICEtaT8Probe]) from a theorem that is already proved in the tree. The statement of
  each lemma is the obligation's text, verbatim; the [_fit] definition beside it type-checks
  the lemma against the class field itself, so a transcription slip cannot hide.

  Two kinds of entries:
  - DISCHARGED: the lemma has no premise; it proves the field outright.
  - REDUCED: the lemma derives one pinned statement from another one that is still open
    (an argument of the lemma, never an axiom), plus landed theorems. It is no discharge;
    it shows the first statement costs nothing once the second is proved.

  The table with every obligation, the theorem tried and the result is
  [lanes/eta/meta/inventory-sweep.md]. *)

From Stdlib Require Import ssreflect ssrbool Lia.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICUnivSubst PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICEquality PCUICContextSubst PCUICArities PCUICWellScopedCumulativity
     PCUICSubstitution PCUICClosedConv PCUICCases PCUICInductives PCUICInductiveInversion
     PCUICSigmaCalculus PCUICCasesContexts PCUICValidity PCUICUnivSubstitutionConv PCUICClosed
     PCUICContexts PCUICSpine
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaNotions PCUICClosedBodies
     PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICEtaC1aR PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5A2
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaCtx
     PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind.
From MetaRocq.PCUIC.Typing Require PCUICContextConversionTypEta PCUICUnivSubstitutionTypEta
     PCUICWeakeningTypEta PCUICWeakeningEnvTypEta PCUICInstTypEta PCUICRenameTypEta.
From MetaRocq.PCUIC Require Import PCUICInstDef PCUICInstConv PCUICInstDefEta PCUICTypingEtaInd
     PCUICInversionEta.
From MetaRocq.PCUIC Require PCUICClosedTypEta BDToPCUICEta BDFromPCUICEta PCUICEtaT8Probe PCUICEtaT8BackSim.
From MetaRocq.PCUIC Require Import PCUICValidityEta PCUICSREta.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

Set Default Goal Selector "!".

(** ** Copy 18: [isType_is_open_termE] (DISCHARGED)

  Field [PCUICSREta.SRForecastCopy18.isType_is_open_termE] (PCUICSREta.v:466). Landed:
  [Typing/PCUICClosedTypEta.isType_is_open_termE] (PCUICClosedTypEta.v:623), the same
  proposition with [Γ T] implicit and [wfE Σ.1] (which is [wfE Σ] after the coercion). *)
Lemma isType_is_open_termE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall (Γ : context) (T : term),
  isTypeE Σ Γ T ->
  is_open_term Γ T.
Proof.
  intros cf Σ wfΣ Γ T h. exact (@PCUICClosedTypEta.isType_is_open_termE cf Σ wfΣ Γ T h).
Qed.

Definition isType_is_open_termE_fit (F : PCUICSREta.SRForecastCopy18) :=
  (@isType_is_open_termE_landed
     : ltac:(let t := type of (@PCUICSREta.isType_is_open_termE F) in exact t)).

(** ** Copy 15 ([SRForecastCopy15], PCUICSREta.v:205-317)

  Each lemma is the base proof ([PCUICSpine.v]) with the base lemmas it calls replaced by their
  landed E twins, or a landed lemma read at the field's instance. *)

(** [ctx_inst_instE] (PCUICSREta.v:214), base [ctx_inst_inst] (PCUICSpine.v:208). Landed:
    [typing_subst_instance''E] (Typing/PCUICUnivSubstitutionTypEta.v:873); [wf_global_extE] is
    [wf_ext_wkE] by definition (:318). DISCHARGED. *)
Lemma ctx_inst_instE_landed :
  forall {cf : checker_flags} (Σ : global_env_ext) (ext : universes_decl) (u : Instance.t)
    (Γ : context) (i : list term) (Δ : context),
  PCUICUnivSubstitutionTypEta.wf_global_extE Σ.1 ext ->
  ctx_instE (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_instE Σ Γ@[u] (map (subst_instance u) i) Δ@[u].
Proof.
  intros cf Σ ext u Γ i Δ wfext ctxi cu.
  induction ctxi; simpl; constructor; auto.
  - destruct Σ as [Σ univs].
    eapply (PCUICUnivSubstitutionTypEta.typing_subst_instance''E Σ); eauto.
  - rewrite (subst_telescope_subst_instance u [i]). apply IHctxi.
  - rewrite (subst_telescope_subst_instance u [b]). apply IHctxi.
Qed.

Definition ctx_inst_instE_fit (F : SRForecastCopy15) :=
  (@ctx_inst_instE_landed : ltac:(let t := type of (@ctx_inst_instE F) in exact t)).

(** [ctx_inst_open_termsE] (PCUICSREta.v:221). Landed: [ctx_inst_closedE]
    (Typing/PCUICClosedTypEta.v:529), the same fact with [closedn #|Γ|] for [is_open_term Γ]
    ([is_open_term_closedE], :444). DISCHARGED. *)
Lemma ctx_inst_open_termsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall (Γ : context) (args : list term) (Δ : context),
  ctx_instE Σ Γ args Δ ->
  All (fun t : term => is_open_term Γ t) args.
Proof.
  intros cf Σ wfΣ Γ args Δ ci.
  eapply All_impl; [exact (PCUICClosedTypEta.ctx_inst_closedE Σ Γ args Δ wfΣ ci)|].
  intros t ht. now rewrite -(PCUICClosedTypEta.is_open_term_closedE Γ t).
Qed.

Definition ctx_inst_open_termsE_fit (F : SRForecastCopy15) :=
  (@ctx_inst_open_termsE_landed : ltac:(let t := type of (@ctx_inst_open_termsE F) in exact t)).

(** [spine_subst_inj_substE] (PCUICSREta.v:261). Landed: base [context_subst_fun]
    (PCUICContextSubst.v:166) on the [context_subst] field of [spine_substE], which is base's
    [context_subst] itself. DISCHARGED. *)
Lemma spine_subst_inj_substE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {inst s s' : list term} {Δ : context},
  spine_substE Σ Γ inst s Δ ->
  spine_substE Σ Γ inst s' Δ ->
  s = s'.
Proof.
  intros cf Σ Γ inst s s' Δ sp sp'.
  exact (context_subst_fun (inst_ctx_substE sp) (inst_ctx_substE sp')).
Qed.

Definition spine_subst_inj_substE_fit (F : SRForecastCopy15) :=
  (@spine_subst_inj_substE_landed : ltac:(let t := type of (@spine_subst_inj_substE F) in exact t)).

(** [subslet_skipnE] (PCUICSREta.v:266), base [subslet_skipn] (PCUICSpine.v:134). No landed
    theorem needed: base's proof reads only the three constructors and [skipn] rewrites, so it
    is the proof here, over the constructors of [subsletE]. DISCHARGED (from the definition). *)
Lemma subslet_skipnE_landed :
  forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (s : list term) (Δ : context) (n : nat),
  subsletE Σ Γ s Δ ->
  subsletE Σ Γ (skipn n s) (skipn n Δ).
Proof.
  intros cf Σ Γ s Δ n.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    + rewrite !skipn_nil. constructor.
    + rewrite !skipn_S. auto.
    + rewrite !skipn_S. auto.
Qed.

Definition subslet_skipnE_fit (F : SRForecastCopy15) :=
  (@subslet_skipnE_landed : ltac:(let t := type of (@subslet_skipnE F) in exact t)).

(** [wf_local_alphaE] (PCUICSREta.v:286), base [wf_local_alpha] (PCUICSpine.v:83). Landed:
    [context_conversionE] (Typing/PCUICContextConversionTypEta.v:368) and
    [eq_context_upto_names_conv_contextE] (PCUICWsCumulEtaCtx.v:203), the twins of the two
    lemmas base calls. DISCHARGED. *)
Lemma wf_local_alphaE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    (Γ Γ' : list context_decl),
  eq_context_upto_names Γ Γ' ->
  wf_localE Σ Γ ->
  wf_localE Σ Γ'.
Proof.
  intros cf Σ wfΣ Γ Γ' h.
  induction h; intros hw; depelim hw; try constructor; auto.
  all: depelim r; constructor; subst; auto.
  all: rewrite -e.
  all: eapply lift_typing_impl; tea; intros t' T Hty.
  all: eapply PCUICContextConversionTypEta.context_conversionE; eauto.
  all: now apply eq_context_upto_names_conv_contextE.
Qed.

Definition wf_local_alphaE_fit (F : SRForecastCopy15) :=
  (@wf_local_alphaE_landed : ltac:(let t := type of (@wf_local_alphaE F) in exact t)).

(** [ws_cumul_ctx_pb_eq_leE] (PCUICSREta.v:292). Landed: [conv_cumul_contextE]
    (PCUICWsCumulEtaCtx.v:167), no premise at all. DISCHARGED. *)
Lemma ws_cumul_ctx_pb_eq_leE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {pb : conv_pb} {Γ Δ : context},
  ws_cumul_ctx_pbE Conv Σ Γ Δ ->
  ws_cumul_ctx_pbE pb Σ Γ Δ.
Proof.
  intros cf Σ pb Γ Δ h. destruct pb; [exact h|exact (conv_cumul_contextE h)].
Qed.

Definition ws_cumul_ctx_pb_eq_leE_fit (F : SRForecastCopy15) :=
  (@ws_cumul_ctx_pb_eq_leE_landed : ltac:(let t := type of (@ws_cumul_ctx_pb_eq_leE F) in exact t)).

(** [ws_cumul_ctx_pb_rel_transE] (PCUICSREta.v:303), base [ws_cumul_ctx_pb_rel_trans]
    (PCUICSpine.v:3052). Landed: [ws_cumul_ctx_pbE_rel_app] (PCUICWsCumulEtaCtx.v:588) and the
    [Transitive] instance [ws_cumul_ctx_pbE_trans] (:355, under [ClosedBodies], which [wfE]
    gives). DISCHARGED. *)
Lemma ws_cumul_ctx_pb_rel_transE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {pb : conv_pb} {Γ Δ Δ' Δ'' : list context_decl},
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ' Δ'' ->
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ''.
Proof.
  intros cf Σ wfΣ pb Γ Δ Δ' Δ'' h h'.
  have cb : ClosedBodies Σ := PCUICClosedTypEta.wfE_ClosedBodies Σ (wfΣ := wfΣ).
  apply (snd ws_cumul_ctx_pbE_rel_app).
  etransitivity; [exact (fst ws_cumul_ctx_pbE_rel_app h)|exact (fst ws_cumul_ctx_pbE_rel_app h')].
Qed.

Definition ws_cumul_ctx_pb_rel_transE_fit (F : SRForecastCopy15) :=
  (@ws_cumul_ctx_pb_rel_transE_landed
     : ltac:(let t := type of (@ws_cumul_ctx_pb_rel_transE F) in exact t)).

(** ** Copies 10, 12, 14 ([SRForecastCopy10/12/14], PCUICSREta.v:112-196; [ValForecastCopy14],
    PCUICValidityEta.v:211-219) *)

(** [subslet_ass_tipE] (PCUICSREta.v:114), base [subslet_ass_tip] (PCUICSubstitution.v:66):
    the constructors of the landed [subsletE] (PCUICValidityEta.v:112). DISCHARGED (from the
    definition). *)
Lemma subslet_ass_tipE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ na t T},
  Σ ;;; Γ |-E t : T ->
  subsletE Σ Γ [t] [vass na T].
Proof. intros cf Σ Γ na t T ht. constructor; [constructor|]. now rewrite subst_empty. Qed.

Definition subslet_ass_tipE_fit (F : SRForecastCopy10) :=
  (@subslet_ass_tipE_landed : ltac:(let t := type of (@subslet_ass_tipE F) in exact t)).

(** [subslet_defE] (PCUICSREta.v:119): the constructor [cons_let_defE]. DISCHARGED (from the
    definition). *)
Lemma subslet_defE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ Δ s na t T t'},
  subsletE Σ Γ s Δ ->
  Σ ;;; Γ |-E subst0 s t : subst0 s T ->
  t' = subst0 s t ->
  subsletE Σ Γ (t' :: s) (Δ ,, vdef na t T).
Proof. intros cf Σ Γ Δ s na t T t' hs ht ->. now constructor. Qed.

Definition subslet_defE_fit (F : SRForecastCopy10) :=
  (@subslet_defE_landed : ltac:(let t := type of (@subslet_defE F) in exact t)).

(** [subslet_lengthE] (PCUICSREta.v:126): induction on [subsletE]. DISCHARGED (from the
    definition). *)
Lemma subslet_lengthE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ s Δ},
  subsletE Σ Γ s Δ -> #|s| = #|Δ|.
Proof. intros cf Σ Γ s Δ h. induction h; cbn; lia. Qed.

Definition subslet_lengthE_fit (F : SRForecastCopy10) :=
  (@subslet_lengthE_landed : ltac:(let t := type of (@subslet_lengthE F) in exact t)).

(** [subslet_untyped_subsletE] (PCUICSREta.v:130), base [subslet_untyped_subslet]
    (PCUICSubstitution.v:829): the constructors of the landed base [untyped_subslet]
    (PCUICSubstitution.v:820). DISCHARGED (from the definitions). *)
Lemma subslet_untyped_subsletE_landed :
  forall {cf : checker_flags} (Σ : global_env_ext) Γ s Γ',
  subsletE Σ Γ s Γ' -> untyped_subslet Γ s Γ'.
Proof. intros cf Σ Γ s Γ' h. induction h; constructor; auto. Qed.

Definition subslet_untyped_subsletE_fit (F : SRForecastCopy10) :=
  (@subslet_untyped_subsletE_landed
     : ltac:(let t := type of (@subslet_untyped_subsletE F) in exact t)).

(** [wf_arities_contextE] (PCUICSREta.v:145), base [wf_arities_context] / [wf_arities_context']
    (PCUICSubstitution.v:554-582). Landed: [on_declared_minductiveE]
    (Typing/PCUICWeakeningEnvTypEta.v:452) and [weaken_ctxE] (Typing/PCUICWeakeningTypEta.v:133).
    DISCHARGED. *)
Lemma wf_arities_contextE_landed :
  forall {cf : checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mind mdecl},
  declared_minductive Σ mind mdecl ->
  wf_localE (Σ, ind_universes mdecl) (arities_context mdecl.(ind_bodies)).
Proof.
  intros cf Σ wfΣ mind mdecl Hdecl.
  pose proof (onInductives (PCUICWeakeningEnvTypEta.on_declared_minductiveE wfΣ Hdecl)) as Ha.
  unfold arities_context. revert Ha.
  induction (ind_bodies mdecl) using rev_ind; [constructor|].
  intros Ha.
  rewrite rev_map_app.
  simpl. apply Alli_app in Ha as [Hl Hx].
  inv Hx. clear X0.
  apply onArity in X as (_ & s & Hs & _ & Her).
  specialize (IHl Hl).
  econstructor; eauto.
  fold (arities_context l) in *.
  cbn in Her.
  repeat (eexists; cbn; tea).
  now eapply PCUICWeakeningTypEta.weaken_ctxE in Hs.
Qed.

Definition wf_arities_contextE_fit (F : SRForecastCopy10) :=
  (@wf_arities_contextE_landed : ltac:(let t := type of (@wf_arities_contextE F) in exact t)).

(** [sorts_local_ctx_wf_localE] (PCUICSREta.v:156). Landed, MORE GENERAL:
    [sorts_local_ctx_All_local_env] (Conversion/PCUICClosedConv.v:26), stated for any typing
    relation [P]; here [P := typingE]. DISCHARGED. *)
Lemma sorts_local_ctx_wf_localE_landed :
  forall {cf : checker_flags} (Σ : global_env_ext) Γ Δ s,
  wf_localE Σ Γ ->
  sorts_local_ctx (lift_typing typingE) Σ Γ Δ s ->
  wf_localE Σ (Γ ,,, Δ).
Proof.
  intros cf Σ Γ Δ s wfΓ h. exact (sorts_local_ctx_All_local_env (@typingE cf) Σ Γ Δ s wfΓ h).
Qed.

Definition sorts_local_ctx_wf_localE_fit (F : SRForecastCopy12) :=
  (@sorts_local_ctx_wf_localE_landed
     : ltac:(let t := type of (@sorts_local_ctx_wf_localE F) in exact t)).

(** [subslet_liftE] (PCUICSREta.v:162), base [subslet_lift] (PCUICContexts.v:591). Landed:
    [weakeningE] (Typing/PCUICWeakeningTypEta.v:85) and [subslet_lengthE_landed] above.
    DISCHARGED. *)
Lemma subslet_liftE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ Δ : context) s Δ',
  wf_localE Σ (Γ ,,, Δ) ->
  subsletE Σ Γ s Δ' ->
  subsletE Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  intros cf Σ wfΣ Γ Δ s Δ' wfl.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  - rewrite -(subslet_lengthE_landed X).
    rewrite -distr_lift_subst. apply PCUICWeakeningTypEta.weakeningE; eauto.
  - rewrite -(subslet_lengthE_landed X).
    rewrite distr_lift_subst. constructor; auto.
    rewrite - !distr_lift_subst. apply PCUICWeakeningTypEta.weakeningE; eauto.
Qed.

Definition subslet_liftE_fit (F : SRForecastCopy12) :=
  (@subslet_liftE_landed : ltac:(let t := type of (@subslet_liftE F) in exact t)).

(** [on_minductive_wf_paramsE] (PCUICSREta.v:185), base [on_minductive_wf_params]
    (PCUICArities.v:633). Landed: [on_declared_minductiveE] (Typing/PCUICWeakeningEnvTypEta.v:452)
    and [wf_local_instantiateE] (Typing/PCUICUnivSubstitutionTypEta.v:926). DISCHARGED. *)
Lemma on_minductive_wf_paramsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind mdecl} {u},
  declared_minductive Σ.1 ind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ (subst_instance u (ind_params mdecl)).
Proof.
  intros cf Σ wfΣ ind mdecl u H cu.
  unshelve epose proof (declared_minductive_to_gen H); eauto with pcuic.
  eapply (PCUICUnivSubstitutionTypEta.wf_local_instantiateE (decl := InductiveDecl mdecl)); eauto.
  eapply (PCUICWeakeningEnvTypEta.on_declared_minductiveE wfΣ) in H.
  now apply onParams in H.
Qed.

Definition on_minductive_wf_paramsE_fit (F : SRForecastCopy14) :=
  (@on_minductive_wf_paramsE_landed
     : ltac:(let t := type of (@on_minductive_wf_paramsE F) in exact t)).

(** [ws_cumul_ctx_pb_appE] (PCUICSREta.v:191), base [ws_cumul_ctx_pb_app] (PCUICArities.v:126).
    Landed: [All2_fold_app], [All2_fold_app_inv] (generic) and [ws_cumul_ctx_pbE_closed_left]
    (PCUICWsCumulEtaCtx.v:120, no premise). DISCHARGED. *)
Lemma ws_cumul_ctx_pb_appE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {le Γ Γ' Δ Δ'},
  #|Δ| = #|Δ'| ->
  ws_cumul_ctx_pbE le Σ (Γ ,,, Δ) (Γ' ,,, Δ') <~>
  ws_cumul_ctx_pbE le Σ Γ Γ' × ws_cumul_ctx_pbE_rel le Σ Γ Δ Δ'.
Proof.
  intros cf Σ wfΣ le Γ Γ' Δ Δ' hlen; split.
  - move/All2_fold_app_inv. move/(_ hlen) => [] onΓ onΔ.
    split; [exact onΓ|]. split; [exact (ws_cumul_ctx_pbE_closed_left onΓ)|exact onΔ].
  - move=> [] onΓ [_ onΔ]. apply All2_fold_app; [exact onΓ|exact onΔ].
Qed.

Definition ws_cumul_ctx_pb_appE_fit (F : SRForecastCopy14) :=
  (@ws_cumul_ctx_pb_appE_landed : ltac:(let t := type of (@ws_cumul_ctx_pb_appE F) in exact t)).

(** [subslet_indsE] (PCUICValidityEta.v:213), base [subslet_inds] (PCUICArities.v:527). Landed:
    [on_declared_minductiveE], the constructor [typeE_Ind], [type_closedE]
    (Typing/PCUICClosedTypEta.v:417). DISCHARGED. *)
Lemma subslet_indsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind u mdecl idecl},
  declared_inductive Σ.1 ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subsletE Σ [] (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u (arities_context (ind_bodies mdecl))).
Proof.
  intros cf Σ wfΣ ind u mdecl idecl isdecl univs.
  unfold inds.
  pose proof (proj1 isdecl) as declm.
  apply (PCUICWeakeningEnvTypEta.on_declared_minductiveE wfΣ) in declm as [oind oc].
  clear oc.
  assert (Alli (fun i x =>
    Σ ;;; [] |-E tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u
      : subst_instance u (ind_type x)) 0 (ind_bodies mdecl)) as X.
  { apply forall_nth_error_Alli. intros i x hnth.
    eapply typeE_Ind; [constructor| |exact univs].
    split; [exact (proj1 isdecl)|exact hnth]. }
  clear oind.
  revert X. clear onNpars.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4 5.
  induction l using rev_ind; simpl; first constructor.
  rewrite /subst_instance /= /map_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=.
  rewrite {1}/map_decl /= length_app /= Nat.add_1_r.
  constructor.
  - rewrite -rev_map_spec. apply IHl; try lia.
    eapply Alli_app in X; intuition auto.
  - eapply Alli_app in X as [oind Hx].
    depelim Hx. clear Hx.
    rewrite Nat.add_0_r in t.
    rewrite subst_closedn; auto.
    now eapply PCUICClosedTypEta.type_closedE in t.
Qed.

Definition subslet_indsE_fit (F : ValForecastCopy14) :=
  (@subslet_indsE_landed : ltac:(let t := type of (@subslet_indsE F) in exact t)).

(** ** Copy 10: the substitution lemmas, from the landed instantiation lemma

  [ValForecastCopy10] (PCUICValidityEta.v:187-205: [isType_substitutionE], [substitutionE],
  [substitution0E]) and [SRForecastCopy10]'s [substitution_letE], [substitution_wf_localE]
  (PCUICSREta.v:134-143). Landed, MORE GENERAL: [type_instE] / [typing_instE]
  (Typing/PCUICInstTypEta.v:377, :649), typing preservation under ANY well-typed
  substitution [σ]; a substitution [s] for [Γ'] is the instance [σ := ⇑^#|Δ| (s ⋅n ids)].
  Base proves the substitution lemmas exactly so ([PCUICSubstitution.v:1665-1887]); the glue,
  [subslet_nth_errorE], [usubst_well_substE] and [subslet_well_substE], is base's proof with
  the landed E lemmas ([shift_typingE], [meta_convE], [subslet_usubst] on the untyped
  substitution). DISCHARGED, all five. *)

Section SubstitutionFromInst.
  Local Open Scope sigma_scope.

  (** Base [subslet_nth_error] (PCUICSubstitution.v:84). *)
  Lemma subslet_nth_errorE {cf : checker_flags} {Σ Γ s Δ decl n} :
    subsletE Σ Γ s Δ ->
    nth_error Δ n = Some decl ->
    ∑ t, nth_error s n = Some t ×
    let ty := subst0 (skipn (S n) s) (decl_type decl) in
    Σ ;;; Γ |-E t : ty ×
    match decl_body decl return Type with
    | Some t' =>
      let b := subst0 (skipn (S n) s) t' in
      (t = b)
    | None => unit
    end.
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists t; split; auto.
      simpl. split; auto.
    - intros. destruct decl as [na' [b|] ty]; cbn in *.
      + specialize (IHX _ H) as [t' [hnth [hty heq]]]. exists t'; intuition auto.
      + now apply IHX.
    - intros [= <-]. eexists; split; eauto.
      simpl. split; auto.
    - apply IHX.
  Qed.

  (** Base [usubst_well_subst] (PCUICSubstitution.v:1665). *)
  Lemma usubst_well_substE {cf : checker_flags} {Σ : global_env_ext} {Γ σ Δ} :
    usubst Γ σ Δ ->
    (forall x decl, nth_error Γ x = Some decl ->
      Σ ;;; Δ |-E σ x : (decl.(decl_type)).[↑^(S x) ∘s σ]) ->
    well_substE Σ Γ σ Δ.
  Proof.
    intros us hty. split; eauto.
    intros x decl hnth. specialize (hty x decl hnth). now sigma.
  Qed.

  (** Base [subslet_well_subst] (PCUICSubstitution.v:1675). *)
  Lemma subslet_well_substE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ} :
    subsletE Σ Γ s Γ' ->
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ->
    well_substE Σ (Γ ,,, Γ' ,,, Δ) (⇑^#|Δ| (s ⋅n ids)) (Γ ,,, subst_context s 0 Δ).
  Proof.
    intros hs hsΔ.
    apply usubst_well_substE.
    - apply (subslet_usubst (subslet_untyped_subsletE_landed _ _ _ _ hs)).
    - intros x decl.
      case: nth_error_app_context => //.
      { intros d hnth hn [= ->].
        rewrite {1}Upn_eq subst_consn_lt; len => //. rewrite /subst_fn.
        rewrite idsn_lt //.
        eapply PCUICRenameTypEta.meta_convE.
        - econstructor; auto.
          rewrite nth_error_app_lt; len => //.
          now rewrite nth_error_subst_context hnth.
        - rewrite /subst_decl. simpl.
          sigma. rewrite -shiftk_shift -subst_compose_assoc -shiftk_shift.
          rewrite subst_shift_comm.
          rewrite -subst_fn_subst_consn. lia_f_equal. }
      { intros n hnth; len; intros hd [= ->].
        pose proof (subslet_lengthE_landed hs).
        move: hnth; case: nth_error_app_context => //.
        * intros n hnth hx [= ->].
          rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
          rewrite subst_consn_compose.
          rewrite subst_consn_lt; len; try lia.
          unfold subst_fn. rewrite nth_error_map.
          destruct (subslet_nth_errorE hs hnth) as [t [hnths [hty hb]]].
          rewrite hnths /=. sigma in hty.
          eapply PCUICRenameTypEta.meta_convE in hty.
          2:now rewrite skipn_subst ?Upn_0; try lia.
          eapply (PCUICWeakeningTypEta.shift_typingE (Δ := subst_context s 0 Δ)) in hty.
          2:tas.
          2:now len.
          rewrite inst_assoc in hty.
          rewrite Upn_eq.
          eapply PCUICRenameTypEta.meta_convE; eauto.
          eapply inst_ext.
          rewrite (shift_subst_consn_ge (S x)); len; try lia.
          rewrite subst_compose_assoc.
          now replace (S x - #|Δ|) with (S (x - #|Δ|)) by lia.
        * intros n hnth hn [= ->].
          eapply PCUICRenameTypEta.meta_conv_allE.
          2:reflexivity.
          2:{ rewrite Upn_subst_consn_ge; try lia. rewrite compose_ids_l.
              instantiate (1 := tRel (x - #|s|)).
              rewrite /shiftk. lia_f_equal. }
          2:{ econstructor; eauto. }
          eapply PCUICRenameTypEta.meta_convE.
          { econstructor; tas.
            rewrite nth_error_app_context_ge; len; try lia.
            rewrite H. erewrite <- hnth. lia_f_equal. }
          rewrite lift0_inst.
          rewrite Upn_eq.
          rewrite shift_subst_consn_ge; len; try lia.
          rewrite subst_consn_compose shift_subst_consn_ge; len; try lia.
          rewrite H. rewrite shiftk_compose. lia_f_equal.
      }
  Qed.

  (** [substitution_wf_localE] (PCUICSREta.v:139), base [substitution_wf_local] /
      [All_local_env_inst] (PCUICSubstitution.v:1738, :1856): the context half of [type_instE],
      read off a typing in the context ([tSort sProp]), then [wf_local_app_instE]
      (Typing/PCUICInstTypEta.v:312). *)
  Lemma substitution_wf_localE_landed :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ},
    subsletE Σ Γ s Γ' ->
    wf_localE Σ (Γ ,,, Γ' ,,, Δ) ->
    wf_localE Σ (Γ ,,, subst_context s 0 Δ).
  Proof.
    intros cf Σ wfΣ Γ Γ' s Δ sub wf.
    pose proof (typeE_Sort _ _ sProp wf) as ty. forward ty; [now simpl|].
    destruct (PCUICInstTypEta.type_instE Σ wfΣ _ _ _ ty) as [_ [HΓ _]].
    have HΓ0 : wf_localE Σ Γ.
    { apply All_local_env_app_inv in wf as [wf _]. now apply All_local_env_app_inv in wf as [wf _]. }
    rewrite subst_context_inst_context.
    eapply (PCUICInstTypEta.wf_local_app_instE _ (Γ ,,, Γ')); eauto.
    - now eapply All_local_env_app_inv in HΓ as [].
    - eapply (subslet_well_substE (Δ := [])) in sub;
        rewrite ?subst_context_nil in sub |- *.
      + apply sub.
      + exact HΓ0.
  Qed.

  Definition substitution_wf_localE_fit (F : SRForecastCopy10) :=
    (@substitution_wf_localE_landed
       : ltac:(let t := type of (@substitution_wf_localE F) in exact t)).

  (** [substitutionE] (PCUICValidityEta.v:195), base [substitution] (PCUICSubstitution.v:1795). *)
  Lemma substitutionE_landed :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ t T},
    subsletE Σ Γ s Γ' ->
    Σ ;;; Γ ,,, Γ' ,,, Δ |-E t : T ->
    Σ ;;; Γ ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T.
  Proof.
    intros cf Σ wfΣ Γ Γ' s Δ t T hs ht.
    have wfs := substitution_wf_localE_landed (wfΣ := wfΣ) hs (typingE_wf_local ht).
    rewrite !subst_inst.
    eapply (@PCUICInstTypEta.typing_instE cf Σ _ _ _ _ _ wfΣ); [exact wfs| |exact ht].
    now eapply (subslet_well_substE (wfΣ := wfΣ)).
  Qed.

  Definition substitutionE_fit (F : ValForecastCopy10) :=
    (@substitutionE_landed : ltac:(let t := type of (@substitutionE F) in exact t)).

  (** [isType_substitutionE] (PCUICValidityEta.v:189), base [isType_substitution]
      (PCUICSubstitution.v:1824). *)
  Lemma isType_substitutionE_landed :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ T},
    subsletE Σ Γ s Γ' ->
    isTypeE Σ (Γ ,,, Γ' ,,, Δ) T ->
    isTypeE Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T).
  Proof.
    intros cf Σ wfΣ Γ Γ' s Δ T hs HT.
    apply lift_typing_f_impl with (1 := HT) => // ?? Ht.
    eapply substitutionE_landed in Ht; tea.
  Qed.

  Definition isType_substitutionE_fit (F : ValForecastCopy10) :=
    (@isType_substitutionE_landed : ltac:(let t := type of (@isType_substitutionE F) in exact t)).

  (** [substitution0E] (PCUICValidityEta.v:201), base [substitution0] (PCUICSubstitution.v:1865). *)
  Lemma substitution0E_landed :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ n u U t T},
    Σ ;;; Γ ,, vass n U |-E t : T -> Σ ;;; Γ |-E u : U ->
    Σ ;;; Γ |-E t {0 := u} : T {0 := u}.
  Proof.
    intros cf Σ wfΣ Γ n u U t T Ht Hu.
    eapply (substitutionE_landed (Γ' := [vass n U]) (Δ := [])); tea.
    now eapply subslet_ass_tipE_landed.
  Qed.

  Definition substitution0E_fit (F : ValForecastCopy10) :=
    (@substitution0E_landed : ltac:(let t := type of (@substitution0E F) in exact t)).

  (** [substitution_letE] (PCUICSREta.v:134), base [substitution_let] (PCUICSubstitution.v:1876). *)
  Lemma substitution_letE_landed :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ n u U t T},
    Σ ;;; Γ ,, vdef n u U |-E t : T ->
    Σ ;;; Γ |-E t {0 := u} : T {0 := u}.
  Proof.
    intros cf Σ wfΣ Γ n u U t T Ht.
    assert ((wf_localE Σ Γ) * (Σ ;;; Γ |-E u : U)%type) as [wfΓ tyu].
    { apply typingE_wf_local in Ht.
      depelim Ht; split; tas. now destruct l as (? & _). }
    eapply (substitutionE_landed (Γ' := [vdef n u U]) (Δ := [])); tea.
    eapply subslet_defE_landed; [constructor| |]; now rewrite !subst_empty.
  Qed.

  Definition substitution_letE_fit (F : SRForecastCopy10) :=
    (@substitution_letE_landed : ltac:(let t := type of (@substitution_letE F) in exact t)).

End SubstitutionFromInst.

(** ** Copy 12: [wf_local_smash_endE] and [typing_expand_letsE] (PCUICSREta.v:168, :173)

  Base [PCUICContexts.v:340-377, 636-694]; the only typed steps are [substitution],
  [weakening_typing] and [subslet_lift], all discharged or landed above
  ([substitutionE_landed], [weakening_typingE] (Typing/PCUICWeakeningTypEta.v:73),
  [subslet_liftE_landed]). DISCHARGED, both. *)

Lemma wf_local_rel_smash_context_genE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ Δ Δ'} :
  wf_localE Σ (Δ' ,,, Γ) ->
  wf_local_relE Σ (Δ' ,,, Γ) Δ ->
  wf_local_relE Σ Δ' (smash_context Δ Γ).
Proof.
  induction Γ in Δ |- *; simpl; auto.
  intros wfΓ wfΔ. depelim wfΓ; simpl.
  - apply IHΓ; auto. eapply All_local_env_app; auto.
    + constructor; auto.
    + eapply All_local_env_impl; eauto. simpl; intros.
      now rewrite app_context_assoc.
  - apply IHΓ; auto.
    apply All_local_env_fold, All_local_env_impl with (1 := wfΔ).
    intros Γ' j X.
    apply lift_typing_f_impl with (1 := X) => // ?? HT.
    rewrite Nat.add_0_r.
    eapply (substitutionE_landed (wfΣ := wfΣ) (Γ' := [vdef na b t]) (s := [b])) in HT; eauto.
    rewrite -{1}(subst_empty 0 b).
    repeat constructor.
    rewrite !subst_empty.
    now eapply unlift_TermTyp.
Qed.

Lemma wf_local_smash_endE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ,
  wf_localE Σ (Γ ,,, Δ) -> wf_localE Σ (Γ ,,, smash_context [] Δ).
Proof.
  intros cf Σ wfΣ Γ Δ wf.
  apply All_local_env_app.
  - now apply All_local_env_app_inv in wf.
  - eapply (wf_local_rel_smash_context_genE (wfΣ := wfΣ)); [exact wf|constructor].
Qed.

Definition wf_local_smash_endE_fit (F : SRForecastCopy12) :=
  (@wf_local_smash_endE_landed : ltac:(let t := type of (@wf_local_smash_endE F) in exact t)).

(** Base [subslet_extended_subst] (PCUICContexts.v:636). *)
Lemma subslet_extended_substE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ :
  wf_localE Σ (Γ ,,, Δ) ->
  subsletE Σ (Γ ,,, smash_context [] Δ)
    (extended_subst Δ 0)
    (lift_context (context_assumptions Δ) 0 Δ).
Proof.
  move=> wfΔ.
  eapply All_local_env_app_inv in wfΔ as [wfΓ wfΔ].
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; try constructor.
  - depelim wfΔ. repeat red in l, l0.
    specialize (IHΔ wfΔ).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    len.
    constructor => //.
    apply unlift_TermTyp in l.
    eapply (PCUICWeakeningTypEta.weakening_typingE (wfΣ := wfΣ) (Γ'' := smash_context [] Δ)) in l.
    + len in l. simpl in l. simpl.
      eapply (substitutionE_landed (wfΣ := wfΣ) (Δ := [])) in l; tea.
    + eapply (wf_local_smash_endE_landed (wfΣ := wfΣ)). now eapply All_local_env_app.
  - rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    depelim wfΔ.
    specialize (IHΔ wfΔ).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    assert (wf_localE Σ (Γ ,,, smash_context [] Δ)).
    { eapply (wf_local_smash_endE_landed (wfΣ := wfΣ)). now eapply All_local_env_app. }
    assert (wf_localE Σ (Γ ,,, smash_context [] Δ ,, mkdecl na None
        (subst0 (extended_subst Δ 0) (lift (context_assumptions Δ) #|Δ| decl_type)))).
    { simpl. constructor; tas.
      eapply lift_typing_f_impl with (f := fun t => _ (_ t)) (1 := l) => // ?? Hs.
      eapply (PCUICWeakeningTypEta.weakening_typingE (wfΣ := wfΣ) (Γ'' := smash_context [] Δ)) in Hs; tas.
      len in Hs.
      now eapply (substitutionE_landed (wfΣ := wfΣ) (Δ := [])) in Hs. }
    constructor.
    + rewrite (lift_extended_subst _ 1).
      rewrite -(PCUICWeakeningConv.lift_context_lift_context 1 _).
      eapply (subslet_liftE_landed (wfΣ := wfΣ) _ [_]); eauto.
    + eapply PCUICRenameTypEta.meta_convE.
      * econstructor; tas. reflexivity.
      * simpl. rewrite (lift_extended_subst _ 1).
        rewrite distr_lift_subst. f_equal. len.
        now rewrite simpl_lift; try lia.
Qed.

Lemma typing_expand_letsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ t T,
  Σ ;;; Γ ,,, Δ |-E t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T.
Proof.
  intros cf Σ wfΣ Γ Δ t T Ht.
  rewrite /expand_lets /expand_lets_k.
  pose proof (typingE_wf_local Ht) as wfΓΔ.
  eapply (PCUICWeakeningTypEta.weakening_typingE (wfΣ := wfΣ) (Γ'' := smash_context [] Δ)) in Ht.
  - len in Ht. simpl in Ht. simpl.
    eapply (substitutionE_landed (wfΣ := wfΣ) (Δ := [])) in Ht; tea.
    now eapply subslet_extended_substE.
  - now eapply (wf_local_smash_endE_landed (wfΣ := wfΣ)).
Qed.

Definition typing_expand_letsE_fit (F : SRForecastCopy12) :=
  (@typing_expand_letsE_landed : ltac:(let t := type of (@typing_expand_letsE F) in exact t)).

(** [wf_local_expand_letsE] and [typing_expand_lets_genE] (copy 16, PCUICSREta.v:359, :365), base
    [wf_local_expand_lets] / [typing_expand_lets_gen] (PCUICInductives.v:2360-2393): the same
    three typed steps ([weakening_wf_localE] / [weakening_typingE], the substitution lemmas,
    [subslet_extended_substE]). DISCHARGED, both. *)
Lemma wf_local_expand_letsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {Γ Δ Γ' : list context_decl},
  wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
  wf_localE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ').
Proof.
  intros cf Σ wfΣ Γ Δ Γ' hwf.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  destruct (All_local_env_app_inv hwf) as [wfΓΔ _].
  rewrite -app_context_assoc in hwf.
  eapply (PCUICWeakeningTypEta.weakening_wf_localE (wfΣ := wfΣ) (Γ'' := smash_context [] Δ)) in hwf.
  - len in hwf. simpl in hwf. simpl.
    rewrite lift_context_app app_context_assoc Nat.add_0_r in hwf.
    eapply (substitution_wf_localE_landed (wfΣ := wfΣ)) in hwf; tea.
    now eapply (subslet_extended_substE (wfΣ := wfΣ)).
  - now eapply (wf_local_smash_endE_landed (wfΣ := wfΣ)).
Qed.

Definition wf_local_expand_letsE_fit (F : SRForecastCopy16) :=
  (@wf_local_expand_letsE_landed : ltac:(let t := type of (@wf_local_expand_letsE F) in exact t)).

Lemma typing_expand_lets_genE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {Γ Δ Γ' : list context_decl} {t T : term},
  Σ ;;; Γ ,,, Δ ,,, Γ' |-E t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' |-E
    expand_lets_k Δ #|Γ'| t : expand_lets_k Δ #|Γ'| T.
Proof.
  intros cf Σ wfΣ Γ Δ Γ' t T Ht.
  rewrite /expand_lets /expand_lets_k.
  pose proof (typingE_wf_local Ht) as X.
  rewrite -app_context_assoc in Ht.
  eapply (PCUICWeakeningTypEta.weakening_typingE (wfΣ := wfΣ) (Γ'' := smash_context [] Δ)) in Ht.
  - len in Ht. simpl in Ht. simpl.
    rewrite lift_context_app app_context_assoc Nat.add_0_r in Ht.
    eapply (substitutionE_landed (wfΣ := wfΣ)) in Ht; tea.
    + now len in Ht.
    + eapply (subslet_extended_substE (wfΣ := wfΣ)). now apply All_local_env_app_inv in X.
  - eapply (wf_local_smash_endE_landed (wfΣ := wfΣ)). now apply All_local_env_app_inv in X.
Qed.

Definition typing_expand_lets_genE_fit (F : SRForecastCopy16) :=
  (@typing_expand_lets_genE_landed
     : ltac:(let t := type of (@typing_expand_lets_genE F) in exact t)).

(** [on_minductive_wf_params_indices_instE] (copy 16 of T2a, PCUICValidityEta.v:320), base
    [on_minductive_wf_params_indices_inst] (PCUICInductives.v:295) through
    [on_minductive_wf_params_indices] (:247) and [it_mkProd_or_LetIn_wf_local]
    (PCUICArities.v:645). Landed: [on_declared_inductiveE] (field [onArityRed]),
    [inversion_LetInE] / [inversion_ProdE] (PCUICInversionEta.v:198, :165, no forecast),
    [wf_local_instantiateE]. DISCHARGED. *)
Lemma it_mkProd_or_LetIn_wf_localE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ T U} :
  Σ ;;; Γ |-E it_mkProd_or_LetIn Δ T : U -> wf_localE Σ (Γ ,,, Δ).
Proof.
  revert Γ T U. induction Δ as [|x Δ IH] using rev_ind; intros Γ T U.
  - intros h. exact (typingE_wf_local h).
  - rewrite it_mkProd_or_LetIn_app /=. intros h.
    have e : Γ ,,, (Δ ++ [x]) = (Γ ,, x) ,,, Δ by rewrite /app_context -app_assoc.
    rewrite e.
    destruct x as [na [b|] ty]; cbn in h.
    + first [ destruct (inversion_LetInE Σ wfΣ h) as (A & _ & hc & _)
            | destruct (inversion_LetInE Σ h) as (A & _ & hc & _) ].
      exact (IH _ _ _ hc).
    + first [ destruct (inversion_ProdE Σ wfΣ h) as (s1 & s2 & _ & hB & _)
            | destruct (inversion_ProdE Σ h) as (s1 & s2 & _ & hB & _) ].
      exact (IH _ _ _ hB).
Qed.

Lemma on_minductive_wf_params_indices_instE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body}
    (decli : declared_inductive Σ ind mdecl idecl) (u : Instance.t),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ ((ind_params mdecl ,,, ind_indices idecl)@[u]).
Proof.
  intros cf Σ wfΣ mdecl ind idecl decli u cu.
  have wfpi : wf_localE (Σ.1, ind_universes mdecl) (ind_params mdecl ,,, ind_indices idecl).
  { destruct (PCUICWeakeningEnvTypEta.on_declared_inductiveE (wfΣ := wfΣ) decli) as [_ oib].
    pose proof (onArityRed oib) as ona.
    rewrite -it_mkProd_or_LetIn_app in ona.
    destruct ona as (_ & s & Hs & _).
    eapply (it_mkProd_or_LetIn_wf_localE (Σ := (Σ.1, ind_universes mdecl)) (wfΣ := wfΣ)) in Hs.
    now rewrite app_context_nil_l in Hs. }
  have H := proj1 decli.
  unshelve epose proof (declared_minductive_to_gen H); eauto with pcuic.
  eapply (PCUICUnivSubstitutionTypEta.wf_local_instantiateE (decl := InductiveDecl mdecl)); eauto.
Qed.

Definition on_minductive_wf_params_indices_instE_fit (F : ValForecastCopy16) :=
  (@on_minductive_wf_params_indices_instE_landed
     : ltac:(let t := type of (@on_minductive_wf_params_indices_instE F) in exact t)).

(** ** Whole classes with every field discharged: instances from landed theorems only *)

Definition SRForecastCopy10_landed : SRForecastCopy10 :=
  {| subslet_ass_tipE := @subslet_ass_tipE_landed;
     subslet_defE := @subslet_defE_landed;
     subslet_lengthE := @subslet_lengthE_landed;
     subslet_untyped_subsletE := @subslet_untyped_subsletE_landed;
     substitution_letE := @substitution_letE_landed;
     substitution_wf_localE := @substitution_wf_localE_landed;
     wf_arities_contextE := @wf_arities_contextE_landed |}.

Definition SRForecastCopy12_landed : SRForecastCopy12 :=
  {| sorts_local_ctx_wf_localE := @sorts_local_ctx_wf_localE_landed;
     subslet_liftE := @subslet_liftE_landed;
     typing_expand_letsE := @typing_expand_letsE_landed;
     wf_local_smash_endE := @wf_local_smash_endE_landed |}.

Definition SRForecastCopy14_landed : SRForecastCopy14 :=
  {| on_minductive_wf_paramsE := @on_minductive_wf_paramsE_landed;
     ws_cumul_ctx_pb_appE := @ws_cumul_ctx_pb_appE_landed |}.

Definition ValForecastCopy10_landed : ValForecastCopy10 :=
  {| isType_substitutionE := @isType_substitutionE_landed;
     substitutionE := @substitutionE_landed;
     substitution0E := @substitution0E_landed |}.

Definition ValForecastCopy14_landed : ValForecastCopy14 :=
  {| subslet_indsE := @subslet_indsE_landed |}.

(** ** Copy 16 ([SRForecastCopy16], PCUICSREta.v:325-370) and copy 15 of T2a
    ([ValForecastCopy15], PCUICValidityEta.v:227-275) *)

(** [isType_introE] (PCUICSREta.v:328). Landed: [has_sort_isTypeE] (PCUICValidityEta.v:81,
    above the forecast block), the same fact with [s] explicit. DISCHARGED. *)
Lemma isType_introE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {T : term} {s : sort},
  Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof. intros cf Σ Γ T s h. exact (has_sort_isTypeE s h). Qed.

Definition isType_introE_fit (F : SRForecastCopy16) :=
  (@isType_introE_landed : ltac:(let t := type of (@isType_introE F) in exact t)).

(** [instantiate_indsE] (PCUICSREta.v:331), base [instantiate_inds] (PCUICInductives.v:203).
    Landed: [subst_instance_inds] (Conversion/PCUICUnivSubstitutionConv.v:1171) and
    [subst_instance_id_mdecl] (:1971); neither reads [wf] or the declaration. DISCHARGED. *)
Lemma instantiate_indsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1},
  forall {u : Instance.t} {mind : kername} {mdecl : mutual_inductive_body},
  declared_minductive Σ.1 mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (inds mind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl))@[u] =
  inds mind u (ind_bodies mdecl).
Proof.
  intros cf Σ wfΣ u mind mdecl _ cu.
  rewrite subst_instance_inds. f_equal.
  exact (subst_instance_id_mdecl Σ u mdecl cu).
Qed.

Definition instantiate_indsE_fit (F : SRForecastCopy16) :=
  (@instantiate_indsE_landed : ltac:(let t := type of (@instantiate_indsE F) in exact t)).

(** [spine_subst_subst_to_extended_list_kE] (PCUICValidityEta.v:239), base
    [spine_subst_subst_to_extended_list_k] (PCUICSpine.v:1860). Landed: base
    [subst_to_extended_list_k] (PCUICSubstitution.v:638) and [make_context_subst_spec_inv]
    (PCUICContextSubst.v:253) on the [context_subst] field. DISCHARGED. *)
Lemma spine_subst_subst_to_extended_list_kE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {args s : list term} {Δ : context},
  spine_substE Σ Γ args s Δ ->
  map (subst0 s) (to_extended_list_k Δ 0) = args.
Proof.
  intros cf Σ Γ args s Δ sp.
  have hm : make_context_subst (List.rev Δ) args [] = Some s.
  { apply make_context_subst_spec_inv. rewrite List.rev_involutive. exact (inst_ctx_substE sp). }
  have h := subst_to_extended_list_k s 0 args Δ hm.
  now rewrite map_lift0 in h.
Qed.

Definition spine_subst_subst_to_extended_list_kE_fit (F : ValForecastCopy15) :=
  (@spine_subst_subst_to_extended_list_kE_landed
     : ltac:(let t := type of (@spine_subst_subst_to_extended_list_kE F) in exact t)).

(** [map_subst_let_expand_to_extended_listE] (PCUICSREta.v:346), base
    [map_subst_let_expand_to_extended_list] (PCUICInductives.v:2444-2466): base's proof reads
    the spine only through [spine_subst_subst_to_extended_list_k], discharged above.
    DISCHARGED. *)
Lemma map_subst_let_expand_k_to_extended_list_liftE {cf : checker_flags} {Σ : global_env_ext}
  {s : list term} {Γ Δ : context} {k} :
  spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
  map (subst_let_expand_k (List.rev s) Δ k) (to_extended_list_k Δ k) = map (lift0 k) s.
Proof.
  intros sp.
  apply spine_subst_subst_to_extended_list_kE_landed in sp.
  rewrite /subst_let_expand_k.
  rewrite -map_map_compose.
  rewrite expand_lets_k_to_extended_list_k.
  rewrite -{2}(Nat.add_0_r k).
  rewrite PCUICLiftSubst.lift_to_extended_list_k -{2}sp !map_map_compose.
  apply map_ext. intros x.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma map_subst_let_expand_to_extended_listE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {s : list term} {Γ Δ : context},
  spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
  map (subst_let_expand (List.rev s) Δ) (to_extended_list Δ) = s.
Proof.
  intros cf Σ s Γ Δ sp.
  specialize (map_subst_let_expand_k_to_extended_list_liftE (k := 0) sp).
  now rewrite map_lift0.
Qed.

Definition map_subst_let_expand_to_extended_listE_fit (F : SRForecastCopy16) :=
  (@map_subst_let_expand_to_extended_listE_landed
     : ltac:(let t := type of (@map_subst_let_expand_to_extended_listE F) in exact t)).

(** [type_mkAppsE] (PCUICValidityEta.v:244, under [ClosedBodies]). Landed:
    [PCUICGenerationEta.type_mkAppsE] (PCUICGenerationEta.v:43) over the [PCUICGeneration]
    spine; every premise of that spine is one of the [PCUICArities] spine's, with
    [ws_cumul_pbE Cumul] forgotten to [cumulSpecE] by [ws_cumul_pbE_forget_spec]
    (PCUICWellScopedCumulativityEta.v:108, under exactly [ClosedBodies]). DISCHARGED. *)
Lemma type_mkAppsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ},
  forall {Γ : context} {t : term} {u : list term} {T t_ty : term},
  Σ ;;; Γ |-E t : t_ty ->
  typing_spineE Σ Γ t_ty u T ->
  Σ ;;; Γ |-E mkApps t u : T.
Proof.
  intros cf Σ wfΣ Γ t u T t_ty Ht Hsp.
  apply (PCUICGenerationEta.type_mkAppsE Σ Γ t u T t_ty Ht). clear Ht.
  induction Hsp as [ty ty' ity ity' c|ty hd tl na A B B' ity iprod c hhd _ IH].
  - exact (PCUICGenerationEta.type_spine_nilE Σ Γ ty ty' ity' (ws_cumul_pbE_forget_spec c)).
  - exact (PCUICGenerationEta.type_spine_consE Σ Γ hd tl na A B ty B'
             iprod (ws_cumul_pbE_forget_spec c) hhd IH).
Qed.

Definition type_mkAppsE_fit (F : ValForecastCopy15) :=
  (@type_mkAppsE_landed : ltac:(let t := type of (@type_mkAppsE F) in exact t)).

(** ** Copy 18 ([SRForecastCopy18], PCUICSREta.v:375-583): the rest *)

(** [cmp_global_instance_ind_invE] (PCUICSREta.v:407), base [cmp_global_instance_ind_inv]
    (PCUICInductiveInversion.v:2947). The statement has no E notion; base reads [wf] only
    through [declared_inductive_to_gen], which [wfE] satisfies (it is generic in the typing
    of the environment), and its [on_declared_inductive] line is dead. DISCHARGED. *)
Lemma cmp_global_instance_ind_invE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall (cmp_universe : conv_pb -> Relation_Definitions.relation Universe.t) (pb : conv_pb)
    (ind : inductive) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (napp : nat)
    (u u' : Instance.t),
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  declared_inductive Σ ind mdecl idecl ->
  cmp_global_instance Σ cmp_universe pb (IndRef ind) napp u u' ->
  ((context_assumptions (ind_indices idecl) + context_assumptions (ind_params mdecl) <= napp ×
    (∑ l : list Variance.t, ind_variance mdecl = Some l × cmp_universe_instance_variance cmp_universe pb l u u')) +
   cmp_universe_instance (cmp_universe Conv) u u')%type.
Proof.
  intros cf Σ wfΣ cmp_universe pb ind mdecl idecl napp u u' Hsub decli.
  unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
  unfold cmp_global_instance, cmp_global_instance_gen, global_variance.
  rewrite (declared_inductive_lookup_gen decli').
  simpl. rewrite context_assumptions_app.
  elim: leb_spec_Set => // comp. 2: now right.
  destruct ind_variance eqn:indv => //. 2: now right.
  move/cmp_opt_variance_var_dec => [|H]. 1: now right.
  left.
  now repeat eexists.
Qed.

Definition cmp_global_instance_ind_invE_fit (F : SRForecastCopy18) :=
  (@cmp_global_instance_ind_invE_landed
     : ltac:(let t := type of (@cmp_global_instance_ind_invE F) in exact t)).

(** [into_ws_cumul_pb_termsE] (PCUICSREta.v:456), base [into_ws_cumul_pb_terms]
    (PCUICInductiveInversion.v:3100). Landed: [into_ws_cumul_pbE_spec]
    (PCUICWellScopedCumulativityEta.v:122, under [ClosedBodies]). DISCHARGED. *)
Lemma into_ws_cumul_pb_termsE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {Γ : list context_decl} {l l' : list term},
  All2 (convSpecE Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  ws_cumul_pbE_terms Σ Γ l l'.
Proof.
  intros cf Σ wfΣ Γ l l' a hΓ hl hl'.
  have cb : ClosedBodies Σ := PCUICClosedTypEta.wfE_ClosedBodies Σ (wfΣ := wfΣ).
  solve_all. eapply All2_impl; [eassumption|]. cbn. intros x y [[hx c] hy].
  exact (into_ws_cumul_pbE_spec c hΓ hx hy).
Qed.

Definition into_ws_cumul_pb_termsE_fit (F : SRForecastCopy18) :=
  (@into_ws_cumul_pb_termsE_landed
     : ltac:(let t := type of (@into_ws_cumul_pb_termsE F) in exact t)).

(** [pre_case_branch_context_eqE] (PCUICSREta.v:498), base [pre_case_branch_context_eq]
    (PCUICInductiveInversion.v:4299). The statement is syntactic; base's one
    environment-dependent step is [instantiate_inds], discharged above. DISCHARGED. *)
Lemma pre_case_branch_context_eqE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {params : list term} {puinst : Instance.t} {bctx : list aname} {cdecl : constructor_body},
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) puinst ->
  wf_branch_gen cdecl bctx ->
  eq_context_upto_names
    (pre_case_branch_context ind mdecl params puinst cdecl)
    (case_branch_context_gen ind mdecl params puinst bctx cdecl).
Proof.
  intros cf Σ wfΣ ind mdecl idecl params puinst bctx cdecl decli cu.
  unfold wf_branch_gen. intros wf%Forall2_All2.
  rewrite /pre_case_branch_context /case_branch_context_gen.
  symmetry. etransitivity.
  - eapply eq_binder_annots_eq.
    rewrite /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
    eapply All2_eq_binder_subst_context_inst.
    now eapply All2_eq_binder_subst_context.
  - rewrite /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
    eapply alpha_eq_subst_context.
    rewrite subst_instance_expand_lets_ctx subst_instance_subst_context.
    now rewrite (instantiate_indsE_landed (wfΣ := wfΣ) (proj1 decli) cu).
Qed.

Definition pre_case_branch_context_eqE_fit (F : SRForecastCopy18) :=
  (@pre_case_branch_context_eqE_landed
     : ltac:(let t := type of (@pre_case_branch_context_eqE F) in exact t)).

(** [positive_cstr_closed_indicesE] (PCUICSREta.v:491), base [positive_cstr_closed_indices]
    (PCUICInductiveInversion.v:1295). The statement has no E notion. Landed:
    [on_declared_constructorE] (Typing/PCUICWeakeningEnvTypEta.v:472; [on_ctype_positive] does
    not read the typing relation) and [declared_inductive_closed_paramsE]
    (Typing/PCUICClosedTypEta.v:641). DISCHARGED. *)
Lemma positive_cstr_closed_indicesE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {i : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {cdecl : constructor_body},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (fun t : term => closedn (context_assumptions (cstr_args cdecl) + #|ind_params mdecl|) t)
    (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)).
Proof.
  intros cf Σ wfΣ i mdecl idecl cdecl H.
  pose proof (PCUICWeakeningEnvTypEta.on_declared_constructorE (wfΣ := wfΣ) H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_ctype_positive)).
  rewrite onc.(cstr_eq) in X. unf_env.
  rewrite -it_mkProd_or_LetIn_app in X.
  eapply positive_cstr_it_mkProd_or_LetIn in X as [hpars hpos].
  rewrite app_context_nil_l in hpos.
  rewrite expand_lets_mkApps in hpos.
  unfold cstr_concl_head in hpos.
  have subsrel := expand_lets_tRel (#|ind_bodies mdecl| - S (inductive_ind i.1))
    (ind_params mdecl ,,, cstr_args cdecl). len in subsrel.
  rewrite (Nat.add_comm #|cstr_args cdecl|) Nat.add_assoc in subsrel.
  rewrite {}subsrel in hpos.
  depelim hpos; solve_discr.
  eapply All_map_inv in a.
  eapply All_app in a as [ _ a].
  eapply All_map; eapply (All_impl a); intros x; len.
  rewrite closedn_expand //.
  exact (PCUICClosedTypEta.declared_inductive_closed_paramsE (wfΣ := wfΣ) (proj1 H)).
Qed.

Definition positive_cstr_closed_indicesE_fit (F : SRForecastCopy18) :=
  (@positive_cstr_closed_indicesE_landed
     : ltac:(let t := type of (@positive_cstr_closed_indicesE F) in exact t)).

(** [conv_decls_fix_contextE] (PCUICSREta.v:440), base [conv_decls_fix_context(_gen)]
    (PCUICInductiveInversion.v:859-901). Landed: [weakening_ws_cumul_pbE]
    (PCUICWsCumulEtaSubst.v:189), [ws_cumul_ctx_pbE_refl_pb] (PCUICWsCumulEtaCtx.v:157),
    [ws_cumul_ctx_pbE_closed_left] (:120), [wf_local_closed_contextE]. DISCHARGED. *)
Lemma conv_decls_fix_context_genE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ mfix mfix1 :
  All2 (fun d d' => ws_cumul_pbE Conv Σ Γ (dtype d) (dtype d') × eq_binder_annot (dname d) (dname d'))
    mfix mfix1 ->
  forall Γ' Γ'',
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
  ws_cumul_ctx_pbE_rel Conv Σ (Γ ,,, Γ') (fix_context_gen #|Γ'| mfix) (fix_context_gen #|Γ''| mfix1).
Proof.
  intros a Γ' Γ'' convctx.
  have cb : ClosedBodies Σ := PCUICClosedTypEta.wfE_ClosedBodies Σ (wfΣ := wfΣ).
  split; [exact (ws_cumul_ctx_pbE_closed_left convctx)|].
  induction a in Γ', Γ'', convctx |- *; [constructor|]. simpl.
  destruct r as [r eqann].
  assert (decl_ws_cumul_pbE Σ (Γ ,,, Γ' ,,, [])
    (vass (dname x) (lift0 #|Γ'| (dtype x)))
    (vass (dname y) (lift0 #|Γ''| (dtype y)))) as hd.
  { constructor; tas.
    pose proof (All2_fold_length convctx) as H.
    rewrite !length_app in H. assert (#|Γ'| = #|Γ''|) as H0 by lia.
    rewrite -H0.
    exact (weakening_ws_cumul_pbE (Γ' := []) r (ws_cumul_ctx_pbE_closed_left convctx)). }
  apply All2_fold_app.
  - constructor; [constructor|exact hd].
  - eapply (All2_fold_impl (P := (fun Δ Δ' : context =>
      decl_ws_cumul_pbE Σ (Γ ,,, (vass (dname x) (lift0 #|Γ'| (dtype x)) :: Γ') ,,, Δ)))).
    + eapply (IHa (vass _ _ :: Γ') (vass _ _ :: Γ'')).
      cbn; constructor; [exact convctx|exact hd].
    + intros. red.
      now rewrite ![_ ,,, _]app_context_assoc.
Qed.

Lemma conv_decls_fix_contextE_landed :
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
  forall {Γ : context} {mfix mfix1 : list (def term)},
  wf_localE Σ Γ ->
  All2 (fun d d' : def term =>
          ws_cumul_pbE Conv Σ Γ (dtype d) (dtype d') × eq_binder_annot (dname d) (dname d'))
    mfix mfix1 ->
  All2_fold (fun Δ _ : context => decl_ws_cumul_pbE Σ (Γ ,,, Δ)) (fix_context mfix) (fix_context mfix1).
Proof.
  intros cf Σ wfΣ Γ mfix mfix1 wfΓ a.
  apply (conv_decls_fix_context_genE (wfΣ := wfΣ) Γ mfix mfix1 a [] []).
  apply ws_cumul_ctx_pbE_refl_pb. exact (PCUICClosedTypEta.wf_local_closed_contextE wfΓ).
Qed.

Definition conv_decls_fix_contextE_fit (F : SRForecastCopy18) :=
  (@conv_decls_fix_contextE_landed
     : ltac:(let t := type of (@conv_decls_fix_contextE F) in exact t)).

(** ** Reductions to T2a's forecast classes (REDUCED, not discharged)

  Each lemma below follows in a few lines from a lemma of [PCUICValidityEta]'s section
  [ValidityEta], which takes T2a's four classes [ValForecastCopy10/14/15/16]. Every consumer
  of the field ([PCUICSREta], [BDToPCUICEta], [BDFromPCUICEta]) already takes those four, so
  deleting the field adds no premise anywhere; the obligation moves to copies 10/14/15/16. *)
Section ReducedToT2a.
  Context {V10 : ValForecastCopy10} {V14 : ValForecastCopy14} {V15 : ValForecastCopy15}
    {V16 : ValForecastCopy16}.

  (** [declared_constructor_valid_tyE] (PCUICSREta.v:448): [validityE] (PCUICValidityEta.v:784)
      on [typeE_Construct], base's proof. *)
  Lemma declared_constructor_valid_tyE_reduced :
    forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mdecl : mutual_inductive_body)
      (idecl : one_inductive_body) (i : inductive) (n : nat) (cdecl : constructor_body) (u : Instance.t),
    wfE Σ.1 ->
    wf_localE Σ Γ ->
    declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeE Σ Γ (type_of_constructor mdecl cdecl (i, n) u).
  Proof.
    intros cf Σ Γ mdecl idecl i n cdecl u wfΣ wfΓ declc cu.
    eapply (validityE (wfΣ := wfΣ)). eapply typeE_Construct; eassumption.
  Qed.

  Definition declared_constructor_valid_tyE_fit (F : SRForecastCopy18) :=
    (@declared_constructor_valid_tyE_reduced
       : ltac:(let t := type of (@declared_constructor_valid_tyE F) in exact t)).

  (** [inversion_mkApps_directE] (PCUICSREta.v:226): [inversion_mkAppsE] (PCUICValidityEta.v:801)
      and [validityE] for the sort of the head's type. *)
  Lemma inversion_mkApps_directE_reduced :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall {Γ : context} {f : term} {u : list term} {T : term},
    isTypeE Σ Γ T ->
    Σ ;;; Γ |-E mkApps f u : T ->
    ∑ (A : term) (s' : sort),
      (Σ ;;; Γ |-E f : A) × (Σ ;;; Γ |-E A : tSort s') × typing_spineE Σ Γ A u T.
  Proof.
    intros cf Σ wfΣ Γ f u T _ h.
    destruct (inversion_mkAppsE (wfΣ := wfΣ) h) as [A [hf sp]].
    destruct (validityE (wfΣ := wfΣ) hf) as (_ & s & hA & _).
    exists A, s. exact (hf, (hA, sp)).
  Qed.

  Definition inversion_mkApps_directE_fit (F : SRForecastCopy15) :=
    (@inversion_mkApps_directE_reduced
       : ltac:(let t := type of (@inversion_mkApps_directE F) in exact t)).

End ReducedToT2a.

(** ** T8: the iteration of the one-step postponement (REDUCED)

  The open "iteration" of [PCUICEtaT8Probe] (header, "Why the one-step commutation does not
  iterate by itself"): from [pe_postpone_statement] (PCUICEtaT8Probe.v:1358) for a [Good] that
  [red1] preserves, [η* · red ⊆ red · η*] on [Good] sources. Landed: [eta_iff_pe]
  (PCUICEtaT8Probe.v:1715, [η* = pe]) and, for the probe's [Good], [Good_red] (:2738). Only the
  one-step statement stays open. *)
Lemma pe_postpone_red (Σ : global_env) (Good : context -> term -> Type)
  (Hgood : forall Γ t u, Good Γ t -> red1 Σ Γ t u -> Good Γ u)
  (H : PCUICEtaT8Probe.pe_postpone_statement Σ Good) Γ t u v :
  Good Γ t -> PCUICEtaT8Probe.pe t u -> red Σ Γ u v ->
  ∑ w, red Σ Γ t w × PCUICEtaT8Probe.pe w v.
Proof.
  intros hg hp hr. apply clos_rt_rt1n_iff in hr.
  induction hr as [u|u u1 v hs _ IH] in t, hg, hp |- *.
  - exists t. split; [apply rt_refl|exact hp].
  - destruct (H Γ t u u1 hg hp hs) as (w & hw & hpw).
    have hrw : red Σ Γ t w.
    { clear -hw. induction hw; [now apply rt_step|eapply rt_trans; eassumption]. }
    have hgw : Good Γ w.
    { clear -hg hrw Hgood. apply clos_rt_rt1n_iff in hrw.
      induction hrw as [x|x y z r _ IHr] in hg |- *; [exact hg|exact (IHr (Hgood _ _ _ hg r))]. }
    destruct (IH w hgw hpw) as (z & hz & hpz).
    exists z. split; [eapply rt_trans; eassumption|exact hpz].
Qed.

Lemma eta_red_postpone_Good (Σ : global_env)
  (H : PCUICEtaT8Probe.pe_postpone_statement Σ (PCUICEtaT8Probe.Good Σ)) Γ t u v :
  PCUICEtaT8Probe.Good Σ Γ t -> eta t u -> red Σ Γ u v -> ∑ w, red Σ Γ t w × eta w v.
Proof.
  intros hg he hr.
  have Hgood : forall Γ t u, PCUICEtaT8Probe.Good Σ Γ t -> red1 Σ Γ t u -> PCUICEtaT8Probe.Good Σ Γ u.
  { intros Γ' t' u' hg' hr'. eapply PCUICEtaT8Probe.Good_red; [exact hg'|now apply rt_step]. }
  destruct (pe_postpone_red Σ _ Hgood H Γ t u v hg (fst (PCUICEtaT8Probe.eta_iff_pe t u) he) hr)
    as (w & hw & hp).
  exists w. split; [exact hw|exact (PCUICEtaT8Probe.pe_to_eta _ _ hp)].
Qed.

(** ** T8: the η-at-the-root case of the parallel postponement (REDUCED to the statement on the
    body)

  Open part of [PCUICEtaT8Probe] (status block, :2584-2586): "the generic η-at-the-root case
  ([pe_eta] source, any [red1] step): [pp_root] with the IH on the body". The case follows from
  landed pieces exactly as [pp_root] (PCUICEtaT8Probe.v:265) does, given
  [pe_postpone_statement] for the body [b] (the induction hypothesis of the [pe_eta] case, in
  the extended context): [red1_lift1] (:260) lifts the step under the binder, [Good_lam_body]
  (:2741) gives the invariant on the body, [abs_red_r] and [pe_eta] (:1076) rebuild the λ. The
  premise [on_free_vars xpredT M'] is [pp_root]'s. So this case adds no new obligation: what
  remains of [pe_postpone_statement] is the congruence cases. *)
Lemma pe_postpone_eta_root {cf : checker_flags} {Σ : global_env} (cb : ClosedBodies Σ) Γ na A b M' v :
  (forall Γ' u w, PCUICEtaT8Probe.Good Σ Γ' b -> PCUICEtaT8Probe.pe b u -> red1 Σ Γ' u w ->
     ∑ z, trans_clos (red1 Σ Γ') b z × PCUICEtaT8Probe.pe z w) ->
  on_free_vars xpredT M' ->
  PCUICEtaT8Probe.Good Σ Γ (tLambda na A b) ->
  PCUICEtaT8Probe.pe b (tApp (lift0 1 M') (tRel 0)) ->
  red1 Σ Γ M' v ->
  ∑ w, trans_clos (red1 Σ Γ) (tLambda na A b) w × PCUICEtaT8Probe.pe w v.
Proof.
  intros IH ho hg hp hr.
  have hr' : red1 Σ (Γ ,, vass na A) (tApp (lift0 1 M') (tRel 0)) (tApp (lift0 1 v) (tRel 0)).
  { apply app_red_l. exact (PCUICEtaT8Probe.red1_lift1 cb Γ na A M' v ho hr). }
  destruct (IH (Γ ,, vass na A) _ _ (PCUICEtaT8Probe.Good_lam_body (Σ := Σ) Γ na A b hg) hp hr')
    as (w & hw & hpw).
  exists (tLambda na A w). split.
  - clear -hw. induction hw; [apply t_step; now apply abs_red_r|eapply t_trans; eassumption].
  - exact (PCUICEtaT8Probe.pe_eta na A w v hpw).
Qed.

(** ** T8: the [_l] statements from the [_r] statements (REDUCED)

  [ws_cumul_pbE Conv] is symmetric, but [ws_cumul_pbE Cumul] is not, so [_l] is not [_r]
  read backwards. Each [_l] follows from its [_r] all the same, by four landed facts:
  1. the A6 inversion [ws_cumul_pbE_*_l_inv] (PCUICEtaA6.v:199, :217; PCUICEtaA6Ind.v:275)
     gives a chain [(R_c ∪ eta1)*] from [canon T] to a head form [H1];
  2. that chain alone is a [JoinE Conv] of [T] and [H1] ([H1] is canonical,
     [chain_canonical], so its own side is the empty chain), hence
     [ws_cumul_pbE Conv T H1] ([chain_ws_cumul_pbE_Conv] below);
  3. [_r] at [Conv] reduces [T] to a head form [H2]; [red_ws_cumul_pbE] and transitivity
     turn the premise [H ≤[pb] T] into [H ≤[pb] H2];
  4. the head-against-head inversion ([ws_cumul_pbE_Sort_inv], PCUICEtaA6.v:176;
     [ws_cumul_pbE_Prod_Prod_inv], :273; [ws_cumul_pbE_Ind_inv], PCUICEtaA6Ind.v:313)
     reads off exactly the [_l] conclusion. The product codomain moves from
     [Γ ,, vass na' dom'] to [Γ ,, vass na dom] by [ws_cumul_pbE_bodies]
     (PCUICWsCumulEtaCtx.v:250): the join reads a context only through its let-bodies. *)

(** A chain from [canon T] to [H] is an E conversion of [T] and [H]. *)
Lemma chain_ws_cumul_pbE_Conv {cf : checker_flags} {Σ : global_env_ext} {cb : ClosedBodies Σ} Γ T H :
  is_closed_context Γ -> is_open_term Γ T ->
  clos_refl_trans (union (R_c Σ Γ) eta1) (canon T) H -> ws_cumul_pbE Conv Σ Γ T H.
Proof.
  intros hΓ hT hch.
  have hcan : canon H = H := chain_canonical (Σ := Σ) Γ (canon T) H (canon_idem T) hch.
  constructor; [exact hΓ|exact hT|exact (chain_open (Σ := Σ) (wfΣ := cb) Γ T H hΓ hT hch)|].
  exists H, H. split; [exact hch|split; [rewrite hcan; apply rt_refl|apply compare_term_eta_refl]].
Qed.

Lemma T8_Sort_l_of_r {cf : checker_flags} (Σ : global_env_ext) :
  PCUICEtaT8Probe.T8_Sort_r_statement Σ -> PCUICEtaT8Probe.T8_Sort_l_statement Σ.
Proof.
  intros hr Γ pb T s s' wfΣ hT hc.
  have cb : ClosedBodies Σ := PCUICClosedTypEta.wfE_ClosedBodies Σ (wfΣ := wfΣ).
  destruct (ws_cumul_pbE_Sort_l_inv (Σ := Σ) pb hc) as (s1 & hch & _).
  have hconv := chain_ws_cumul_pbE_Conv (cb := cb) Γ T _ (wsE_ctx hc) (wsE_right hc) hch.
  destruct (hr Γ Conv T s1 s' wfΣ hT hconv) as (s2 & hred & _).
  exists s2. split; [exact hred|].
  have h2 : ws_cumul_pbE pb Σ Γ (tSort s) (tSort s2) :=
    ws_cumul_pbE_trans (Σ := Σ) (wfΣ := cb) _ _ _ hc (red_ws_cumul_pbE (wfΣ := cb) hred).
  exact (ws_cumul_pbE_Sort_inv (Σ := Σ) pb h2).
Qed.

Lemma T8_Prod_l_of_r {cf : checker_flags} (Σ : global_env_ext) :
  PCUICEtaT8Probe.T8_Prod_r_statement Σ -> PCUICEtaT8Probe.T8_Prod_l_statement Σ.
Proof.
  intros hr Γ pb T na dom codom s' wfΣ hT hc.
  have cb : ClosedBodies Σ := PCUICClosedTypEta.wfE_ClosedBodies Σ (wfΣ := wfΣ).
  destruct (ws_cumul_pbE_Prod_l_inv (Σ := Σ) hc) as (na1 & dom1 & codom1 & [hch _ hdom _]).
  have hconv := chain_ws_cumul_pbE_Conv (cb := cb) Γ T _ (wsE_ctx hc) (wsE_right hc) hch.
  destruct (hr Γ Conv T na1 dom1 codom1 s' wfΣ hT hconv) as (na2 & dom2 & codom2 & [hred _ _ _]).
  have h2 : ws_cumul_pbE pb Σ Γ (tProd na dom codom) (tProd na2 dom2 codom2) :=
    ws_cumul_pbE_trans (Σ := Σ) (wfΣ := cb) _ _ _ hc (red_ws_cumul_pbE (wfΣ := cb) hred).
  destruct (ws_cumul_pbE_Prod_Prod_inv (Σ := Σ) h2) as [hna hd hcd].
  exists na2, dom2, codom2. split; [exact hred|exact hna|exact hd|].
  eapply ws_cumul_pbE_bodies; [|exact (closed_snoc_vass Γ na dom (wsE_ctx hc) (wsE_left hdom))|exact hcd].
  apply upto_domain_r_bodies_vass, upto_domain_r_bodies_refl.
Qed.

Lemma T8_Ind_l_of_r {cf : checker_flags} (Σ : global_env_ext) :
  PCUICEtaT8Probe.T8_Ind_r_statement Σ -> PCUICEtaT8Probe.T8_Ind_l_statement Σ.
Proof.
  intros hr Γ pb T ind ui l s' wfΣ hT hc.
  have cb : ClosedBodies Σ := PCUICClosedTypEta.wfE_ClosedBodies Σ (wfΣ := wfΣ).
  destruct (ws_cumul_pbE_Ind_l_inv (Σ := Σ) hc) as (ui1 & l1 & [hch _ _]).
  have hconv := chain_ws_cumul_pbE_Conv (cb := cb) Γ T _ (wsE_ctx hc) (wsE_right hc) hch.
  destruct (hr Γ Conv T ind ui1 l1 s' wfΣ hT hconv) as (ui2 & l2 & [hred _ _]).
  have h2 : ws_cumul_pbE pb Σ Γ (mkApps (tInd ind ui) l) (mkApps (tInd ind ui2) l2) :=
    ws_cumul_pbE_trans (Σ := Σ) (wfΣ := cb) _ _ _ hc (red_ws_cumul_pbE (wfΣ := cb) hred).
  destruct (ws_cumul_pbE_Ind_inv (Σ := Σ) h2) as [_ hu _ hl].
  exists ui2, l2. split; [exact hred|exact hu|exact hl].
Qed.

(** ** Assumptions

  Every DISCHARGED lemma together, then each class instance, then the REDUCED lemmas: the build
  log prints their [Print Assumptions]. A REDUCED lemma's open statement is an argument, so it
  is not listed. *)
Definition inventory_sweep_discharged :=
  (@isType_is_open_termE_landed, @cmp_global_instance_ind_invE_landed,
   @into_ws_cumul_pb_termsE_landed, @pre_case_branch_context_eqE_landed,
   @positive_cstr_closed_indicesE_landed, @conv_decls_fix_contextE_landed,
   @ctx_inst_instE_landed, @ctx_inst_open_termsE_landed, @spine_subst_inj_substE_landed,
   @subslet_skipnE_landed, @wf_local_alphaE_landed, @ws_cumul_ctx_pb_eq_leE_landed,
   @ws_cumul_ctx_pb_rel_transE_landed,
   @isType_introE_landed, @instantiate_indsE_landed, @map_subst_let_expand_to_extended_listE_landed,
   @wf_local_expand_letsE_landed, @typing_expand_lets_genE_landed,
   @spine_subst_subst_to_extended_list_kE_landed, @type_mkAppsE_landed,
   @on_minductive_wf_params_indices_instE_landed).
Print Assumptions inventory_sweep_discharged.
Print Assumptions SRForecastCopy10_landed.
Print Assumptions SRForecastCopy12_landed.
Print Assumptions SRForecastCopy14_landed.
Print Assumptions ValForecastCopy10_landed.
Print Assumptions ValForecastCopy14_landed.

Definition inventory_sweep_reduced :=
  (@declared_constructor_valid_tyE_reduced, @inversion_mkApps_directE_reduced,
   @pe_postpone_red, @eta_red_postpone_Good, @pe_postpone_eta_root,
   @T8_Sort_l_of_r, @T8_Prod_l_of_r, @T8_Ind_l_of_r).
Print Assumptions inventory_sweep_reduced.
