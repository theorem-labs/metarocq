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
     PCUICWeakeningTypEta PCUICWeakeningEnvTypEta.
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
