(* Distributed under the terms of the MIT license. *)
(* The header is EtaMetaLane's [PCUICSREta]'s (fork/wip/eta-meta-integ1-2026-10-29 @ 9d9eda50,
   [pcuic/theories/PCUICSREta.v:7-53]), every module of which is on this tree, so that the copy of its
   [prim_op_head_typeE] below runs with the same tactics and hints. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICUtils PCUICOnOne
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv PCUICWeakeningEnv PCUICWeakeningEnvConv
     PCUICWeakeningEnvTyp PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSubstitution PCUICContextSubst PCUICCasesContexts PCUICClosed PCUICClosedTyp PCUICClosedConv PCUICCasesWfTyp
     PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICContextConversionTyp
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICWellScopedCumulativity PCUICGuardCondition
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICFixWitness PCUICInductiveInversion
     PCUICSigmaCalculus PCUICPrimitiveRed PCUICOnFreeVars PCUICContextReduction
     PCUICSR.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure
     PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions PCUICClosedBodies
     PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta PCUICCasesWfTypEta
     PCUICGuardClosureEta PCUICWfUniversesEta
     PCUICEtaI5 PCUICEtaI5A2 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICEtaJoinSpec PCUICEtaFInstGlue
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC Require Import PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta
     PCUICInductivesEta PCUICInductiveInversionEta.
From MetaRocq.PCUIC Require Import PCUICWsCumulEtaInstancesGlobal.
From MetaRocq.PCUIC.Typing Require Import PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require Import PCUICValidityEta.
From MetaRocq.PCUIC.Typing Require PCUICUnivSubstitutionTypEta.
From MetaRocq.PCUIC Require PCUICGenerationEta.

From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.
Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** * ETAK discharge, row 47: an over-applied registered operation is not [welltypedE]

  BET-64 EtaCheckerLane, worker EtaTranscribe6, 2026-10-30. Row 47 of
  [lanes/eta/etak/eta51-sizing.md] (TRANSCRIPTION): the field [rtfc_prim_overapplied] of
  [PCUICEtaFactsCompose.ReduceTypedFactsCoreE]. Its base proof is [PCUICSafeReduce.v:161]
  ([prim_app_overapplied_ill_typed]) with [:99] ([typing_spine_prim_args_sat]) and [:129]
  ([prim_app_saturated_not_prod]); their E twins are below, each base's statement with [typing] →
  [typingE], [wf] → [wfE], [⊢] → [⊢E], [typing_spine] → [PCUICAritiesEta.typing_spineE], and base's
  script with each lemma replaced by its landed E twin:
  - [validity], [inversion_mkApps] → [validityE], [inversion_mkAppsE] ([PCUICValidityEta]);
  - [PCUICSpine.inversion_mkApps_direct] → [inversion_mkApps_directE] ([PCUICSpineEta]);
  - [inversion_Const], [inversion_App] → [inversion_ConstE], [inversion_AppE] ([PCUICInversionEta]);
  - [ws_cumul_pb_Prod_Prod_inv], [substitution0_ws_cumul_pb] → [ws_cumul_pbE_Prod_Prod_inv]
    ([PCUICEtaA6]), [substitution0_ws_cumul_pbE] ([PCUICWsCumulEtaSubst]);
  - [invert_cumul_ind_prod] → [invert_cumul_ind_prodE] ([PCUICEtaA6Ind]);
  - the [SInt] case: base's [ws_cumul_pb_Axiom_l_inv] then [invert_red_prod] (a closed reduction of a
    product to an axiom application) is, over E, the landed head clash [invert_cumul_axiom_prodE]
    ([PCUICEtaA6Ind.v:445]: an axiom application is not below a product), which states that
    conclusion directly; the E inversion [ws_cumul_pbE_Axiom_l_inv] concludes with a [chain] of
    canonical forms, not a closed reduction, so base's two steps do not transcribe one by one;
  - [prim_op_head_type] ([PCUICSR.v:1702]) → [dsc_prim_op_head_typeE] below, a copy of EtaMetaLane's E
    twin [PCUICSREta.prim_op_head_typeE] (integ1 @ 9d9eda50, [PCUICSREta.v:996-1049], proof unchanged),
    which is not on this tree. Its proof uses no subject reduction and no forecast class (it is
    environment plumbing). The prefix [dsc_] keeps it from colliding with [PCUICSREta.prim_op_head_typeE]
    when that file lands; that landing makes this copy redundant (replace by import, after the
    two-way compiled check).
  No hypothesis (no [Context], no class field). *)

(** Copy of EtaMetaLane's [PCUICSREta.prim_op_head_typeE] (integ1 @ 9d9eda50, [PCUICSREta.v:992-1049]),
    twin of base [prim_op_head_type] ([PCUICSR.v:1702]). Its comment, verbatim: Under [wfE] the
    registering declaration's conversion is [cumulSpecE0]; it moves to [Σ], the instance and the context
    by [weakening_env_convSpecE], [convSpecE_subst_instance] (P2), and enters [ws_cumul_pbE] by I5's
    [into_ws_cumul_pbE_spec] in place of base [cumulSpec_cumulAlgo]. *)
Lemma dsc_prim_op_head_typeE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ c u decl op A} :
  wf_localE Σ Γ ->
  declared_constant Σ c decl ->
  consistent_instance_ext Σ (cst_universes decl) u ->
  prim_op_of Σ c = Some op ->
  Σ ;;; Γ ⊢E (cst_type decl)@[u] ≤ A ->
  ∑ res Tp,
    [× PCUICPrimOpType.prim_shape_type Σ.1.(retroknowledge) (po_shape (info op)) = Some res,
       PCUICPrimOpType.prim_arg_types Σ.1.(retroknowledge) (po_args (info op)) res = Some Tp,
       Σ ;;; Γ ⊢E Tp ≤ A,
       on_prim_op_result Σ (po_shape (info op)) &
       All (prim_op_tag_declared Σ) (po_args (info op))].
Proof.
  intros wfΓ hdecl cu hop hle.
  unshelve epose proof (hg := declared_constant_to_gen hdecl); eauto.
  destruct (lookup_on_global_env_prim_decl wfΣ hg) as (Σ' & [onΣ' ext hretro hpd]).
  cbn in hpd. specialize (hpd op). forward hpd.
  { unfold prim_op_of in *. cbn. rewrite hretro. exact hop. }
  destruct hpd as [_ huniv [Tp [hTp hconv]] hargsinv hres].
  rewrite hretro in hTp. unfold PCUICPrimOpType.prim_op_type in hTp.
  destruct (PCUICPrimOpType.prim_shape_type _ (po_shape (info op))) as [res|] eqn:hsh => //.
  exists res, Tp.
  destruct (prim_shape_type_closed_inst _ _ _ u hsh) as [hclres hures].
  destruct (prim_arg_types_closed_inst _ _ _ _ u hTp hclres hures) as [hclTp huTp].
  assert (hext : extends Σ' Σ.1)
    by (eapply extends_decls_extends, strictly_extends_decls_extends_decls; tea).
  split; [reflexivity|exact hTp| | |].
  - change (cumulSpecE0 (Σ', cst_universes decl) [] Conv (cst_type decl) Tp) in hconv.
    eapply (weakening_env_convSpecE Σ' Σ.1 (cst_universes decl) []) in hconv; tea.
    eapply (convSpecE_subst_instance (Σ.1, cst_universes decl) [] u _ _ Σ.2) in hconv.
    2:{ eapply PCUICUnivSubstitutionTypEta.consistent_instance_valid_constraintsE; tea.
        split; [exact wfΣ|]. now eapply (weaken_lookup_on_global_env' _ _ (ConstantDecl decl)). }
    rewrite huTp in hconv. cbn in hconv.
    assert (hcl : closed (cst_type decl)@[u]).
    { rewrite closedn_subst_instance. eapply declared_constant_closed_typeE; tea. }
    have hws : Σ ;;; [] ⊢E (cst_type decl)@[u] = Tp.
    { apply into_ws_cumul_pbE_spec; [destruct Σ; exact hconv|reflexivity|..];
        now eapply closedn_on_free_vars. }
    eapply (weakening_ws_cumul_pbE (Γ := []) (Γ' := []) (Γ'' := Γ)) in hws.
    2: rewrite app_context_nil_l; now eapply wf_local_closed_contextE.
    cbn in hws. rewrite app_context_nil_l !lift_closed in hws; tas.
    etransitivity; [|exact hle]. eapply ws_cumul_pbE_eq_le. now symmetry.
  - destruct (po_shape (info op)); cbn in hres |- *.
    + destruct hres as (kn & d & [hpc hd hinv]). exists kn, d. split; tas.
      * cbn in hpc |- *. now rewrite -hretro.
      * eapply weakening_env_declared_constant; tea.
    + destruct hres as (i & mdecl & idecl & hpb & hdi). exists i, mdecl, idecl. split.
      * exact (eq_trans (f_equal Retroknowledge.retro_bool (eq_sym hretro)) hpb).
      * eapply weakening_env_declared_inductive; tea.
  - eapply All_impl; [exact hargsinv|]. intros t (kn & d & [hpc hd hinv]).
    exists kn, d. split; tas.
    + unfold primitive_constant in hpc |- *. now rewrite -hretro.
    + eapply weakening_env_declared_constant; tea.
Qed.

(** Base [typing_spine_prim_args_sat] ([PCUICSafeReduce.v:99]). *)
Lemma typing_spine_prim_args_satE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ r tags res T} {args : list term} ty ty' :
  PCUICPrimOpType.prim_arg_types r tags res = Some ty ->
  Σ ;;; Γ ⊢E ty ≤ ty' ->
  #|args| = #|tags| ->
  PCUICAritiesEta.typing_spineE Σ Γ ty' args T ->
  Σ ;;; Γ ⊢E res ≤ T.
Proof.
  induction tags as [|t tags ih] in args, ty, ty' |- *; intros hty hle hlen hsp.
  - destruct args as [|x args]; [|cbn in hlen; lia].
    cbn in hty. noconf hty. depelim hsp. etransitivity; tea.
  - cbn in hty.
    destruct (PCUICPrimOpType.prim_tag_type r t) as [a|] eqn:ht; [|discriminate hty].
    destruct (PCUICPrimOpType.prim_arg_types r tags res) as [rest|] eqn:hrest;
      [|discriminate hty].
    cbn in hty. noconf hty.
    destruct args as [|x args]; [cbn in hlen; lia|].
    depelim hsp.
    assert (hP : Σ ;;; Γ ⊢E tImpl a rest ≤ tProd na A B) by (etransitivity; tea).
    unfold tImpl in hP.
    eapply ws_cumul_pbE_Prod_Prod_inv in hP as [_ hdom hcod].
    eapply substitution0_ws_cumul_pbE in hcod; [|exact (subject_is_open_termE t0)].
    unfold subst1 in hcod. rewrite simpl_subst_k in hcod; [reflexivity|].
    exact (ih args rest (B {0 := x}) eq_refl hcod ltac:(cbn in hlen; lia) hsp).
Qed.

(** Base [prim_app_saturated_not_prod] ([PCUICSafeReduce.v:129]). *)
Lemma prim_app_saturated_not_prodE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ c u op args na A B} :
  prim_op_of Σ c = Some op -> #|args| = arity op ->
  Σ ;;; Γ |-E mkApps (tConst c u) args : tProd na A B -> False.
Proof.
  intros hop hlen ht.
  pose proof (validityE ht) as isT.
  eapply inversion_mkApps_directE in ht as (A0 & s & hc & _ & hsp); tea.
  eapply inversion_ConstE in hc as (decl & wfΓ & hdecl & cu & hle); tea.
  destruct (dsc_prim_op_head_typeE wfΓ hdecl cu hop hle) as (res & Tp & [hsh hTp hTA hres _]).
  pose proof (typing_spine_prim_args_satE Tp A0 hTp hTA hlen hsp) as hcum.
  destruct (po_shape (info op)) eqn:hshape; cbn in hsh, hres.
  - (* SInt: the result is the int type constant, a bodiless non-operation *)
    destruct hres as (kn & d & [hpc hdecl' hinv]).
    unfold PCUICPrimOpType.prim_tag_type, EnvironmentTyping.retro_type_constant in hsh.
    cbn in hpc. rewrite hpc in hsh. cbn in hsh. noconf hsh.
    destruct hinv as [_ hbody _].
    pose proof wfΣ as (_ & wfr & _).
    assert (hnop : prim_op_of Σ kn = None)
      by exact (prim_op_of_primitive_constant Σ primInt kn wfr hpc).
    exact (invert_cumul_axiom_prodE (args := []) hdecl' hbody hnop hcum).
  - (* SBool: the result is the registered inductive *)
    destruct (Retroknowledge.retro_bool _) as [ind|]; cbn in hsh; noconf hsh.
    exact (invert_cumul_ind_prodE (args := []) hcum).
Qed.

(** Base [prim_app_overapplied_ill_typed] ([PCUICSafeReduce.v:161]): row 47's statement, at
    [welltypedE]. *)
Lemma prim_app_overapplied_ill_typedE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ c u op args} :
  prim_op_of Σ c = Some op -> arity op < #|args| ->
  welltypedE Σ Γ (mkApps (tConst c u) args) -> False.
Proof.
  intros hop hlt [T ht].
  rewrite <- (firstn_skipn (arity op) args), mkApps_app in ht.
  destruct (skipn (arity op) args) as [|x more] eqn:hsk.
  { apply (f_equal (@length _)) in hsk. rewrite length_skipn in hsk. cbn in hsk. lia. }
  cbn in ht.
  eapply inversion_mkAppsE in ht as (A & htapp & _); tea.
  eapply inversion_AppE in htapp as (na & A' & B' & hf & _); tea.
  eapply prim_app_saturated_not_prodE; [exact hop| |exact hf].
  rewrite length_firstn. lia.
Qed.
