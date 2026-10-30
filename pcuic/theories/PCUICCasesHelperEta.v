(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun.
Set Warnings "-notation-overridden".
From MetaRocq.Utils Require Import utils monad_utils.
Set Warnings "notation-overridden".
From MetaRocq.Common Require Import config.

From MetaRocq.PCUIC Require Import PCUICTyping PCUICArities PCUICInductives PCUICSpine
  PCUICWeakeningTyp PCUICUnivSubstitutionConv PCUICValidity PCUICGeneration
  PCUICAst PCUICPrimitive PCUICCases PCUICProgram
  PCUICSubstitution PCUICConversion PCUICInductiveInversion
  PCUICContextSubst PCUICOnFreeVars PCUICSR PCUICTactics PCUICClosed
  PCUICCasesHelper.

From MetaRocq.PCUIC Require Import PCUICClosedBodies PCUICCumulativitySpecEta
  PCUICEtaJoinSpec PCUICWellScopedCumulativityEta PCUICWsCumulEtaCtxTyp
  PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions
  PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICInversionEta
  PCUICSREtaConv PCUICSpineEta PCUICInductivesEta
  PCUICInductiveInversionEta PCUICInductiveInversionEtaB PCUICValidityEta.
From MetaRocq.PCUIC.Typing Require Import PCUICClosedTypEta PCUICWeakeningTypEta
  PCUICWeakeningEnvTypEta PCUICUnivSubstitutionTypEta.
(* The NON-canonical [typing_spineE] lives here (C2); the import guard allows a plain
   [Require] only, and every use below is written qualified. *)
Require MetaRocq.PCUIC.PCUICGenerationEta.

From Equations Require Import Equations.

(** * Case-construction helpers over [typingE]

  The E copy of [PCUICCasesHelper]. Each declaration of the base file that mentions typing,
  [wf_local], [wf], [wf_ext], [isType], [type_local_ctx], [spine_subst] or the specification
  relation is copied; its E name is the base name with the suffix [E], and its statement is the
  base statement with only the relations renamed: [typing] → [typingE], [wf_local] →
  [wf_localE], [wf] → [wfE], [wf_ext] → [wf_extE], [isType] → [isTypeE], [spine_subst] →
  [spine_substE], [lift_typing typing] → [lift_typing typingE], and base's specification
  conversion [Σ ;;; Γ |- t =s u] ([convSpec]) → [convSpecE Σ Γ t u]. Reduction ([red]),
  closedness, scoping and every syntactic notion are unchanged. Implicit status, binder names
  and positions are base's, and so are the section structure and the [Proof using] annotations.

  Not copied, because they mention none of those relations (they are used from base, which this
  file imports): [make_case_pred], [make_br], [make_case], the tactic [let_to_set],
  [forget_types_inst_case_context], [map_lift_map_lift], [inddecl_name], [indpred_ctx],
  [case_branch_context], [instantiate_cstr_indices], [case_branch_type_only_gen],
  [case_branch_type_only], [case_branch_type_gen_split], [case_branch_type_split],
  [case_branch_type_subst_gen], [case_branch_type_subst], [pre_case_branch_context_gen_length]
  and [case_branch_context_unfold].

  Proof routes that differ from base (the statements are twins):

  - [AritiesToGeneration_typing_spineE]: base turns the algorithmic comparison of
    [PCUICArities.typing_spine] into the specification one of [PCUICGeneration.typing_spine] with
    [PCUICConversion.cumulAlgo_cumulSpec]. Over η that bridge is [ws_cumul_pbE_forget_spec]
    (the canonical join's specification bridge, [PCUICWellScopedCumulativityEta]), which carries
    [ClosedBodies Σ]; the E statement therefore adds exactly that premise (the ClosedBodies
    register's class, [NOT TWIN (ADDED ClosedBodies)]).

  - [case_branch_type_betaE] and [case_branch_type_conv_betaE]: base's [red_betas] and
    [conv_betas] take [wf Σ]; the E forms [red_betas_cb] and [conv_betasE]
    ([PCUICWsCumulEtaCtxTyp]) take [ClosedBodies Σ], supplied here from the statement's own
    [wfE Σ] through [wfE_ClosedBodies]. [case_branch_type_conv_betaE] ends on
    [ws_cumul_pbE_forget_spec] where base's [conv_betas] already produces the specification.

  - [type_Case_subst_helperE] and [type_Case_simple_subst_helperE]: base reduces the β-redex of
    the motive and carries the typing along it with [PCUICSR.subject_reduction]. Subject
    reduction over [typingE] is row T1 and is not on this tree, so the two typings are built by
    SUBSTITUTION instead, through the file's own [type_betasE]: the spine of a typed β-redex is
    a [ctx_instE] ([inversion_mkAppsE], [inversion_it_mkLambda_or_LetInE],
    [typing_spine_strengthenE], [typing_spine_ctx_instE]), hence a [subsletE]
    ([ctx_inst_spine_substE]), and [substitutionE] types the contractum at the substituted type.
    [type_betasE] needs no subject reduction and no new axiom, and it gives the SAME sort as the
    redex, which base's route also gives. The reductions and the conversions of both proofs are
    base's ([red_betas_cb], [conv_betasE]). *)

Lemma weakening0E {cf : checker_flags} Σ Γ t T :
  wfE Σ.1 -> wf_localE Σ Γ ->
  Σ ;;; [] |-E t : T -> Σ ;;; Γ |-E lift0 #|Γ| t : lift0 #|Γ| T.
Proof.
  rewrite -{1 2}[Γ]app_context_nil_l; apply: weakeningE.
Qed.

Arguments weakening0E {_ _} _ {_ _ _ _} _.


(* Unused *)
Lemma weakening_type_local_ctxE {cf:checker_flags} Σ Γ Δ Δ' ctxs :
  wfE Σ.1 ->
  wf_localE Σ (Γ ,,, Δ) ->
  type_local_ctx (PCUICTyping.lift_typing typingE) Σ Γ Δ' ctxs ->
  type_local_ctx (PCUICTyping.lift_typing typingE) Σ (Γ ,,, Δ) (lift_context #|Δ| 0 Δ') ctxs.
Proof.
  induction Δ'; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + simpl; rewrite PCUICLiftSubst.lift_context_snoc /= Nat.add_0_r;
    split; tas.
    apply lift_typing_f_impl with (1 := b0) => // ?? Hs.
    now eapply weakening_typingE in Hs.
  + rewrite PCUICLiftSubst.lift_context_snoc /= Nat.add_0_r.
    split; tas.
    apply lift_typing_f_impl with (1 := b) => // ?? Hs.
    now eapply weakening_typingE in Hs.
Qed.

Lemma wf_local_expand_lets0E {cf : checker_flags} {Σ : global_env_ext} :
  wfE Σ ->
  forall Δ Γ : context,
  wf_localE Σ (Δ,,, Γ) ->
  wf_localE Σ (smash_context [] Δ,,, expand_lets_ctx Δ Γ).
Proof.
  move=> ? Δ ?.
  rewrite -{1}[Δ]app_context_nil_l -{1}[smash_context _ _]app_context_nil_l.
  apply: wf_local_expand_letsE.
Qed.


Section WithCheckerFlagsE.
  Context `{cf : checker_flags}.

  Lemma AritiesToGeneration_typing_spineE (Σ : global_env_ext) {cbΣ : ClosedBodies Σ} Δ T s U :
    PCUICAritiesEta.typing_spineE Σ Δ T s U ->
    PCUICGenerationEta.typing_spineE Σ Δ T s U.
  Proof using cf.
    move=> z; depind z; econstructor=> //; try eassumption.
    all: by apply: ws_cumul_pbE_forget_spec.
  Qed.

  Lemma isType_liftE {Σ : global_env_ext} {n Γ Δ ty}
    (isdecl : n <= #|Γ|):
    wfE Σ -> wf_localE Σ (Γ ,,, lift_context n 0 Δ) ->
    isTypeE Σ (skipn n Γ ,,, Δ) ty ->
    isTypeE Σ (Γ,,, lift_context n 0 Δ) (PCUICAst.lift n #|Δ| ty).
  Proof using cf.
    intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
    assert (n = #|firstn n Γ|).
    { rewrite firstn_length_le; auto with arith. }
    apply lift_typing_f_impl with (1 := wfty) => // ?? Hs.
    rewrite {3 4 5}H.
    eapply (weakening_typingE (Γ := skipn n Γ) (Γ' := Δ) (Γ'' := firstn n Γ));
      eauto with wf.
  Qed.


End WithCheckerFlagsE.



Section CaseDefinitionsE.
  Context
    `{cf : checker_flags}
    (ind : inductive)
    (mib : mutual_inductive_body)
    (oib : one_inductive_body)
    (pparams : list term)
    (puinst : Instance.t).

  Lemma pre_case_predicate_context_gen_indpred_ctxE Σ Γ :
    spine_substE Σ Γ pparams (List.rev pparams) (smash_context [] (ind_params mib)@[puinst]) ->
    consistent_instance_ext Σ (ind_universes mib) puinst ->
    pre_case_predicate_context_gen ind mib oib pparams puinst =
    indpred_ctx ind mib oib pparams puinst.
  Proof using cf.
    move=> pparamssubst ?.
    rewrite /pre_case_predicate_context_gen /ind_predicate_context /indpred_ctx /inst_case_context.
    rewrite PCUICUnivSubst.subst_instance_cons subst_context_snoc. f_equal.
    rewrite /vass /inddecl_name subst_instance_length expand_lets_ctx_length.
    rewrite {1}/subst_instance /= /subst_decl /map_decl /=; f_equal.
    rewrite PCUICUnivSubst.subst_instance_mkApps PCUICLiftSubst.subst_mkApps.
    f_equal => /=; first (f_equal; apply: subst_instance_id_mdecl; eassumption).
    rewrite PCUICUnivSubst.map_subst_instance_to_extended_list_k.
    rewrite PCUICContexts.to_extended_list_k_app.
    rewrite map_app; f_equal.
    - rewrite expand_lets_ctx_length Nat.add_0_r.
      rewrite -{2}[#|_|]Nat.add_0_r PCUICLiftSubst.lift_to_extended_list_k List.map_map.
      erewrite MRList.map_ext; last (move=> ?; rewrite subst_lift_subst; reflexivity).
      rewrite -List.map_map; f_equal.
      rewrite -(PCUICLiftSubst.map_subst_instance_to_extended_list_k puinst) subst_instance_smash.
      apply: spine_subst_subst_to_extended_list_kE; eassumption.
    - rewrite -PCUICSubstitution.to_extended_list_k_map_subst ?expand_lets_ctx_length //.
      rewrite to_extended_list_k_expand_lets //.
  Qed.



End CaseDefinitionsE.



(************************************************)
(* Beta-reduction of match's motive in branches *)
(************************************************)

Section CaseBranchTypeBetaE.
  Context `{cf : checker_flags}.

  Lemma case_branch_type_betaE (Σ : global_env_ext) Γ ind mib params puinst predctx rettyp i cb :
    wfE Σ ->
    closedn #|Γ ,,, predctx| rettyp ->
    closed_ctx (Γ ,,, predctx) ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in
    closed_ctx (Γ ,,, cstr_ctx) ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    PCUICReduction.red Σ.1 (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ clret clpred clcstr indxseq.
    apply: (red_betas_cb Σ (@wfE_ClosedBodies _ Σ.1 wfΣ));
      first (rewrite /instantiate_cstr_indices /Δ; by len).
    - have -> : #|Γ ,,, cstr_ctx ,,, Δ| = #|Γ ,,, predctx| + #|cstr_args cb|
      by rewrite /Δ !length_app /cstr_ctx /pre_case_branch_context_gen; len; lia.
      by apply: PCUICClosed.closedn_lift.
    - rewrite PCUICClosed.closedn_ctx_app clcstr /= /Δ length_app.
      have -> : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len; lia.
      apply: PCUICClosed.closedn_ctx_lift.
      by apply: closed_ctx_app.
  Qed.


  Lemma case_branch_type_conv_betaE (Σ : global_env_ext) Γ ind mib oib params puinst predctx rettyp i cb :
    wfE Σ ->
    closedn #|Γ ,,, predctx| rettyp ->
    closed_ctx (Γ ,,, predctx) ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in
    closed_ctx (Γ ,,, cstr_ctx) ->
    forallb (closedn #|Γ|) params ->
    #|params| = ind_npars mib ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    declared_inductive Σ ind mib oib ->
    declared_constructor Σ (ind,i) mib oib cb ->
    convSpecE Σ (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ clret clpred clcstr clpar pareq indxseq declind declctor.
    pose proof (declmind := MRProd.proj1 declind).
    have eqcstrctx : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len; lia.
    apply: (conv_betasE Σ (@wfE_ClosedBodies _ Σ.1 wfΣ)).
    - have -> : #|Γ ,,, cstr_ctx ,,, Δ| = #|Γ ,,, predctx| + #|cstr_args cb|
      by rewrite /Δ !length_app eqcstrctx; len; lia.
      by apply: PCUICClosed.closedn_lift.
    - rewrite PCUICClosed.closedn_ctx_app clcstr /= /Δ length_app eqcstrctx.
      apply: PCUICClosed.closedn_ctx_lift.
      by apply: closed_ctx_app.
    - rewrite forallb_app; apply/andP; split.
      + rewrite /instantiate_cstr_indices !forallb_map.
        apply: All_forallb.
        apply: All_impl; first (apply: on_constructor_closed_indicesE; eassumption).
        move=> x /=.
        rewrite -PCUICClosedTyp.is_open_term_closed eqcstrctx !length_app=> clx.
        rewrite Nat.add_comm.
        apply: PCUICClosed.closedn_subst; first by rewrite forallb_rev.
        set G := (_ @[_]). have -> : #|List.rev params| = context_assumptions G.
        1: by rewrite /G context_assumptions_subst_instance -(declared_minductive_ind_nparsE declmind) List.length_rev.
        rewrite PCUICClosed.closedn_expand_lets_eq {}/G.
        1:{
          rewrite PCUICClosed.closedn_subst_instance_context.
          apply: (PCUICClosed.closedn_ctx_upwards 0); last lia.
          apply: declared_inductive_closed_paramsE declind.
        }
        rewrite subst_instance_length -Nat.add_assoc [X in _ + X]Nat.add_comm.
        apply: PCUICClosed.closedn_subst.
        1:{
          apply: forallb_impl; last apply: PCUICClosed.closed_inds.
          move=> ???; apply: PCUICLiftSubst.closed_upwards; first eassumption; lia.
        }
        rewrite inds_length PCUICClosed.closedn_subst_instance.
        apply: PCUICLiftSubst.closed_upwards; first eassumption.
        rewrite arities_context_length eqcstrctx; lia.
      + rewrite /= andb_true_r PCUICClosed.closedn_mkApps /= forallb_app ; apply/andP; split.
        * rewrite forallb_map. apply: forallb_impl; last eassumption.
          move=> x _ clx; rewrite length_app eqcstrctx Nat.add_comm.
          by apply: PCUICClosed.closedn_lift.
        * apply: forallb_impl; last apply: PCUICClosed.closedn_to_extended_list.
          move=> ? _ ?; apply: PCUICLiftSubst.closed_upwards; first eassumption.
          rewrite length_app eqcstrctx ; lia.
    - rewrite /Δ /instantiate_cstr_indices; by len.
  Qed.


  Lemma case_branch_type_beta_typedE (Σ : global_env_ext) Γ ind mib params puinst predctx rettyp i cb :
    wfE Σ ->
    isTypeE Σ (Γ ,,, predctx) rettyp ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in
    wf_localE Σ (Γ,,, cstr_ctx) ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    PCUICReduction.red Σ.1 (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ retWty wfcstr_ctx ?. destruct retWty as (_ & ps & retWty & _).
    apply: (red_betas_typedE Σ wfΣ);
      first by rewrite /Δ /instantiate_cstr_indices; len; lia.
    rewrite /Δ; have -> : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len.
    apply: weakening_typingE; eassumption.
  Qed.

End CaseBranchTypeBetaE.


(*****************)
(* Random lemmas *)
(*****************)

Section RandomLemmasE.
  Context `{cf: checker_flags}.


  Lemma cstr_indices_lengthE {Σ} {wfΣ : wfE Σ} {ind mib oib cb} :
    declared_constructor Σ ind mib oib cb ->
    #|cstr_indices cb| = context_assumptions (ind_indices oib).
  Proof using cf.
    move=> declctor.
    unshelve epose proof (X := on_declared_constructorE declctor).
    move: X => [] _ [] ? [_] /on_cindices /ctx_inst_length.
    rewrite context_assumptions_rev context_assumptions_lift; apply.
  Qed.

  Lemma isType_mkApps_Ind_inv_spineE
    (ind : inductive)
    (mib : mutual_inductive_body)
    (oib : one_inductive_body)
    (pparams : list term)
    (puinst : Instance.t)
    (indices : list term)
    (Σ : global_env_ext) Γ :
    wf_extE Σ ->
    declared_inductive Σ ind mib oib ->
    #|pparams| = ind_npars mib ->
    isTypeE Σ Γ (mkApps (tInd ind puinst) (pparams ++ indices)) ->
    ∑ s, spine_substE Σ Γ (pparams ++ indices) s (ind_params mib,,, ind_indices oib)@[puinst].
  Proof using cf.
    move=> wfΣ inddecl pparamslen discrtypok.
    have Γwf : wf_localE Σ Γ by apply: (typingE_wf_local discrtypok.2.π2.1).
    have wfΣ1 := (fst wfΣ : wfE Σ.1).
    move: (inddecl)=> /(@on_declared_inductiveE _ Σ.1 _ _ _ wfΣ1) [on_ind on_body].
    have wfΣwk := declared_inductive_wf_ext_wkE _ _ _ wfΣ1 (MRProd.proj1 inddecl).

    move: (discrtypok)=> /(isType_mkApps_Ind_invE wfΣ1 inddecl Γwf).
    rewrite firstn_app_left // skipn_all_app_eq //.
    move=> [parsubst [indxsubst]].
    match goal with [|- ?t -> _] => let_to_set t end.
    move=> [sspparams ssindices _ indiceslen puinstok].

    exists (indxsubst ++ parsubst).

    rewrite subst_instance_app_ctx.
    have indxsubstlen : #|(ind_indices oib)@[puinst]| = #|indxsubst|.
    {
      rewrite -(subst_context_length parsubst 0 _).
      symmetry. apply: subslet_lengthE.
      exact (ssindices.(inst_subsletE)).
    }
    apply: spine_subst_appE.
    * rewrite pparamslen context_assumptions_subst_instance.
      apply: declared_minductive_ind_nparsE; exact: MRProd.proj1 inddecl.
    * rewrite -app_context_assoc-subst_instance_app_ctx; apply: PCUICWeakeningTypEta.weaken_wf_localE=> //.
      set (Δ := _ ,,, _). destruct Σ as [Σ1 Σ2].
      refine (PCUICUnivSubstitutionTypEta.typing_subst_instance_wf_localE Σ1 Σ2 Δ puinst (ind_universes mib) _ _ _)=> //.
      destruct (onArityRed on_body) as (_ & s & lind & _). move: lind => /=.
      move=> /type_it_mkProd_or_LetIn_invE [uparams [? [slparams + _ _]]].
      move=> /type_it_mkProd_or_LetIn_invE [uindxs [? [slindxs + _ _]]].
      move=> indsortTyp.
      pose proof (h := typingE_wf_local indsortTyp); move: h.
      rewrite app_context_nil_l //.
    * rewrite skipn_all_app_eq //.
    * rewrite firstn_app_left // skipn_all_app_eq //.
  Qed.

End RandomLemmasE.


(** The typed β-contraction of a spine, WITHOUT subject reduction.

    Base's [PCUICCasesHelper] carries the typing of [mkApps (it_mkLambda_or_LetIn Δ t) l]
    along the reduction of [red_betas] with [PCUICSR.subject_reduction]. Subject reduction
    over [typingE] is not on this tree, so the contractum is typed by SUBSTITUTION: the
    application's own typing gives a [typing_spineE] from the motive's type, hence (through
    [inversion_it_mkLambda_or_LetInE] and [typing_spine_strengthenE], which move the spine onto
    [it_mkProd_or_LetIn Δ _]) a [ctx_instE] over [List.rev Δ], hence a [subsletE]; the
    conclusion is then [substitutionE] on the GIVEN typing of [t]. The resulting type is
    [subst0 (mk_ctx_subst Δ l) T], which at [T = tSort ps] is [tSort ps] itself, so no sort is
    lost where base's route keeps one. *)
Lemma type_betasE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ l t T U} :
  #|l| = context_assumptions Δ ->
  Σ ;;; Γ ,,, Δ |-E t : T ->
  Σ ;;; Γ |-E mkApps (it_mkLambda_or_LetIn Δ t) l : U ->
  Σ ;;; Γ |-E subst0 (mk_ctx_subst Δ l) t : subst0 (mk_ctx_subst Δ l) T.
Proof.
  move=> hl tty happ.
  destruct (inversion_mkAppsE happ) as [A [hf sp]].
  destruct (inversion_it_mkLambda_or_LetInE Σ wfΣ hf) as [B [tB le]].
  have wfΓΔ : wf_localE Σ (Γ ,,, Δ) by apply: (typingE_wf_local tty).
  have iT : isTypeE Σ Γ (it_mkProd_or_LetIn Δ B).
  { apply: validityE. exact: (PCUICGenerationEta.type_it_mkLambda_or_LetInE _ _ _ _ _ tB). }
  have sp' := typing_spine_strengthenE (wfΣ := wfΣ) sp _ iT le.
  rewrite -(app_nil_r l) in sp'.
  destruct (typing_spine_ctx_instE (wfΣ := wfΣ) hl sp') as [ci _].
  have ss := ctx_inst_spine_substE (wfΣ := wfΣ) wfΓΔ ci.
  rewrite (mk_ctx_subst_spec'E ci).
  exact: (substitutionE (wfΣ := wfΣ) (Δ := []) (inst_subsletE ss) tty).
Qed.


Lemma type_Case_helperE
  `{cf : checker_flags}
  (ind : inductive)
  (mib : mutual_inductive_body)
  (oib : one_inductive_body)
  (pparams : list term)
  (puinst : Instance.t)
  (discr : term)
  (rettyp : term)
  (brs : list term)
  (indices : list term)
  (ps : Universes.sort) (Σ : global_env_ext) Γ :
  wf_extE Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->

  Σ;;; Γ |-E discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let predctx := case_predicate_context ind mib oib p in


  (wf_localE Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |-E preturn p : tSort ps) ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->
  isSortRel ps oib.(ind_relevance) ->

  (isCoFinite (ind_finite mib) ==> on_free_vars (strengthenP 0 1 xpredT) rettyp) = true ->

  #|brs| = #|ind_ctors oib| ->

  let ptm := it_mkLambda_or_LetIn predctx rettyp in

  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctxty := case_branch_type ind mib oib p br ptm i cdecl in
        wf_localE Σ (Γ,,, brctxty.1) ->
        typingE Σ (Γ,,, brctxty.1) brctxty.2 (tSort ps) ->
        typingE Σ (Γ,,, brctxty.1) (bbody br) brctxty.2
    )
    0 (ind_ctors oib) brs ->

  let subst_rettyp := mkApps ptm (indices ++ [discr]) in

  Σ ;;; Γ |-E make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp p predctx ptyp pselimok Her isfinite brslen ptm brstyp srettyp.
  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (fst wfΣ : wfE Σ.1).
  have Γwf : wf_localE Σ Γ by apply: (typingE_wf_local discrtyp).

  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply PCUICEquality.eq_context_upto_names_binder_annot; reflexivity.
  }

  pose proof (discrtypok := validityE discrtyp).

  have predctxwf : wf_localE Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_contextE=> //=; eassumption.

  specialize (ptyp predctxwf).

  have puinstok : consistent_instance_ext Σ (ind_universes mib) puinst.
  by move: (discrtypok)=> /(isType_mkApps_Ind_invE wfΣ1 inddecl Γwf) [? [?] [?? _ ?]]//.

  have [s ssparamsindxs] : ∑ s, spine_substE Σ Γ (pparams ++ indices) s
                        (ind_params mib,,, ind_indices oib)@[puinst]
  by (apply: isType_mkApps_Ind_inv_spineE => //; eassumption).

  apply: typeE_Case=> //.
  - apply: ptyp.
  - rewrite -/ci -/predctx. constructor=> //=; first reflexivity.
    apply: (spine_subst_ctx_instE ssparamsindxs).
  - have wfbrs : wf_branches oib (MRList.map2 (make_br ind mib) (ind_ctors oib) brs).
    {
      rewrite /wf_branches.
      elim: (ind_ctors oib) {brstyp}brs brslen=> [|decl ctors ih] //= [|br brs] //=.
      move=> [=] /ih h; constructor=> // {h}.
      hnf=>/=.
      rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
      rewrite /subst_context /lift_context !forget_types_fold_context_k.
      apply PCUICEquality.eq_context_upto_names_binder_annot. reflexivity.
    }

    constructor=> //.

    apply: All2i_map2_right.
    rewrite -/ci -/p -/ptm -/predctx.
    apply Forall2_All2 in wfbrs.
    apply All2_map2_right_inv in wfbrs=> //.
    pose proof (declctors := declared_ind_declared_constructors inddecl).
    epose proof (alls := All2i_All2_mix_left wfbrs (All2i_Alli_mix_left declctors brstyp)).

    apply: (All2i_impl alls) => i x y.

    move=> [wfbr [declctor]].
    set (br := make_br _ _ _  _). rewrite -/br in wfbr.
    set (brctxty := case_branch_type _ _ _ _ _ _ _ _).

    move=> bodytyp.
    split; first (apply: All2_refl; reflexivity).
    unshelve epose proof (X := wf_case_branch_typeE (Γ:=Γ)(p:=p) (ci:=ci) ps indices inddecl discrtypok wfpredp ptyp _ i x br declctor wfbr).
    1: reflexivity.
    move: X=> [] *. split=> //. split=> //.
    apply: bodytyp=> //.
Qed.



Lemma type_Case_subst_helperE
  `{cf : checker_flags}
  (ind : inductive)
  (mib : mutual_inductive_body)
  (oib : one_inductive_body)
  (pparams : list term)
  (puinst : Instance.t)
  (discr : term)
  (rettyp : term)
  (brs : list term)
  (indices : list term)
  (ps : Universes.sort) (Σ : global_env_ext) Γ :
  wf_extE Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->

  Σ;;; Γ |-E discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let predctx := case_predicate_context ind mib oib p in


  (wf_localE Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |-E preturn p : tSort ps) ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->
  isSortRel ps oib.(ind_relevance) ->

  (isCoFinite (ind_finite mib) ==> on_free_vars (strengthenP 0 1 xpredT) rettyp) = true ->

  #|brs| = #|ind_ctors oib| ->


  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctx := PCUICCasesHelper.case_branch_context ind mib p br cdecl in
      let brty := case_branch_type_subst ind mib p predctx rettyp i cdecl in
      wf_localE Σ (Γ,,, brctx) ->
      typingE Σ (Γ,,, brctx) brty (tSort ps) ->
      typingE Σ (Γ,,, brctx) (bbody br) brty
    )
    0 (ind_ctors oib) brs ->

  let subst_rettyp := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp in

  Σ ;;; Γ |-E make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp p predctx predWty elimok Her finok brslen brsok substrettyp.

  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (fst wfΣ : wfE Σ.1).
  have Γwf : wf_localE Σ Γ by apply: (typingE_wf_local discrtyp).

  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply PCUICEquality.eq_context_upto_names_binder_annot; reflexivity.
  }


  pose proof (discrtypok := validityE discrtyp).

  have predctxwf : wf_localE Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_contextE=> //=; eassumption.


  move: (discrtypok)=> /(isType_mkApps_Ind_invE wfΣ1 inddecl Γwf).
  rewrite firstn_app_left // skipn_all_app_eq //.
  move=> [parsubst [indxsubst]].
  move=> [sspparams ssindices _ indiceslen puinstok].

  set ptm := it_mkLambda_or_LetIn predctx rettyp.
  set redex_rettyp := mkApps ptm (indices ++ [discr]).


  have ?: closedn #|Γ,,, predctx| rettyp
  by apply: subject_closedE; exact: (predWty predctxwf).
  have ?: closed_ctx (Γ,,, predctx)
  by apply: closed_wf_localE; exact: predctxwf.

  have mk_caseWtyp : Σ;;; Γ |-E make_case ind mib oib pparams puinst discr rettyp brs : redex_rettyp.
  {
    apply: type_Case_helperE=> //; try eassumption.
    pose proof (declctors := declared_ind_declared_constructors inddecl).
    apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br.
    rewrite case_branch_type_split.
    set brctx := (x in (x, _)).
    set brty := (x in (_, x)).
    move=> /= wf wfty.

    have ?: closed_ctx (Γ,,, pre_case_branch_context_gen ind mib x pparams puinst)
    by apply: closed_wf_localE; rewrite -(case_branch_context_unfold _ _ oib _ _ rettyp _ t).

    have ?: #|cstr_indices x| + 1 = context_assumptions predctx.
    {
      rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
      rewrite (cstr_indices_lengthE declctor); len.
    }

    econstructor; try eassumption.
    + apply: (h wf).
      (* Base reduces [brty] along [case_branch_type_beta] and keeps the typing with
         subject reduction; here the contractum is typed by substitution. *)
      rewrite /brty /case_branch_type_only /case_branch_type_only_gen in wfty.
      rewrite /case_branch_type_subst /case_branch_type_subst_gen.
      rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r in wfty.
      rewrite /brctx case_branch_context_unfold in wf wfty |- *.
      have hlen : #|instantiate_cstr_indices ind mib pparams puinst x
                    ++ [mkApps (tConstruct ind i puinst)
                          (ListDef.map (lift0 #|cstr_args x|) pparams ++ to_extended_list (cstr_args x))]|
                  = context_assumptions (lift_context #|cstr_args x| 0 predctx)
      by rewrite /instantiate_cstr_indices; len.
      have hΔ : #|cstr_args x| = #|pre_case_branch_context_gen ind mib x pparams puinst|
      by rewrite /pre_case_branch_context_gen; len.
      have wrettyp : Σ ;;; (Γ ,,, pre_case_branch_context_gen ind mib x pparams puinst)
                       ,,, lift_context #|cstr_args x| 0 predctx
                     |-E PCUICAst.lift #|cstr_args x| #|predctx| rettyp : tSort ps.
      { have hh := @weakening_typingE _ Σ wfΣ1 Γ predctx
                     (pre_case_branch_context_gen ind mib x pparams puinst) rettyp (tSort ps)
                     wf (predWty predctxwf).
        rewrite -hΔ in hh. exact hh. }
      have wfty' : Σ ;;; Γ ,,, pre_case_branch_context_gen ind mib x pparams puinst
        |-E mkApps (it_mkLambda_or_LetIn (lift_context #|cstr_args x| 0 predctx)
                      (PCUICAst.lift #|cstr_args x| #|predctx| rettyp))
              (instantiate_cstr_indices ind mib pparams puinst x
               ++ [mkApps (tConstruct ind i puinst)
                     (ListDef.map (lift0 #|cstr_args x|) pparams ++ to_extended_list (cstr_args x))])
            : tSort ps := wfty.
      exact (type_betasE (U := tSort ps) hlen wrettyp wfty').
    + apply: cumulE_Sym.
      rewrite /brctx case_branch_context_unfold.
      apply: case_branch_type_conv_betaE=> //; try eassumption.
      exact: closed_spine_subst_instE sspparams.
  }


  specialize (predWty predctxwf).

  have hindlen : #|indices ++ [discr]| = context_assumptions predctx.
  by len; rewrite indiceslen /predctx PCUICCasesContexts.inst_case_predicate_context_eq;
     first reflexivity; len.

  have red_rettyp : PCUICReduction.red Σ.1 Γ redex_rettyp substrettyp
  by apply: (red_betas_cb Σ (@wfE_ClosedBodies _ Σ.1 wfΣ1))=> //.

  econstructor.
  1: exact: mk_caseWtyp.
  - (* [isTypeE] of the contractum, by substitution instead of subject reduction *)
    have hU := (validityE (wfΣ := wfΣ1) mk_caseWtyp).2.π2.1.
    exact (type_betasE (U := tSort _) hindlen predWty hU).
  - apply: convSpecE_cumulSpecE.
    apply: (conv_betasE Σ (@wfE_ClosedBodies _ Σ.1 wfΣ1))=> //.
    rewrite forallb_app /= (subject_closedE discrtyp) !andb_true_r.
    apply: closed_spine_subst_instE ssindices.
Qed.

Lemma type_Case_simple_subst_helperE
  `{cf : checker_flags}
  (ind : inductive)
  (mib : mutual_inductive_body)
  (oib : one_inductive_body)
  (pparams : list term)
  (puinst : Instance.t)
  (discr : term)
  (rettyp : term)
  (brs : list term)
  (indices : list term)
  (ps : Universes.sort) (Σ : global_env_ext) Γ :
  wf_extE Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->

  Σ;;; Γ |-E discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let rettyp' := lift0 (Datatypes.S #|ind_indices oib|) rettyp in

  let p := make_case_pred ind mib oib pparams puinst rettyp' in
  let predctx := case_predicate_context ind mib oib p in


  Σ ;;; Γ |-E rettyp : tSort ps ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->
  isSortRel ps oib.(ind_relevance) ->

  #|brs| = #|ind_ctors oib| ->


  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctx := PCUICCasesHelper.case_branch_context ind mib p br cdecl in
      let brty := lift0 #|brctx| rettyp in
      wf_localE Σ (Γ,,, brctx) ->
      typingE Σ (Γ,,, brctx) brty (tSort ps) ->
      typingE Σ (Γ,,, brctx) (bbody br) brty
    )
    0 (ind_ctors oib) brs ->


  Σ ;;; Γ |-E make_case ind mib oib pparams puinst discr rettyp' brs : rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp rettyp' p predctx predWty elimok Her brslen brsok.

  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (fst wfΣ : wfE Σ.1).
  have Γwf : wf_localE Σ Γ by apply: (typingE_wf_local discrtyp).

  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply PCUICEquality.eq_context_upto_names_binder_annot; reflexivity.
  }


  pose proof (discrtypok := validityE discrtyp).

  have predctxwf : wf_localE Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_contextE=> //=; eassumption.


  move: (discrtypok)=> /(isType_mkApps_Ind_invE wfΣ1 inddecl Γwf).
  rewrite firstn_app_left // skipn_all_app_eq //.
  move=> [parsubst [indxsubst]].
  move=> [sspparams ssindices _ indiceslen puinstok].

  have predctxlen : Datatypes.S #|ind_indices oib| = #|predctx|
  by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity; len.

  have ? : context_assumptions predctx = Datatypes.S #|indices|
  by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; try reflexivity; len.

  set subst_rettyp' := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp'.
  have -> : rettyp = subst_rettyp'.
  by rewrite /subst_rettyp' /rettyp' PCUICLiftSubst.simpl_subst_k // mk_ctx_subst_length //; len.

  (* [rettyp'] is lifted over the whole predicate context, so it does not mention the
     scrutinee. *)
  have finok : (isCoFinite (ind_finite mib) ==>
                on_free_vars (strengthenP 0 1 xpredT) rettyp') = true.
  { apply/implyP => _. rewrite /rettyp'. apply: on_free_vars_lift0.
    eapply on_free_vars_impl; last exact: (subject_is_open_termE predWty).
    move=> i _. change (strengthenP 0 1 xpredT (Datatypes.S #|ind_indices oib| + i)).
    rewrite strengthenP01. apply/negP => /Nat.eqb_eq. lia. }

  apply: type_Case_subst_helperE=> //; try eassumption.
  - rewrite -/predctx=> ? /=.
    have -> : tSort ps = lift0 (Datatypes.S #|ind_indices oib|) (tSort ps) by reflexivity.
    apply: weakening_genE=> //.
  - pose proof (declctors := declared_ind_declared_constructors inddecl).
    apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br brctx brty wfctx wfty.
    move: (h wfctx). rewrite -/brctx -/br.
    set brty' := (lift0 _ _).
    have <- : brty = brty'; last by apply.
    rewrite /brty' /brty /rettyp' /case_branch_type_subst /case_branch_type_subst_gen /=.
    rewrite -/predctx -predctxlen. set s := (_ ++ _).
    rewrite PCUICLiftSubst.simpl_lift. 1,2: lia.
    rewrite PCUICContexts.subst_lift_above.
    + rewrite mk_ctx_subst_length /s; len.
      rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
      rewrite (cstr_indices_lengthE declctor); len.
    + f_equal. rewrite /brctx case_branch_context_unfold; len.
Qed.
