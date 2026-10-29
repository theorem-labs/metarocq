(* Distributed under the terms of the MIT license. *)

(** * First-order values over [typingE] (row T6): the E copy of [PCUICFirstorder]

  The E twin of every declaration of base [PCUICFirstorder] whose statement mentions typing,
  conversion, [wf] or [isType]: [typing] → [typingE], [wf] → [wfE], [wf_local] → [wf_localE],
  [isType] → [isTypeE] ([PCUICTypingEtaNotions]), [PCUICArities.typing_spine] →
  [PCUICAritiesEta.typing_spineE] and [PCUICSpine.arity_spine] → [PCUICSpineEta.arity_spineE]
  (both written qualified: [PCUICGenerationEta.typing_spineE] and the statement file's
  [arity_spineE] exist too), [Σ ;;; Γ ⊢ A ≤ B] ([ws_cumul_pb]) → [Σ ;;; Γ ⊢E A ≤ B]
  ([ws_cumul_pbE]), [Σ ⊢ Γ = Δ] ([ws_cumul_ctx_pb Conv]) → [ws_cumul_ctx_pbE Conv Σ Γ Δ].
  [PCUICWcbvEval.value] and the syntactic notions are unchanged. Each name takes the suffix [E];
  constructors too ([firstorder_value_CE], [firstorder_spine_nilE], [firstorder_spine_consE]).

  Imported from base, not copied (they mention none of the relations and base's compiled forms
  take no environment premise): [plookup_env], [firstorder_type], [firstorder_con],
  [firstorder_oneind], [firstorder_mutind], [firstorder_ind], [firstorder_env'],
  [firstorder_env], [firstorder_lookup_inv], [isPropositional], [instantiated], [leb_spect],
  [nth_error_inds], [alli_subst_instance], [plookup_env_lookup_env], [fresh_global_app],
  [plookup_env_Some_not_fresh], and the [Arguments] settings of base's file.

  Copied although they mention no relation, because base's compiled forms take [wf Σ] and a
  [wfE] context cannot supply it: [firstorder_ind_propositionalE], [plookup_env_extendsE],
  [firstorder_mutind_extE].

  Not copied: base [invert_cumul_it_mkProd_or_LetIn_Sort_Ind] ([:605]). Its landed E form
  [PCUICEtaA6More.invert_cumul_it_mkProd_or_LetIn_Sort_IndE] (row x16) is stronger (any [pb],
  [ClosedBodies]); [firstorder_value_specE] uses it, written qualified, at [Cumul] with
  [wfE_ClosedBodies]. The base-twin form ([wfE], [Cumul]) is its corollary (checked by
  ascription of the derived term on integ1 @ [e3069684], 2026-10-29).

  ** Proof routes that differ from base (statements do not)

  - The zeta steps: base proves [Σ ;;; Γ ⊢ tLetIn na a A B ≤ B {0 := a}] through the
    specification ([cumulSpec_cumulAlgo_curry], [cumul_zeta]); here the zeta reduction is a
    [closed_red] and [red_ws_cumul_pbE_left] ([firstorder_spine_letE]), or
    [ws_cumul_pbE_LetIn_l_inv] ([typing_spine_arity_spineE]).
  - [typing_spine_arity_spineE], product case: base's [substitution0_ws_cumul_pb] takes a typing
    of the substituted term; the landed [substitution0_ws_cumul_pbE] takes its scoping, from that
    typing ([subject_is_open_termE]).

  ** The forecast block

  Section premise: T1's [SRForecastCopy18] ([Construct_Ind_ind_eqE],
  [declared_constructor_valid_tyE]; it enters through [invert_ind_indE],
  [invert_fix_indE] and [typing_cofix_coindE]), imported, never redefined. Copy 16 has landed
  (frac/eta 0fb43f10): T2a's, T1's, [PCUICClassificationEta]'s and this file's copy-16 classes
  ([FirstorderForecastCopy16]: [declared_inductive_type_ws_cumulE]) were deleted after a
  compiled-form identity check of each field, and [PCUICInductivesEta] is imported. [Print
  Assumptions] in [PCUICFirstorderEtaInstances] shows the class as an argument. *)

From Stdlib Require Import Program ssreflect ssrbool List.
From MetaRocq.Utils Require Import utils MRRelations.
From MetaRocq.Common Require Import config Kernames.

From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction
  PCUICReflect PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp
  PCUICContextConversionTyp
  PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion
  PCUICUnivSubstitutionTyp
  PCUICCumulativity PCUICSR PCUICSafeLemmata
  PCUICValidity PCUICPrincipality PCUICElimination
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICClassification.

From MetaRocq.PCUIC Require Import PCUICArities PCUICSpine.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.PCUIC Require Import PCUICEquality PCUICAlpha PCUICFirstorder.

From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningEnvTypEta
  PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
  PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICContextConversionEta PCUICWsCumulEtaCtx
  PCUICWsCumulEtaCtxTyp PCUICInversionEta PCUICSubstitutionEta PCUICContextsEta
  PCUICAritiesEta PCUICSpineEta PCUICWsCumulEtaInstancesGlobal PCUICInductivesEta PCUICValidityEta
  PCUICSREta PCUICClassificationEta.
From MetaRocq.PCUIC.Typing Require Import PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require PCUICGenerationEta.
From Equations.Type Require Import Relation.

Section cf.

Context {cf : config.checker_flags}.

(** Base [firstorder_value] ([:109]). *)
Inductive firstorder_valueE Σ Γ : term -> Prop :=
| firstorder_value_CE i n ui u args pandi :
   Σ ;;; Γ |-E mkApps (tConstruct i n ui) args :
   mkApps (tInd i u) pandi ->
   Forall (firstorder_valueE Σ Γ) args ->
   ~~ isPropositional Σ i ->
   firstorder_valueE Σ Γ (mkApps (tConstruct i n ui) args).

(** Base [firstorder_value_inds] ([:117]). *)
Lemma firstorder_value_indsE :
 forall (Σ : global_env_ext) (Γ : context) (P : term -> Prop),
(forall (i : inductive) (n : nat) (ui u : Instance.t)
   (args pandi : list term),
 Σ;;; Γ |-E mkApps (tConstruct i n ui) args : mkApps (tInd i u) pandi ->
 Forall (firstorder_valueE Σ Γ) args ->
 Forall P args ->
 ~~ isPropositional (PCUICEnvironment.fst_ctx Σ) i ->
 P (mkApps (tConstruct i n ui) args)) ->
forall t : term, firstorder_valueE Σ Γ t -> P t.
Proof using Type.
  intros ? ? ? ?. fix rec 2. intros t [ ]. eapply H; eauto.
  clear - H0 rec.
  induction H0; econstructor; eauto.
Qed.

(** Base [firstorder_ind_propositional] ([:133]). *)
Lemma firstorder_ind_propositionalE {Σ : global_env_ext} {wfΣ:wfE Σ} i mind oind :
  declared_inductive Σ i mind oind ->
  firstorder_ind Σ (firstorder_env Σ) i ->
  ~~ isPropositional Σ i.
Proof using Type.
  intros d. unshelve epose proof (d_ := declared_inductive_to_gen d); eauto.
  pose proof d_ as [d1 d2]. intros H. red in d1. unfold firstorder_ind in H.
  unfold isPropositional.
  unfold PCUICEnvironment.fst_ctx in *. rewrite d1 in H |- *.
  unfold firstorder_mutind in H.
  rewrite /lookup_inductive /lookup_inductive_gen /lookup_minductive_gen /= d1 d2.
  move/andP: H => [ind H0].
  eapply forallb_nth_error in H0; tea.
  erewrite d2 in H0. cbn in H0.
  unfold firstorder_oneind in H0. solve_all.
  destruct (ind_sort oind) eqn:E2; inv H0. reflexivity.
Qed.

(** Base [firstorder_spine] ([:151]). *)
Inductive firstorder_spineE Σ (Γ : context) : term -> list term -> term -> Type :=
| firstorder_spine_nilE ty ty' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ ty' ->
    Σ ;;; Γ ⊢E ty ≤ ty' ->
    firstorder_spineE Σ Γ ty [] ty'

| firstorder_spine_consE ty hd tl na i u args B B' mind oind :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ (tProd na (mkApps (tInd i u) args) B) ->
    Σ ;;; Γ ⊢E ty ≤ tProd na (mkApps (tInd i u) args) B ->
    declared_inductive Σ i mind oind ->
    Σ ;;; Γ |-E hd : (mkApps (tInd i u) args) ->
    firstorder_ind Σ (@firstorder_env Σ) i ->
    firstorder_spineE Σ Γ (subst10 hd B) tl B' ->
    firstorder_spineE Σ Γ ty (hd :: tl) B'.

Import PCUICLiftSubst.
(** Base [isType_context_conversion] ([:181]). *)
Lemma isType_context_conversionE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ} {T} :
  isTypeE Σ Γ T ->
  ws_cumul_ctx_pbE Conv Σ Γ Δ ->
  wf_localE Σ Δ ->
  isTypeE Σ Δ T.
Proof using Type.
  intros HT ??.
  apply lift_typing_impl with (1 := HT); intros ?? H.
  eapply context_conversionE; tea. now eapply ws_cumul_ctx_pbE_forget.
Qed.

(** Base [typing_spine_arity_spine] ([:192]). *)
Lemma typing_spine_arity_spineE {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ args T' i u pars :
  PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd i u) pars)) args T' ->
  PCUICSpineEta.arity_spineE Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd i u) pars)) args T'.
Proof using Type.
  intros H. revert args pars T' H.
  induction Δ using PCUICInduction.ctx_length_rev_ind; intros args pars T' H.
  - cbn. depelim H.
    + econstructor; eauto.
    + eapply invert_cumul_ind_prodE in w. eauto.
  - cbn. depelim H.
    + econstructor; eauto.
    + rewrite it_mkProd_or_LetIn_app in w, i0 |- *. cbn. destruct d as [name [body |] type]; cbn in *.
      -- constructor. rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps. eapply X. now len.
         econstructor; tea.
         ++ eapply isType_tLetIn_redE in i0; [|pcuic].
            rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps in i0. exact i0.
         ++ eapply ws_cumul_pbE_LetIn_l_inv in w.
            rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps in w. exact w.
      -- eapply cumul_Prod_invE in w as []. econstructor.
         ++ eapply type_ws_cumul_pbE. 3: eapply ws_cumul_pbE_eq_le; symmetry. all:eauto.
            eapply isType_tProdE in i0. eapply isTypeRelE_isTypeE, i0.
         ++ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. autorewrite with subst.
            cbn. eapply X. len.
            eapply typing_spine_strengthenE. eauto.
            2:{ replace (it_mkProd_or_LetIn (subst_context [hd] 0 Γ0)
            (mkApps (tInd i u) (map (subst [hd] (#|Γ0| + 0)) pars))) with ((PCUICAst.subst10 hd (it_mkProd_or_LetIn Γ0 (mkApps (tInd i u) pars)))).
            2:{ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. now autorewrite with subst. }
            eapply substitution0_ws_cumul_pbE; [now eapply subject_is_open_termE|eauto].
            }
            replace (it_mkProd_or_LetIn (subst_context [hd] 0 Γ0)
            (mkApps (tInd i u) (map (subst [hd] (#|Γ0| + 0)) pars))) with ((PCUICAst.subst10 hd (it_mkProd_or_LetIn Γ0 (mkApps (tInd i u) pars)))).
            2:{ rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn. now autorewrite with subst. }
            eapply isType_substE. eapply subslet_ass_tipE. eauto.
            eapply isType_tProdE in i0 as [_ tprod].
            eapply isType_context_conversionE; tea. constructor. eapply ws_cumul_ctx_pbE_refl. now eapply typingE_wf_local, wf_local_closed_contextE in t.
            constructor; tea. constructor. pcuic. now eapply isType_tProdE in i1 as [].
Qed.

(* As base ([:260]), section-local. *)
Arguments firstorder_mutind : clear implicits.

(** Base [firstorder_spine_let] ([:298]). *)
Lemma firstorder_spine_letE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na a A B args T'} :
  firstorder_spineE Σ Γ (B {0 := a}) args T' ->
  isTypeE Σ Γ (tLetIn na a A B) ->
  firstorder_spineE Σ Γ (tLetIn na a A B) args T'.
Proof using Type.
  intros H; depind H.
  - constructor; auto.
    match goal with h : isTypeE _ _ (tLetIn _ _ _ _) |- _ =>
      eapply red_ws_cumul_pbE_left; [|tea];
      constructor; [exact (wf_local_closed_contextE (isType_wf_localE h))
                   |exact (PCUICClosedTypEta.isType_is_open_termE h)
                   |apply rt_step; apply red_zeta] end.
  - intros. econstructor. tea.
    2:{ match goal with h : isTypeE _ _ (tLetIn _ _ _ _) |- _ =>
          eapply red_ws_cumul_pbE_left; [|tea];
          constructor; [exact (wf_local_closed_contextE (isType_wf_localE h))
                       |exact (PCUICClosedTypEta.isType_is_open_termE h)
                       |apply rt_step; apply red_zeta] end. }
    all:tea.
Qed.

Section FirstorderForecastE.

(* FORECAST-ONLY: T1's class ([PCUICSREta]); delete it when copy 18b lands. A lemma takes the
   class only where its proof names it in [Proof using]. *)
Context {F18 : SRForecastCopy18}.

(** Base [instantiated_typing_spine_firstorder_spine] ([:314]). *)
Lemma instantiated_typing_spine_firstorder_spineE {Σ : global_env_ext} {wfΣ : wfE Σ} Γ T args T' :
  instantiated (Σ := Σ) Γ T ->
  PCUICSpineEta.arity_spineE Σ Γ T args T' ->
  isTypeE Σ Γ T ->
  firstorder_spineE Σ Γ T args T'.
Proof using.
  intros hi hsp.
  revert hi; induction hsp; intros hi isty.
  - constructor => //. now eapply isType_ws_cumul_pbE_refl.
  - econstructor; eauto.
  - depelim hi. solve_discr. eapply firstorder_spine_letE; eauto. eapply IHhsp => //.
    now eapply isType_tLetIn_redE in isty; pcuic.
  - depelim hi. solve_discr.
    specialize (i1 hd). specialize (IHhsp i1).
    destruct (validityE t) as (_ & s & Hs & _). eapply PCUICValidityEta.inversion_mkAppsE in Hs as [? [hi _]].
    eapply inversion_IndE in hi as [mdecl [idecl [decli [? ?]]]].
    econstructor; tea. 2:{ eapply IHhsp. eapply isType_applyE in isty; tea. }
    now eapply isType_ws_cumul_pbE_refl. eauto.
Qed.

(* As base ([:334]), section-local. *)
Arguments firstorder_type : clear implicits.

Import PCUICGlobalMaps.

(** Base [plookup_env_extends] ([:377]). *)
Lemma plookup_env_extendsE {Σ Σ' : global_env} kn b :
  strictly_extends_decls Σ' Σ ->
  wfE Σ ->
  plookup_env (firstorder_env' (declarations Σ')) kn = Some b ->
  plookup_env (firstorder_env' (declarations Σ)) kn = Some b.
Proof using Type.
  intros [equ [Σ'' eq] eqr]. rewrite eq.
  clear equ eqr. intros [o [_ o0]]. clear o.
  rewrite eq in o0. clear eq. move: o0.
  generalize (declarations Σ'). clear Σ'.
  induction Σ''.
  - cbn => //.
  - cbn. destruct a => //. intros gs ong.
    depelim ong. specialize (IHΣ'' _ ong).
    destruct o as [f ? ? ?].
    destruct g => //.
    * intros hl. specialize (IHΣ'' hl).
      eapply plookup_env_Some_not_fresh in hl.
      cbn. case: eqb_spec.
      + intros <-.  apply fresh_global_app in f as [].
        contradiction.
      + now intros neq.
    * intros hl. specialize (IHΣ'' hl).
      eapply plookup_env_Some_not_fresh in hl.
      cbn. case: eqb_spec.
      + intros <-. apply fresh_global_app in f as [].
        contradiction.
      + now intros neq.
Qed.

(** Base [firstorder_mutind_ext] ([:407]). *)
Lemma firstorder_mutind_extE {Σ Σ' : global_env_ext} m :
  strictly_extends_decls Σ' Σ ->
  wfE Σ ->
  firstorder_mutind (firstorder_env' (declarations Σ')) m ->
  firstorder_mutind (firstorder_env Σ) m.
Proof using Type.
  intros [equ [Σ'' eq]] wf.
  unfold firstorder_env. rewrite eq.
  unfold firstorder_mutind.
  move/andP => [] -> /=. apply forallb_impl => x _.
  unfold firstorder_oneind.
  move/andP => [] h -> /=; rewrite andb_true_r.
  eapply forallb_impl; tea => c _.
  unfold firstorder_con.
  eapply alli_impl => i [] _ _ ty.
  unfold firstorder_type.
  destruct decompose_app => // /=.
  destruct t => //. destruct ind => //.
  destruct plookup_env eqn:hl => //. destruct b => //.
  eapply (plookup_env_extendsE (Σ:=Σ)) in hl. 2:split; eauto.
  rewrite eq in hl. rewrite hl //. apply wf.
  all: destruct l; eauto.
Qed.

(** Base [firstorder_args] ([:431]). *)
Lemma firstorder_argsE {Σ : global_env_ext} {wfΣ : wfE Σ} { mind cbody i n ui args u pandi oind} :
  declared_constructor Σ (i, n) mind oind cbody ->
  PCUICAritiesEta.typing_spineE Σ [] (type_of_constructor mind cbody (i, n) ui) args (mkApps (tInd i u) pandi) ->
  firstorder_ind Σ (@firstorder_env Σ) i ->
  firstorder_spineE Σ [] (type_of_constructor mind cbody (i, n) ui) args (mkApps (tInd i u) pandi).
Proof using.
  intros Hdecl Hspine Hind. revert Hspine.
  unshelve edestruct @declared_constructor_invE with (Hdecl := Hdecl); eauto. exact weaken_env_prop_typingE.

  (* revert Hspine. *) unfold type_of_constructor.
  erewrite cstr_eq. 2: eapply p.
  rewrite <- it_mkProd_or_LetIn_app.
  rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
  rewrite PCUICSpine.subst0_it_mkProd_or_LetIn. intros Hspine.

  match goal with
   | [ |- firstorder_spineE _ _ ?T _ _ ] =>
  assert (@instantiated Σ [] T) as Hi end.
  { clear Hspine. destruct Hdecl as [[d1 d3] d2]. pose proof d3 as Hdecl.
    unfold firstorder_ind in Hind.
    unshelve epose proof (d1_ := declared_minductive_to_gen d1); eauto.
    rewrite d1_ in Hind. solve_all. clear a.
    move/andP: Hind => [indf H0].
    eapply forallb_nth_error in H0 as H'.
    erewrite d3 in H'.
    unfold firstorder_oneind in H'. cbn in H'.
    rtoProp.
    eapply nth_error_forallb in H. 2: eauto.
    unfold firstorder_con in H.
    revert H. cbn.
    unfold cstr_concl.
    rewrite PCUICUnivSubst.subst_instance_mkApps subst_mkApps.
    rewrite subst_instance_length length_app.
    unfold cstr_concl_head. rewrite PCUICInductives.subst_inds_concl_head. now eapply nth_error_Some_length in Hdecl.
    rewrite -length_app.
    generalize (cstr_args cbody ++ ind_params mind)%list.
    clear -wfΣ d1 indf H1 H0 Hdecl.
    (* generalize conclusion to mkApps tInd args *)
    intros c.
    change (list context_decl) with context in c.
    move: (map (subst (inds _ _ _) _) _).
    intros args.
    rewrite (alli_subst_instance _ ui (fun k t => firstorder_type _ #|ind_bodies mind| k t)).
    { intros k t.
      rewrite /firstorder_type.
      rewrite -PCUICUnivSubstitutionConv.subst_instance_decompose_app /=.
      destruct (decompose_app) => //=. destruct t0 => //; destruct l; eauto. }
    replace (List.rev c)@[ui] with (List.rev c@[ui]).
    2:{ rewrite /subst_instance /subst_instance_context /map_context map_rev //. }
    revert args.
    induction (c@[ui]) using PCUICInduction.ctx_length_rev_ind => args.
    - unfold cstr_concl, cstr_concl_head. cbn.
      autorewrite with substu subst.
      rewrite subst_context_nil. cbn -[subst0].
      econstructor.
    - rewrite rev_app_distr /=. destruct d as [na [b|] t].
      + move=> /andP[] fot foΓ.
        rewrite subst_context_app /=.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        constructor.
        rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps /=. len.
        rewrite -subst_app_context' // PCUICSigmaCalculus.subst_context_decompo.
        cbn. len. eapply X. now len.
        rewrite -subst_telescope_subst_context. clear -foΓ.
        revert foΓ. move: (lift0 #|ind_bodies mind| _).
        generalize 0.
        induction (List.rev Γ) => //.
        cbn -[subst_telescope]. intros n t.
        destruct a; cbn -[subst_telescope].
        move/andP => [] fo fol.
        rewrite PCUICContextSubst.subst_telescope_cons /=.
        apply/andP; split; eauto.
        clear -fo.
        move: fo.
        unfold firstorder_type; cbn.
        destruct (decompose_app decl_type) eqn:da.
        rewrite (decompose_app_inv da) subst_mkApps /=.
        destruct t0 => //=; destruct l; eauto.
        { move/andP => [/Nat.leb_le hn /Nat.ltb_lt hn'].
          destruct (Nat.leb_spec n n0).
          destruct (n0 - n) eqn:E. lia.
          cbn. rewrite nth_error_nil /=.
          apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
          rewrite decompose_app_mkApps //=.
          apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
        { destruct ind => //. }
      + move=> /andP[] fot foΓ.
        rewrite subst_context_app /=.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        unfold firstorder_type in fot.
        destruct ((PCUICAstUtils.decompose_app t)) eqn:E.
        cbn in fot. destruct t0; try solve [inv fot].
        * rewrite (decompose_app_inv E) /= subst_mkApps.
          rewrite Nat.add_0_r in fot. destruct l; try solve [inversion fot].
          eapply Nat.ltb_lt in fot.
          cbn. rewrite nth_error_inds. lia. cbn.
          eapply instantiated_tProd with (args := []).
          unshelve epose proof (d1_ := declared_minductive_to_gen d1); eauto.
          { rewrite /firstorder_ind d1_ /= /firstorder_mutind indf H0 //. }
          intros x.
          rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps /=. len.
          rewrite -subst_app_context' // PCUICSigmaCalculus.subst_context_decompo.
          cbn. len. eapply X. now len.
          rewrite -subst_telescope_subst_context. clear -foΓ.
          revert foΓ. generalize (lift0 #|ind_bodies mind| x).
          generalize 0.
          induction (List.rev Γ) => //.
          cbn -[subst_telescope]. intros n t.
          destruct a; cbn -[subst_telescope].
          move/andP => [] fo fol.
          rewrite PCUICContextSubst.subst_telescope_cons /=.
          apply/andP; split; eauto.
          clear -fo.
          move: fo.
          unfold firstorder_type; cbn.
          destruct (decompose_app decl_type) eqn:da.
          rewrite (decompose_app_inv da) subst_mkApps /=.
          destruct t0 => //=; destruct l; eauto.
          { move/andP => [/Nat.leb_le hn /Nat.ltb_lt hn'].
            destruct (Nat.leb_spec n n0).
            destruct (n0 - n) eqn:E. lia.
            cbn. rewrite nth_error_nil /=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
            rewrite decompose_app_mkApps //=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
          { destruct ind => //. }
        * rewrite (decompose_app_inv E) subst_mkApps //=.
          constructor. {
             unfold firstorder_ind. destruct ind. cbn in *.
             destruct l; [|inversion fot].
             destruct plookup_env eqn:hp => //.
             eapply plookup_env_lookup_env in hp as [Σ' [decl [eq [ext he]]]].
             rewrite eq. destruct decl; subst b => //.
             eapply (firstorder_mutind_extE (Σ' := (empty_ext Σ'))); tea. }
          intros x. rewrite /subst1 PCUICLiftSubst.subst_it_mkProd_or_LetIn subst_mkApps /=; len.
          rewrite -subst_app_context' // PCUICSigmaCalculus.subst_context_decompo.
          eapply X. now len. len.
          rewrite -subst_telescope_subst_context. clear -foΓ.
          revert foΓ. generalize (lift0 #|ind_bodies mind| x).
          generalize 0.
          induction (List.rev Γ) => //.
          cbn -[subst_telescope]. intros n t.
          destruct a; cbn -[subst_telescope].
          move/andP => [] fo fol.
          rewrite PCUICContextSubst.subst_telescope_cons /=.
          apply/andP; split; eauto.
          clear -fo.
          move: fo.
          unfold firstorder_type; cbn.
          destruct (decompose_app decl_type) eqn:da.
          rewrite (decompose_app_inv da) subst_mkApps /=.
          destruct t0 => //=; destruct l; eauto.
          { move/andP => [/Nat.leb_le hn /Nat.ltb_lt hn'].
            destruct (Nat.leb_spec n n0).
            destruct (n0 - n) eqn:E. lia.
            cbn. rewrite nth_error_nil /=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
            rewrite decompose_app_mkApps //=.
            apply/andP. split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
          { destruct ind => //. }
  }
  cbn in Hi |- *.
  revert Hi Hspine. cbn.
  unfold cstr_concl, cstr_concl_head.
  autorewrite with substu subst.
  rewrite subst_instance_length length_app.
  rewrite PCUICInductives.subst_inds_concl_head. { cbn. destruct Hdecl as [[d1 d2] d3]. eapply nth_error_Some. rewrite d2. congruence. }
  match goal with [ |- context[mkApps _ ?args]] => generalize args end.
  intros args' Hi Spine.
  eapply instantiated_typing_spine_firstorder_spineE; tea.
  now eapply typing_spine_arity_spineE in Spine.
  now eapply typing_spine_isType_domE in Spine.
Qed.

(** Base [firstorder_value_spec] ([:618]). *)
Lemma firstorder_value_specE (Σ:global_env_ext) t i u args :
  wfE Σ -> wf_localE Σ [] ->
   Σ ;;; [] |-E t : mkApps (tInd i u) args ->
  PCUICWcbvEval.value Σ t ->
  firstorder_ind Σ (firstorder_env Σ) i ->
  firstorder_valueE Σ [] t.
Proof using F18.
  intros Hwf Hwfl Hty Hvalue.
  revert i u args Hty.

  induction Hvalue as [ t Hvalue | p pv ih | t args' Hhead Hargs IH ] using PCUICWcbvEval.value_values_ind;
   intros i u args Hty Hfo.
  - destruct t; inversion_clear Hvalue.
    + exfalso. eapply inversion_SortE in Hty as (? & ? & Hcumul); eauto.
      now eapply invert_cumul_sort_indE in Hcumul.
    + exfalso. eapply inversion_ProdE in Hty as (? & ? & ? & ? & Hcumul); eauto.
      now eapply invert_cumul_sort_indE in Hcumul.
    + exfalso. eapply inversion_LambdaE in Hty as (? & ? & ? & Hcumul); eauto.
      now eapply invert_cumul_prod_indE in Hcumul.
    + exfalso. eapply inversion_IndE in Hty as (? & ? & ? & d & ? & w); eauto.
      epose proof (declared_inductive_type_ws_cumulE d [] _ Hwfl) as e.
      symmetry in e. eapply ws_cumul_pbE_eq_le in e.
      eapply (ws_cumul_pbE_trans _ _ _ e) in w. clear e.
      destruct (ind_params x ,,, ind_indices x0) as [ | [? [] ?] ? _] using rev_ind.
      * cbn in w. now eapply invert_cumul_sort_indE in w.
      * rewrite it_mkProd_or_LetIn_app in w. cbn in w.
        eapply ws_cumul_pbE_LetIn_l_inv in w.
        rewrite /subst1 PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn PCUICLiftSubst.subst_it_mkProd_or_LetIn in w.
        (* Base [invert_cumul_it_mkProd_or_LetIn_Sort_Ind] ([:605]): the landed, stronger
           [PCUICEtaA6More.invert_cumul_it_mkProd_or_LetIn_Sort_IndE] (row x16: any [pb],
           [ClosedBodies]) at [Cumul], with [wfE_ClosedBodies]. *)
        now eapply (PCUICEtaA6More.invert_cumul_it_mkProd_or_LetIn_Sort_IndE
                      (wfΣ := wfE_ClosedBodies Σ (wfΣ := Hwf)) (pb := Cumul)) in w.
      * rewrite it_mkProd_or_LetIn_app in w. cbn in w.
        now eapply invert_cumul_prod_indE in w.
    + eapply inversion_ConstructE in Hty as Hty'; eauto.
      destruct Hty' as (? & ? & ? & ? & ? & ? & ?).
      assert (ind = i) as ->. {
         eapply Construct_Ind_ind_eqE with (args := []); eauto.
      }
      eapply firstorder_value_CE with (args := []); eauto.
      eapply firstorder_ind_propositionalE; eauto. sq. eauto.
      apply declared_inductive_from_gen.
      eapply (declared_constructor_inductive (ind := (i, _))).
      unshelve eapply declared_constructor_to_gen; eauto.
    + exfalso. eapply invert_fix_indE with (args := []) in Hty as [].
      destruct unfold_fix as [ [] | ]; auto. eapply nth_error_nil.
    + exfalso. eapply (typing_cofix_coindE (args := [])) in Hty. red in Hty.
      red in Hfo. unfold firstorder_ind in Hfo.
      destruct lookup_env eqn:E; try congruence.
      destruct g; try congruence.
      eapply andb_true_iff in Hfo as [Hfo _].
      rewrite /check_recursivity_kind E in Hty.
      now eapply (negb_False _ Hfo).
  - eapply inversion_PrimE in Hty as [prim_ty [cdecl [wf hp hdecl inv ty cum]]]; eauto.
      (* The guard on the axiom inversions: [prim_ty] is the registered
         primitive TYPE constant, which §4.2(a)1 keeps out of the operation
         table. *)
      assert (hnop : prim_op_of Σ prim_ty = None).
      { pose proof Hwf as [_ [wfr _]]. eapply prim_op_of_primitive_constant; tea. }
      now eapply invert_cumul_prim_type_indE in cum; tea.
  - destruct t; inv Hhead.
    + exfalso. now eapply invert_ind_indE in Hty.
    + apply PCUICValidityEta.inversion_mkAppsE in Hty as Hcon; auto.
      destruct Hcon as (?&typ_ctor& spine).
      apply inversion_ConstructE in typ_ctor as (?&?&?&?&?&?&?); auto.
      pose proof d as [[d' _] _]. red in d'. cbn in *. unfold PCUICEnvironment.fst_ctx in *.
      eapply @Construct_Ind_ind_eqE with (mdecl := x0) in Hty as Hty'; eauto.
      destruct Hty' as (([[[]]] & ?)  & ? & ? & ? & ? & _). subst.
      econstructor; eauto.
      2:{ eapply firstorder_ind_propositionalE; sq; eauto.
          unshelve eapply declared_constructor_to_gen in d; eauto.
          eapply declared_constructor_inductive in d.
          apply declared_inductive_from_gen; eauto. }
      eapply typing_spine_strengthenE in spine. 3: eauto.
      2: eapply declared_constructor_valid_tyE; eauto.

      eapply firstorder_argsE in spine; eauto.
      clear c0 c1 e0 w Hty H0 Hargs.
      induction spine.
      * econstructor.
      * destruct d as [d1 d2]. inv IH.
        econstructor. inv X.
        eapply H0. tea.
        unshelve eapply declared_inductive_to_gen in d0; eauto.
        inv X. eapply IHspine; eauto.
     + exfalso.
       destruct PCUICWcbvEval.cunfold_fix as [[] | ] eqn:E; inversion H.
       eapply invert_fix_indE in Hty. auto.
       unfold unfold_fix. unfold PCUICWcbvEval.cunfold_fix in E.
       destruct (nth_error mfix idx); auto.
       inversion E; subst; clear E.
       eapply nth_error_None. lia.
    + exfalso. eapply (typing_cofix_coindE (args := args')) in Hty.
      red in Hfo. unfold firstorder_ind in Hfo.
      destruct lookup_env eqn:E; try congruence.
      destruct g; try congruence.
      eapply andb_true_iff in Hfo as [Hfo _].
      rewrite /check_recursivity_kind E in Hty.
      now eapply (negb_False _ Hfo).
Qed.

End FirstorderForecastE.

(** Base [firstorder_value_alpha] ([:716]). *)
Lemma firstorder_value_alphaE Σ t t' :
  t ≡α t' ->
  firstorder_valueE Σ [] t ->
  t = t'.
Proof.
  intros Ha H. induction H in t', Ha |- using firstorder_value_indsE.
  eapply eq_term_upto_univ_napp_mkApps_l_inv in Ha as (? & ? & [] & ->).
  invs e. repeat f_equal.
  - now eapply cmp_universe_instance_eq.
  - revert x0 a. clear - H0. induction H0; intros; invs a; f_equal; eauto.
Qed.

End cf.
