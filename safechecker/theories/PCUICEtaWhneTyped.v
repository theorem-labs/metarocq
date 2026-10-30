(* Distributed under the terms of the MIT license. *)
(* The header is EtaMetaLane's [PCUICSREta]'s ([pcuic/theories/PCUICSREta.v] on frac/eta 730e8c59), the
   same as [PCUICEtaPrimOverapplied]'s, then the landed SR and classification copies and the untyped
   weak-head forms. *)
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
(* Base [PCUICClassification], for its untyped helpers ([assumption_context_assumptions],
   [assumption_context_firstn]: their compiled forms take no environment premise), as
   [PCUICClassificationEta] does; the E copies imported below come later and are the ones named. *)
From MetaRocq.PCUIC Require Import PCUICClassification.
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
(* LAND3 (frac/eta 730e8c59): subject reduction and classification over [typingE]. *)
From MetaRocq.PCUIC Require Import PCUICSREta PCUICClassificationEta.
(* Copy 18b; base's untyped [PCUICPrimCanonical] lemmas ([primitive_constant_inj],
   [prim_op_args_int_or_string]); the canonical form [canon] of the E cumulativity. All qualified. *)
From MetaRocq.PCUIC Require PCUICInductiveInversionEtaB PCUICPrimCanonical PCUICEtaCanon.
(* The weak-head forms ([whnf], [whne] and their constructors), untyped and unchanged in E. *)
From MetaRocq.PCUIC Require Import PCUICNormal.

From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.
Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** * ETAK discharge: canonical forms at a primitive type, and rows 48-50, over [typingE]

  BET-64 EtaCheckerLane, worker EtaTranscribe6, 2026-10-30. The E twins of:
  - base [PCUICPrimCanonical]'s section [BelowAxiom] ([PCUICPrimCanonical.v:45-90]) and
    [whnf_prim_type_canonical] ([:107]);
  - base [PCUICSafeReduce]'s [prim_rigid_arg_whne] ([:177]), [whnf_non_ctor_finite_ind_typed]
    ([:1638]), [whnf_non_ctor_non_cofix_ind_typed] ([:1690]), [whnf_fix_arg_whne] ([:1732]),
    [whnf_case_arg_whne] ([:1765]), [whnf_proj_arg_whne] ([:1786]): the base proofs of the fields
    [rtfc_fix_arg_whne], [rtfc_case_arg_whne], [rtfc_proj_arg_whne] of
    [PCUICEtaFactsCompose.ReduceTypedFactsCoreE] (rows 48-50 of [lanes/eta/etak/eta51-sizing.md]).
  Each statement is base's with [typing] → [typingE], [wf] → [wfE], [⊢] → [⊢E] (cumulativity),
  [typing_spine] → [PCUICAritiesEta.typing_spineE]; [whnf], [whne] and reduction are unchanged. Each
  script is base's with every typed lemma replaced by its landed E twin: the E inversions
  ([PCUICInversionEta]), [validityE], [inversion_mkAppsE] ([PCUICValidityEta]),
  [inversion_mkApps_directE], [typing_spine_strengthenE] ([PCUICSpineEta]), the classification
  copies ([PCUICClassificationEta]: [typing_spine_smashE], [typing_spine_nth_error_None_prodE],
  [typing_spine_all_invE], [typing_spine_more_invE], [wf_fixpoint_spineE], [wf_cofixpoint_spineE],
  [isArity_typing_spineE], [invert_ind_indE], [invert_fix_indE], [typing_cofix_coindE],
  [wt_closed_red_reflE]), [prim_app_typing_invE] and [prim_op_head_typeE] ([PCUICSREta]), and the A6
  head clashes ([PCUICEtaA6Ind], [PCUICEtaA6More]).
  One step does not transcribe one by one: base's [BelowAxiom] reads a closed REDUCTION out of
  [ws_cumul_pb_Axiom_r_inv]; the E inversion [ws_cumul_pbE_Axiom_r_inv] gives a [chain] of canonical
  forms instead. The [_not_below_axiomE] lemmas below conclude base's statements from that chain, with
  A6's chain lemmas ([chain_Sort], [chain_Prod], [chain_mkApps_Ind], [chain_mkApps_Const]).
  No row uses [wf_cofixpoint_all] or [ws_cumul_pb_terms_confl] (the two lemmas false over η in their
  untyped forms). No hypothesis (no [Context], no class field). *)

(** ** Base [BelowAxiom] ([PCUICPrimCanonical.v:45-90]): what lies below a bodiless non-operation *)

(** Base [sort_not_below_axiom] ([:56]). *)
Lemma sort_not_below_axiomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {kn d} :
  declared_constant Σ kn d -> cst_body d = None -> prim_op_of Σ kn = None ->
  forall {Γ s u}, Σ ;;; Γ ⊢E tSort s ≤ tConst kn u -> False.
Proof.
  intros hd hb hnop Γ s u h.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  destruct (ws_cumul_pbE_Axiom_r_inv (args := []) hd hb hnop h) as (u' & args' & [hc _ _]).
  cbn [PCUICEtaCanon.canon] in hc. apply chain_Sort in hc.
  destruct (mkApps_head_inj (tConst kn u') (tSort s) args' [] eq_refl eq_refl hc) as [E _].
  discriminate E.
Qed.

(** Base [prod_not_below_axiom] ([:63]). *)
Lemma prod_not_below_axiomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {kn d} :
  declared_constant Σ kn d -> cst_body d = None -> prim_op_of Σ kn = None ->
  forall {Γ na A B u}, Σ ;;; Γ ⊢E tProd na A B ≤ tConst kn u -> False.
Proof.
  intros hd hb hnop Γ na A B u h.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  destruct (ws_cumul_pbE_Axiom_r_inv (args := []) hd hb hnop h) as (u' & args' & [hc _ _]).
  cbn [PCUICEtaCanon.canon] in hc.
  destruct (chain_Prod _ _ _ _ _ hc) as (na1 & A1 & B1 & [E _ _ _]).
  exact (mkApps_rigid_not_Prod (tConst kn u') _ _ _ _ eq_refl (fun _ _ _ => ltac:(discriminate)) E).
Qed.

(** Base [ind_not_below_axiom] ([:70]). *)
Lemma ind_not_below_axiomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {kn d} :
  declared_constant Σ kn d -> cst_body d = None -> prim_op_of Σ kn = None ->
  forall {Γ ind ui l u}, Σ ;;; Γ ⊢E mkApps (tInd ind ui) l ≤ tConst kn u -> False.
Proof.
  intros hd hb hnop Γ ind ui l u h.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  pose proof h as [hΓ hl hr _].
  destruct (ws_cumul_pbE_Axiom_r_inv (args := []) hd hb hnop h) as (u' & args' & [hc _ _]).
  rewrite PCUICEtaI5A2.canon_mkApps in hc. cbn [PCUICEtaCanon.canon] in hc.
  destruct (chain_mkApps_Ind Γ ind ui (map PCUICEtaCanon.canon l) _ hΓ (open_mkApps_canon Γ _ l eq_refl hl) hc)
    as (l1 & E & _).
  destruct (mkApps_head_inj (tConst kn u') (tInd ind ui) _ _ eq_refl eq_refl E) as [E1 _].
  discriminate E1.
Qed.

(** What base's literal case reads off [below_axiom] and [invert_red_axiom(_app)] ([:226-236]): an
    application of a bodiless non-operation [c] below another one [kn] has [c = kn]. *)
Lemma axiom_below_axiomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {c dc kn dk} :
  declared_constant Σ c dc -> cst_body dc = None -> prim_op_of Σ c = None ->
  declared_constant Σ kn dk -> cst_body dk = None -> prim_op_of Σ kn = None ->
  forall {pb Γ u args uk}, Σ ;;; Γ ⊢E mkApps (tConst c u) args ≤[pb] tConst kn uk -> c = kn.
Proof.
  intros hdc hbc hnc hdk hbk hnk pb Γ u args uk h.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  pose proof h as [hΓ hl hr _].
  destruct (ws_cumul_pbE_Axiom_r_inv (args := []) hdk hbk hnk h) as (u' & args' & [hc _ _]).
  rewrite PCUICEtaI5A2.canon_mkApps in hc. cbn [PCUICEtaCanon.canon] in hc.
  destruct (chain_mkApps_Const Γ c dc u (map PCUICEtaCanon.canon args) _ hdc hbc hnc hΓ
              (open_mkApps_canon Γ _ args eq_refl hl) hc) as (l1 & E & _).
  destruct (mkApps_head_inj (tConst kn u') (tConst c u) _ _ eq_refl eq_refl E) as [E1 _].
  injection E1 as ekn _. now subst.
Qed.

(** Base [Is_conv_to_Arity_axiom] ([:77]), over [ClosedBodies] ([invert_red_axiom_cb]). *)
Lemma Is_conv_to_Arity_axiomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {kn d} :
  declared_constant Σ kn d -> cst_body d = None -> prim_op_of Σ kn = None ->
  forall {Γ u}, Is_conv_to_Arity Σ Γ (tConst kn u) -> False.
Proof.
  intros hd hb hnop Γ u.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  move=> [ar [[r] isA]].
  pose proof (invert_red_axiom_cb (cbΣ := cbΣ) hd hb hnop r) as e. rewrite e in isA. inversion isA.
Qed.

(** Base [typing_spine_arity_axiom] ([:83]). *)
Lemma typing_spine_arity_axiomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {kn d} :
  declared_constant Σ kn d -> cst_body d = None -> prim_op_of Σ kn = None ->
  forall {Γ T l u},
  wf_localE Σ Γ -> PCUICAritiesEta.typing_spineE Σ Γ T l (tConst kn u) ->
  Is_conv_to_Arity Σ Γ T -> False.
Proof.
  intros hd hb hnop Γ T l u.
  move=> wf sp isc.
  eapply (isArity_typing_spineE wf sp) in isc.
  now eapply (Is_conv_to_Arity_axiomE hd hb hnop).
Qed.

(** ** Base [whnf_prim_type_canonical] ([PCUICPrimCanonical.v:107]) *)

Lemma whnf_prim_type_canonicalE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} flags {Γ a tag kn d u} :
  primitive_constant Σ tag = Some kn -> declared_constant Σ kn d -> primitive_invariants tag d ->
  tag = primInt \/ tag = primString ->
  whnf flags Σ Γ a -> Σ ;;; Γ |-E a : tConst kn u -> lit_of_term a = None ->
  whne flags Σ Γ a.
Proof.
  move=> hkn hd hinv htag hw.
  revert tag kn d u hkn hd hinv htag.
  induction hw; intros tag kn dk uk hkn hd hinv htag typ hnl.
  all: assert (hb : cst_body dk = None)
         by (destruct htag as [-> | ->]; destruct hinv as [_ hb' _]; exact hb').
  all: pose proof wfΣ as (_ & wfr & _).
  all: assert (hnop : prim_op_of Σ kn = None)
         by exact (prim_op_of_primitive_constant Σ tag kn wfr hkn).
  - (* neutral *) assumption.
  - (* sort *) exfalso.
    apply inversion_SortE in typ as (? & ? & hle); auto.
    exact (sort_not_below_axiomE hd hb hnop hle).
  - (* product *) exfalso.
    apply inversion_ProdE in typ as (? & ? & ? & ? & hle); auto.
    exact (sort_not_below_axiomE hd hb hnop hle).
  - (* lambda *) exfalso.
    apply inversion_LambdaE in typ as (? & ? & ? & hle); auto.
    exact (prod_not_below_axiomE hd hb hnop hle).
  - (* constructor *) exfalso.
    eapply inversion_mkAppsE in typ as [A [hC hs]]; auto.
    apply inversion_ConstructE in hC as [mdecl [idecl [cdecl [hΓ [isdecl [const htc]]]]]]; auto.
    assert (vty := PCUICInductiveInversionEtaB.declared_constructor_valid_tyE _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const).
    eapply typing_spine_strengthenE in hs. 3:eapply htc. all:eauto.
    pose proof isdecl as declc.
    destruct (on_declared_constructorE declc) as [[onmind onind] [? [_ onc]]].
    destruct declc as [decli declc].
    destruct onc as [argslength cdecl_eq [cs' t] cargs cinds]; simpl.
    unfold type_of_constructor in hs, vty. simpl in hs, vty.
    rewrite cdecl_eq in hs vty.
    rewrite !subst_instance_it_mkProd_or_LetIn in hs vty.
    rewrite !subst_it_mkProd_or_LetIn subst_instance_length Nat.add_0_r in hs vty.
    rewrite subst_instance_mkApps subst_mkApps subst_instance_length in hs vty.
    assert (Hind : inductive_ind i < #|ind_bodies mdecl|).
    { destruct decli. now eapply nth_error_Some_length in H0. }
    rewrite (subst_inds_concl_head i) in hs vty => //.
    rewrite -it_mkProd_or_LetIn_app in hs vty.
    eapply typing_spine_smashE in hs.
    rewrite expand_lets_mkApps in hs.
    set (Δ := smash_context [] _) in hs.
    have assΔ : assumption_context Δ by apply smash_context_assumption_context; constructor.
    destruct (Nat.lt_total #|v| (context_assumptions Δ)) as [lt|[eq|gt]].
    + destruct (nth_error (List.rev Δ) #|v|) as [dl|] eqn:hn.
      2:{ apply nth_error_None in hn. rewrite ?List.length_rev ?rev_length in hn.
          rewrite (assumption_context_assumptions assΔ) in lt. lia. }
      eapply (typing_spine_nth_error_None_prodE _ _ _ _ _ _ #|v| dl) in hs
        as (na & dom & codom & cum); eauto.
      * exact (prod_not_below_axiomE hd hb hnop cum).
      * eapply wf_local_smash_endE; eauto.
        destruct vty as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetInE in Hs; eauto.
        now eapply typingE_wf_local.
      * now apply nth_error_None.
    + destruct (typing_spine_all_invE wfΣ _ _ _ _ _ hs eq) as [cum _].
      rewrite expand_lets_mkApps subst_mkApps /= in cum.
      exact (ind_not_below_axiomE hd hb hnop cum).
    + exact (typing_spine_more_invE wfΣ _ _ _ _ _ _ _ hs gt).
    + exact wfΣ.
  - (* inductive *) exfalso.
    eapply inversion_mkAppsE in typ as (? & ? & ?); auto.
    eapply inversion_IndE in t as (? & ? & wfΓ & decl & cu & ?); auto.
    eapply typing_spine_strengthenE in t0; eauto.
    eapply (typing_spine_ind_type_invE decl) in t0; tea.
    rewrite it_mkProd_or_LetIn_app !subst_instance_it_mkProd_or_LetIn in t0.
    eapply (typing_spine_arity_axiomE hd hb hnop) in t0; eauto.
    eapply typing_spine_isType_domE in t0 as (_ & s & Hs & _).
    eexists; split; [sq|]. now eapply wt_closed_red_reflE.
    now do 2 eapply isArity_it_mkProd_or_LetIn.
    now eapply isTypeRelE_isTypeE, (declared_inductive_valid_typeE decl).
  - (* unsaturated fixpoint *) exfalso.
    eapply inversion_mkAppsE in typ as (? & ? & ?); eauto.
    eapply inversion_FixE in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRelE_isTypeE in a.
    eapply typing_spine_strengthenE in t0; eauto.
    destruct o as [[? [e' hnth]] | e']; rewrite e in e'; noconf e'.
    eapply (wf_fixpoint_spineE wfΣ) in t0; eauto.
    rewrite hnth in t0. destruct t0 as [na [dom [codom cum]]].
    exact (prod_not_below_axiomE hd hb hnop cum).
  - (* cofixpoint *) exfalso.
    eapply inversion_mkAppsE in typ as [A [Hcof sp]]; auto.
    eapply inversion_CoFixE in Hcof as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto.
    simpl in a.
    apply isTypeRelE_isTypeE in a.
    eapply typing_spine_strengthenE in sp; eauto.
    eapply wf_cofixpoint_spineE in sp as (Γ' & concl & _ & ?); eauto.
    move: s => [ind' [u' [indargs' [[ceq ccum] ck]]]].
    subst concl. move: ck.
    elim: Nat.ltb_spec => Hargs.
    + rewrite subst_it_mkProd_or_LetIn; len.
      set (ctx := subst_context _ _ _).
      assert (assumption_context ctx).
      eapply assumption_context_fold, assumption_context_firstn, smash_context_assumption_context; constructor.
      assert (#|ctx| > 0).
      { rewrite /ctx; len; rewrite firstn_length_le. len; lia. lia. }
      destruct ctx as [|ctx [na [b|] ty]] using rev_case. simpl in H0; lia.
      exfalso; move/assumption_context_app: H => [ass assd]; depelim assd.
      move/assumption_context_app: H => [ass assd]; depelim assd.
      rewrite it_mkProd_or_LetIn_app /mkProd_or_LetIn /= => cum.
      exact (prod_not_below_axiomE hd hb hnop cum).
    + move=> [hargs ccum'].
      rewrite expand_lets_mkApps subst_mkApps /= in ccum'.
      exact (ind_not_below_axiomE hd hb hnop ccum').
  - (* a literal: of this type it is excluded, of another type its constant differs *)
    exfalso.
    eapply inversion_PrimE in typ as (prim_ty & cdecl & [? hpc hdecl' hinv' ? w]); tea.
    destruct p as [? []]; cbn in hnl; try discriminate hnl;
      destruct hinv' as [? hb' ?]; simp prim_type in w.
    + (* float *)
      pose proof (axiom_below_axiomE (args := []) hdecl' hb'
                    (prim_op_of_primitive_constant _ _ _ wfr hpc) hd hb hnop w) as e.
      subst prim_ty.
      pose proof (PCUICPrimCanonical.primitive_constant_inj _ _ _ wfr hpc hkn) as et. cbn in et.
      destruct htag as [-> | ->]; discriminate et.
    + (* array *)
      pose proof (axiom_below_axiomE (args := [_]) hdecl' hb'
                    (prim_op_of_primitive_constant _ _ _ wfr hpc) hd hb hnop w) as e.
      subst prim_ty.
      pose proof (PCUICPrimCanonical.primitive_constant_inj _ _ _ wfr hpc hkn) as et. cbn in et.
      destruct htag as [-> | ->]; discriminate et.
  - (* unsaturated operation: a product type *) exfalso.
    destruct (prim_app_typing_invE e1 typ (Nat.lt_le_incl _ _ l)) as [_ hprod].
    destruct (hprod l) as (na & A & B & hle).
    exact (prod_not_below_axiomE hd hb hnop hle).
  - (* rigid operation: stuck on its blocking argument, by induction *)
    eapply whne_primapp_stuck; eauto.
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    destruct (prim_app_typing_invE e1 typ hle) as [hargs _].
    destruct (nth_error (po_args (info op)) #|ls|) as [tag'|] eqn:htag'.
    2:{ apply nth_error_None in htag'. rewrite /arity in e2. lia. }
    have hnth : nth_error (map term_of_lit ls ++ a :: rest) #|ls| = Some a.
    { rewrite nth_error_app2; len => //. rewrite Nat.sub_diag //. }
    destruct (hargs _ _ _ hnth htag') as (kn' & hkn' & hta).
    pose proof (validityE typ) as isT.
    eapply inversion_mkApps_directE in typ as (A0 & s0 & hc & _ & _); tea.
    eapply inversion_ConstE in hc as (decl0 & wfΓ0 & hdecl0 & cu0 & hle0); tea.
    destruct (prim_op_head_typeE wfΓ0 hdecl0 cu0 e1 hle0) as (res & Tp & [_ _ _ _ hdeclared]).
    eapply All_nth_error in hdeclared; tea.
    destruct hdeclared as (kn'' & d'' & [hkn'' hd'' hinv'']).
    rewrite hkn' in hkn''. noconf hkn''.
    eapply (IHhw tag' kn' d'' [] hkn' hd'' hinv'' (PCUICPrimCanonical.prim_op_args_int_or_string htag') hta).
    assumption.
Qed.

(** ** Base [prim_rigid_arg_whne] ([PCUICSafeReduce.v:177]) *)

Lemma prim_rigid_arg_whneE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} flags {Γ c u op ls a rest T} :
  prim_op_of Σ c = Some op -> #|ls| + S #|rest| = arity op ->
  whnf flags Σ Γ a -> lit_of_term a = None ->
  Σ ;;; Γ |-E mkApps (tConst c u) (map term_of_lit ls ++ a :: rest) : T ->
  whne flags Σ Γ a.
Proof.
  intros hop hlen hwa hnl typ.
  assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
    by (rewrite length_app length_map; cbn; lia).
  destruct (prim_app_typing_invE hop typ hle) as [hargs _].
  destruct (nth_error (po_args (info op)) #|ls|) as [tag|] eqn:htag.
  2:{ apply nth_error_None in htag. unfold arity in hlen. lia. }
  assert (hnth : nth_error (map term_of_lit ls ++ a :: rest) #|ls| = Some a).
  { rewrite nth_error_app2; len => //. rewrite Nat.sub_diag //. }
  destruct (hargs _ _ _ hnth htag) as (kn & hkn & hta).
  pose proof (validityE typ) as isT.
  eapply inversion_mkApps_directE in typ as (A0 & s0 & hc & _ & _); tea.
  eapply inversion_ConstE in hc as (decl0 & wfΓ0 & hdecl0 & cu0 & hle0); tea.
  destruct (prim_op_head_typeE wfΓ0 hdecl0 cu0 hop hle0) as (res & Tp & [_ _ _ _ hdeclared]).
  eapply All_nth_error in hdeclared; [|exact htag].
  destruct hdeclared as (kn' & d' & [hkn' hd' hinv']).
  rewrite hkn in hkn'. noconf hkn'.
  exact (whnf_prim_type_canonicalE flags hkn hd' hinv'
           (PCUICPrimCanonical.prim_op_args_int_or_string htag) hwa hta hnl).
Qed.

(** ** Rows 48-50: base [PCUICSafeReduce.v:1638-1813] *)

(** Base [isCoFix_app] ([PCUICSafeReduce.v:1684]), untyped; same body. The prefix keeps it apart from
    base's name, which this file does not import. *)
Definition dsc_isCoFix_app t :=
  match (decompose_app t).1 with
  | tCoFix _ _ => true
  | _ => false
  end.

(** Base [whnf_non_ctor_finite_ind_typed] ([:1638]). *)
Lemma whnf_non_ctor_finite_ind_typedE {cf} flags Σ Γ t ind u args :
  wfE Σ ->
  whnf flags Σ Γ t ->
  isConstruct_app t = false ->
  check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite = false ->
  Σ ;;; Γ |-E t : mkApps (tInd ind u) args ->
  whne flags Σ Γ t.
Proof.
  intros wf wh ctor fin typ.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wf).
  destruct wh.
  - easy.
  - apply inversion_SortE in typ as (?&?&?); auto.
    exfalso; eapply invert_cumul_sort_indE; eauto.
  - apply inversion_ProdE in typ as (?&?&?&?&?); auto.
    exfalso; eapply invert_cumul_sort_indE; eauto.
  - apply inversion_LambdaE in typ as (?&?&?&?); auto.
    exfalso; eapply invert_cumul_prod_indE; eauto.
  - unfold isConstruct_app in ctor.
    now rewrite decompose_app_mkApps in ctor.
  - exfalso; eapply invert_ind_indE; eauto.
  - exfalso; eapply invert_fix_indE; eauto.
    unfold unfold_fix. destruct o as [[? [-> ?]] | ->]; eauto.
  - apply typing_cofix_coindE in typ; auto.
    unfold is_true in typ.
    unfold PCUICAst.PCUICEnvironment.fst_ctx in *.
    congruence.
  - eapply inversion_PrimE in typ as (prim_ty & cdecl & [? hpc hdecl hinv ? w]); tea.
    pose proof wf as (_ & wfr & _).
    exfalso. eapply (invert_cumul_prim_type_indE hdecl hinv); [|exact w].
    exact (prim_op_of_primitive_constant Σ _ _ wfr hpc).
  (* An unsaturated operation has a product type, never an inductive one. *)
  - exfalso.
    match goal with
    | hop : prim_op_of _ _ = Some _, hlt : #|?l| < arity _ |- _ =>
      destruct (prim_app_typing_invE (wfΣ := wf) hop typ (Nat.lt_le_incl _ _ hlt))
        as [_ hprod];
      destruct (hprod hlt) as (na & A & B & hle);
      exact (invert_cumul_prod_indE hle)
    end.
  (* A rigid application: its blocking argument is neutral ([whnf_prim_type_canonicalE]). *)
  - eapply whne_primapp_stuck; try eassumption.
    eapply (prim_rigid_arg_whneE (wfΣ := wf)); eassumption.
Qed.

(** Base [whnf_non_ctor_non_cofix_ind_typed] ([:1690]). *)
Lemma whnf_non_ctor_non_cofix_ind_typedE {cf} flags Σ Γ t ind u args :
  wfE Σ ->
  whnf flags Σ Γ t ->
  isConstruct_app t = false ->
  dsc_isCoFix_app t = false ->
  Σ ;;; Γ |-E t : mkApps (tInd ind u) args ->
  whne flags Σ Γ t.
Proof.
  intros wf wh ctor cof typ.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wf).
  destruct wh.
  - easy.
  - apply inversion_SortE in typ as (?&?&?); auto.
    exfalso; eapply invert_cumul_sort_indE; eauto.
  - apply inversion_ProdE in typ as (?&?&?&?&?); auto.
    exfalso; eapply invert_cumul_sort_indE; eauto.
  - apply inversion_LambdaE in typ as (?&?&?&?); auto.
    exfalso; eapply invert_cumul_prod_indE; eauto.
  - unfold isConstruct_app in ctor.
    now rewrite decompose_app_mkApps in ctor.
  - exfalso; eapply invert_ind_indE; eauto.
  - exfalso; eapply invert_fix_indE; eauto.
    unfold unfold_fix. destruct o as [[? [-> ?]] | ->]; eauto.
  - unfold dsc_isCoFix_app in cof.
    now rewrite decompose_app_mkApps in cof.
  - eapply inversion_PrimE in typ as (prim_ty & cdecl & [? hpc hdecl hinv ? w]); tea.
    pose proof wf as (_ & wfr & _).
    exfalso. eapply (invert_cumul_prim_type_indE hdecl hinv); [|exact w].
    exact (prim_op_of_primitive_constant Σ _ _ wfr hpc).
  (* An unsaturated operation has a product type, never an inductive one. *)
  - exfalso.
    match goal with
    | hop : prim_op_of _ _ = Some _, hlt : #|?l| < arity _ |- _ =>
      destruct (prim_app_typing_invE (wfΣ := wf) hop typ (Nat.lt_le_incl _ _ hlt))
        as [_ hprod];
      destruct (hprod hlt) as (na & A & B & hle);
      exact (invert_cumul_prod_indE hle)
    end.
  (* A rigid application is stuck on its blocking argument. *)
  - eapply whne_primapp_stuck; try eassumption.
    eapply (prim_rigid_arg_whneE (wfΣ := wf)); eassumption.
Qed.

(** Base [whnf_fix_arg_whne] ([:1732]). *)
Lemma whnf_fix_arg_whneE {cf} flags mfix idx body Σ Γ t before args aftr ty :
  wfE Σ ->
  unfold_fix mfix idx = Some (#|before|, body) ->
  match t with
  | tConstruct _ _ _ => False
  | tApp _ _ => False
  | _ => True
  end ->
  whnf flags Σ Γ (mkApps t args) ->
  Σ ;;; Γ |-E mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr) : ty ->
  whne flags Σ Γ (mkApps t args).
Proof.
  intros wf uf shape wh typ.
  apply inversion_mkAppsE in typ as (fix_ty & typ_fix & typ_args); auto.
  apply inversion_FixE in typ_fix as (def&f&e&a&a0&i&w); auto.
  eapply All_nth_error in a; eauto.
  apply isTypeRelE_isTypeE in a.
  (* Base's [eapply wf_fixpoint_spine in i; eauto. 2: { eapply typing_spine_strengthen; eauto. }],
     with every argument given. *)
  have sp : PCUICAritiesEta.typing_spineE Σ Γ (dtype def) (before ++ mkApps t args :: aftr) ty.
  { eapply typing_spine_strengthenE; [exact typ_args|exact a|exact w]. }
  pose proof (wf_fixpoint_spineE wf Γ mfix idx def _ _ i e a sp) as hs.
  unfold unfold_fix in uf.
  rewrite e in uf.
  rewrite (nth_error_snoc before (mkApps t args) aftr (rarg def) ltac:(congruence)) in hs.
  destruct hs as (?&?&?&typ&fin).
  eapply whnf_non_ctor_finite_ind_typedE; try eassumption.
  - unfold isConstruct_app.
    rewrite (decompose_app_mkApps t args ltac:(now destruct t)).
    cbn.
    now destruct t.
  - destruct check_recursivity_kind eqn:cofin in |- *; [|easy].
    (* base's [check_recursivity_kind_inj] takes [wf Σ] (its section's [Type*]); the E twin takes [wfE Σ] *)
    eapply (check_recursivity_kind_injE (wfΣ := wf)) in fin; [|exact cofin].
    congruence.
Qed.

(** Base [whnf_case_arg_whne] ([:1765]). *)
Lemma whnf_case_arg_whneE {cf} flags Σ Γ hd args ci p brs T :
  wfE Σ ->
  match hd with
  | tApp _ _
  | tConstruct _ _ _
  | tCoFix _ _ => False
  | _ => True
  end ->
  whnf flags Σ Γ (mkApps hd args) ->
  Σ;;; Γ |-E tCase ci p (mkApps hd args) brs : T ->
  whne flags Σ Γ (mkApps hd args).
Proof.
  intros wf shape wh typ.
  apply inversion_CaseE in typ as (?&?&isdecl&?&[]&?); auto.
  eapply whnf_non_ctor_non_cofix_ind_typedE; try eassumption.
  - unfold isConstruct_app.
    now rewrite decompose_app_mkApps; destruct hd.
  - unfold dsc_isCoFix_app.
    now rewrite decompose_app_mkApps; destruct hd.
Qed.

(** Base [whnf_proj_arg_whne] ([:1786]); base's [PCUICInductiveInversion.invert_Proj_Construct] is copy
    18b's [invert_Proj_ConstructE]. *)
Lemma whnf_proj_arg_whneE {cf} flags Σ Γ hd args p T :
  wfE Σ ->
  match hd with
  | tApp _ _
  | tCoFix _ _ => False
  | tConstruct _ c _ => c <> 0
  | _ => True
  end ->
  whnf flags Σ Γ (mkApps hd args) ->
  Σ ;;; Γ |-E tProj p (mkApps hd args) : T ->
  whne flags Σ Γ (mkApps hd args).
Proof.
  intros wf shape wh typ.
  assert (typ' := typ).
  apply inversion_ProjE in typ as (?&?&?&?&?&?&?&?&?); auto.
  cbn in *.
  eapply whnf_non_ctor_non_cofix_ind_typedE; try eassumption.
  - unfold isConstruct_app.
    rewrite (decompose_app_mkApps hd args ltac:(now destruct hd)).
    cbn.
    destruct hd; try easy.
    destruct p as [].
    eapply PCUICInductiveInversionEtaB.invert_Proj_ConstructE in typ' as (?&?&?); auto.
    2: sq; eapply wf.
    congruence.
  - unfold dsc_isCoFix_app.
    now rewrite decompose_app_mkApps; destruct hd.
Qed.
