(* Distributed under the terms of the MIT license. *)

(** * Principality over the η relations (plan row T2b): the E copy of [PCUICPrincipality]

  A copy of base [PCUICPrincipality.v] over [typingE]: [typing] → [typingE], [wf_ext] → [wf_extE],
  [wf] → [wfE], [isWfArity] → [isWfArityE], [Σ ;;; Γ ⊢ _ ≤ _] → [⊢E], [ws_cumul_pb_terms] →
  [ws_cumul_pbE_terms]; each name takes the suffix [E]. Base's imports of [PCUICClassification]
  and [PCUICCumulProp] are dropped (no name of either is used). The six syntactic lemmas of base
  (:391-441) are used from base, qualified ([Require PCUICPrincipality]).

  Typed T8 at base's five raw sites ([Sort] :98-117, [Prod] :132 and :152-161, [Case] :226-238,
  [Proj] :261-278, [principal_type_ind] :376-380): [BDFromPCUICEta.T8_*_r_plug] (the proved
  [PCUICEtaT8Probe.T8_*_r_two] with [subject_reductionE]) and [T8_Prod_l_plug] (from [Prod_r] by
  [T8_Prod_l_of_r], copied below from the inventory sweep); the premise [T : tSort s'] comes from
  [validityE] at each site. The [Ind_r] universe clause is read at full application
  ([finst_ind_glue_full], [isTypeE_mkApps_Ind_head_arity]).

  [typing_leq_term] (:741) needs NO Axiom-shaped T8 form: the landed canonical-form
  [ws_cumul_pbE_Axiom_l_inv] and [chain_ws_cumul_pbE_Conv] give the needed E conversion with no
  typing premise; it is copied ([typing_leq_termE], [typing_eq_termE]).

  Forecast classes (imported, never redefined): [ValForecastCopy16], [SRForecastCopy16],
  [SRForecastCopy18], [BDFromForecastCopy18]. Instances: [PCUICPrincipalityEtaInstances].

  One home for shared helpers: [closed_red_confluence_cb] and [invert_red_sort_cb] are used by
  [Bidirectional/BDUniqueEta], [chain_ws_cumul_pbE_Conv] and [T8_Prod_l_plug] by
  [PCUICClassificationEta]; both require this file without importing it and write the names
  qualified. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnvTyp PCUICSubstitution PCUICEquality
     PCUICReduction PCUICCumulativity PCUICConfluence PCUICClosed PCUICClosedTyp
     PCUICContextConversion PCUICContextConversionTyp PCUICConversion PCUICInversion PCUICUnivSubst
     PCUICArities PCUICValidity PCUICInductives PCUICInductiveInversion
     PCUICSR PCUICWfUniverses
     PCUICOnFreeVars PCUICWellScopedCumulativity.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningEnvTypEta
     PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICEtaC1aR PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaFInstGlue
     PCUICEtaI5 PCUICEtaI5A2 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICEtaA6 PCUICEtaA6Ind PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICInversionEta PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta
     PCUICValidityEta PCUICSREtaConv PCUICSREta BDTypingEta BDToPCUICEta BDFromPCUICEta.
From MetaRocq.PCUIC Require Import PCUICWsCumulEtaInstancesGlobal.
From MetaRocq.PCUIC.Typing Require Import PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require PCUICGenerationEta PCUICEtaT8Probe PCUICPrincipality.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** Untyped reduction facts under [ClosedBodies] *)

(** Base [closed_red_confluence] ([PCUICContextConversion.v:528]), under [ClosedBodies Σ] in
    place of [wf Σ]: base's proof with [red_confluence_cb]. *)
Lemma closed_red_confluence_cb {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ} {t u v} :
  Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v ->
  ∑ v', Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v'.
Proof.
  intros [clΓ clT r] [clΓ' clT' r'].
  destruct (red_confluence_cb (Γ := exist Γ clΓ) (t := exist t clT) r r') as [v' [redl redr]].
  cbn in *. exists v'; split; split; auto.
  - exact (red_is_open_term_cb _ _ r clΓ clT).
  - exact (red_is_open_term_cb _ _ r' clΓ clT).
Qed.

(** Base [invert_red_sort] ([PCUICConversion.v:1119]); base's [wf Σ] is not needed: a sort has
    no one-step reduct. *)
Lemma invert_red_sort_cb {cf} {Σ : global_env_ext} Γ u v :
  Σ ;;; Γ ⊢ (tSort u) ⇝ v -> v = tSort u.
Proof.
  intros [_ _ H]. remember (tSort u) as x eqn:e.
  induction H in e |- *.
  - subst. depelim r; solve_discr.
  - now subst.
  - specialize (IHclos_refl_trans1 e). subst. now apply IHclos_refl_trans2.
Qed.

(** ** Typed T8, proved (row B1)

  [Sort_r], [Prod_r] and [Ind_r] are [BDFromPCUICEta.T8_*_r_plug]: the proved two-hypothesis
  theorems [PCUICEtaT8Probe.T8_*_r_two] with [subject_reduction] discharged by
  [PCUICSREta.subject_reductionE]. [Prod_l] is derived from [Prod_r] by the proof of
  [T8_Prod_l_of_r] on [fork/wip/eta-meta-invsweep-2026-10-29] @ [f54375b2]
  ([pcuic/theories/PCUICEtaInventorySweep.v:1262-1300]), copied here with its helper
  [chain_ws_cumul_pbE_Conv] because that file does not land. *)

(** A chain from [canon T] to [H] is an E conversion of [T] and [H]. *)
Lemma chain_ws_cumul_pbE_Conv {cf : checker_flags} {Σ : global_env_ext} {cb : ClosedBodies Σ} Γ T H :
  is_closed_context Γ -> is_open_term Γ T ->
  Equations.Type.Relation.clos_refl_trans (Equations.Type.Relation.union (R_c Σ Γ) eta1) (canon T) H -> ws_cumul_pbE Conv Σ Γ T H.
Proof.
  intros hΓ hT hch.
  have hcan : canon H = H := chain_canonical (Σ := Σ) Γ (canon T) H (canon_idem T) hch.
  constructor; [exact hΓ|exact hT|exact (chain_open (Σ := Σ) (wfΣ := cb) Γ T H hΓ hT hch)|].
  exists H, H. split; [exact hch|split; [rewrite hcan; apply Equations.Type.Relation.rt_refl|apply compare_term_eta_refl]].
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

Section PrincipalityEta.

(* FORECAST-ONLY: the classes of the lemmas used here, imported, never redefined: T2a's
   [ValForecastCopy16] ([PCUICValidityEta]), T1's [SRForecastCopy16]/[SRForecastCopy18]
   ([PCUICSREta]) and copy 18's [projection_cumulative_indicesE] ([BDFromForecastCopy18],
   [Bidirectional/BDFromPCUICEta]); delete each when its row lands. *)
Context {V16 : ValForecastCopy16} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}
  {BF18 : BDFromForecastCopy18}.

(** [Prod_l], from the proved [Prod_r] ([T8_Prod_r_plug]) by [T8_Prod_l_of_r]. Its type is the
    body of the pinned [PCUICEtaT8Probe.T8_Prod_l_statement] (:144-151) under
    [forall (cf : checker_flags) (Σ : global_env_ext),], verbatim; [T8_Prod_l_plug_fit] checks
    it against the [Definition]. *)
Definition T8_Prod_l_plug :
    forall (cf : checker_flags) (Σ : global_env_ext),
    forall Γ pb T na dom codom s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ (tProd na dom codom) T ->
      ∑ na' dom' codom',
        [× Σ ;;; Γ ⊢ T ⇝ tProd na' dom' codom', eq_binder_annot na na',
           ws_cumul_pbE Conv Σ Γ dom dom' &
           ws_cumul_pbE pb Σ (Γ ,, vass na dom) codom codom'] :=
  fun cf Σ => T8_Prod_l_of_r Σ (T8_Prod_r_plug cf Σ).

Definition T8_Prod_l_plug_fit (cf : checker_flags) (Σ : global_env_ext) :
  @PCUICEtaT8Probe.T8_Prod_l_statement cf Σ := T8_Prod_l_plug cf Σ.

#[local] Hint Resolve has_sort_isTypeE typingE_wf_local : pcuic.
#[local] Hint Immediate typing_closed_contextE : fvs.

Section Principality.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf_extE Σ).

  Ltac pih :=
    lazymatch goal with
    | ih : forall _ _ _, _ -> _ ;;; _ |-E ?u : _ -> _,
    h1 : _ ;;; _ |-E ?u : _,
    h2 : _ ;;; _ |-E ?u : _
    |- _ =>
  specialize (ih _ _ _ h1 h2)
  end.

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  (** Base [isWfArity_sort] ([PCUICPrincipality.v:61]). *)
  Lemma isWfArity_sortE Γ u :
    wf_localE Σ Γ ->
    wf_sort Σ u ->
    isWfArityE Σ Γ (tSort u).
  Proof using Type.
    move=> wfΓ wfu.
    split. eapply isType_SortE; eauto. exists [], u. intuition auto.
  Qed.
  Hint Extern 10 (isWfArityE _ _ (tSort _)) => apply isWfArity_sortE : pcuic.

  Ltac int inv := intros B hB; eapply inv in hB; auto; split; [|econstructor; eauto].

  (** Base [principal_type] ([PCUICPrincipality.v:74]). *)
  Theorem principal_typeE {Γ u A} : Σ ;;; Γ |-E u : A ->
    ∑ C, (forall B, Σ ;;; Γ |-E u : B -> Σ ;;; Γ ⊢E C ≤ B × Σ ;;; Γ |-E u : C).
  Proof.
    intros hA. have wfΣ' : wfE Σ := wfΣ.1. have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ.
    induction u in Γ, A, hA |- * using term_forall_list_ind.
    - apply inversion_RelE in hA as iA. 2: auto.
      destruct iA as [decl [? [e ?]]].
      eexists; int inversion_RelE.
      destruct hB as [decl' [? [e' ?]]].
      rewrite e' in e. noconf e.
      all: try eassumption.
    - apply inversion_VarE in hA. destruct hA.
    - apply inversion_EvarE in hA. destruct hA.
    - apply inversion_SortE in hA as iA. 2: auto.
      repeat outsum. repeat outtimes. subst.
      exists (tSort (Sort.super s)).
      int inversion_SortE.
      repeat outsum. repeat outtimes. now subst.
    - apply inversion_ProdE in hA as (dom1 & codom1 & t & t0 & w); auto.
      pose proof (t.2.π2.2.p2) as Her. rewrite -t.2.π2.2.p1 /= in Her.
      apply unlift_TypUniv in t.
      specialize (IHu1 _ _ t) as [dom Hdom].
      specialize (IHu2 _ _ t0) as [codom Hcodom].
      destruct (Hdom _ t) as [e e'].
      (* T8 [Sort_r] (base: [ws_cumul_pb_Sort_r_inv]); [dom : tSort _] by validity of [e']. *)
      destruct (validityE e') as (_ & sd & hsd & _).
      destruct (T8_Sort_r_plug _ Σ _ _ _ _ _ wfΣ' hsd e) as [domu [red leq]]. clear e hsd.
      destruct (Hcodom _ t0) as [e e''].
      destruct (validityE e'') as (_ & sc & hsc & _).
      destruct (T8_Sort_r_plug _ Σ _ _ _ _ _ wfΣ' hsc e) as [codomu [cored coleq]]. clear e hsc.
      exists (tSort (Sort.sort_of_product domu codomu)).
      int inversion_ProdE.
      destruct hB as (x & x0 & t1 & t2 & w0).
      apply unlift_TypUniv in t1.
      + etransitivity. 1: auto. 2:eapply w0.
        destruct (Hdom _ t1) as [le' u1'].
        destruct (validityE u1') as (_ & sd' & hsd' & _).
        destruct (T8_Sort_r_plug _ Σ _ _ _ _ _ wfΣ' hsd' le') as [u' [redu' leu']]. clear le' hsd'.
        destruct (Hcodom _ t2) as [le'' u2'].
        destruct (validityE u2') as (_ & sc' & hsc' & _).
        destruct (T8_Sort_r_plug _ Σ _ _ _ _ _ wfΣ' hsc' le'') as [u'' [redu'' leu'']]. clear le'' hsc'.
        apply ws_cumul_pbE_Sort; [exact (typing_closed_contextE e')|].
        apply leq_sort_product_mon; auto.
        pose proof (closed_red_confluence_cb red redu') as [v' [redl redr]].
        eapply invert_red_sort_cb in redl.
        eapply invert_red_sort_cb in redr. subst. now noconf redr.
        pose proof (closed_red_confluence_cb cored redu'') as [v' [redl redr]].
        eapply invert_red_sort_cb in redl.
        eapply invert_red_sort_cb in redr. subst. now noconf redr.
      + repeat (eexists; eauto).
        2: eapply geq_relevance, Her; tea.
        eapply type_reductionE; eauto. eapply red.
      + eapply type_reductionE; eauto. eapply cored.

    - apply inversion_LambdaE in hA => //; eauto.
      destruct hA as (x & H & t & w).
      destruct (IHu2 _ _ t) as [x0 p].
      destruct (p _ t).
      exists (tProd n u1 x0).
      (* base: [int inversion_Lambda]. T8 [Prod_l] below needs [B : tSort _], so the E script
         first keeps it, by validity of [hB]. *)
      intros B hB. pose proof (validityE hB) as (_ & sB & hsB & _).
      eapply inversion_LambdaE in hB; auto; split; [|econstructor; eauto].
      destruct hB as (x1 & _ & t1 & w1).
      repeat outsum. repeat outtimes.
      etransitivity; eauto.
      (* T8 [Prod_l] (base: [ws_cumul_pb_Prod_l_inv]). *)
      destruct (T8_Prod_l_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsB w1) as [na' [A' [B' [redA eqna u1eq hcod]]]].
      destruct (p _ t1).
      eapply ws_cumul_pbE_Prod => //; auto.
      transitivity A' => //. now symmetry.

    - eapply inversion_LetInE in hA as (bty & Hu12 & Hu3 & Hcum); auto.
      destruct (IHu3 _ _ Hu3) as [u3' p3].
      destruct (p3 _ Hu3).
      exists (tLetIn n u1 u2 u3').
      int inversion_LetInE.
      destruct hB as (bty' & Hu12' & Hu3' & Hcum'); eauto.
      etransitivity; eauto.
      (* Base [ws_cumul_pb_LetIn] keeps [pb] on the body; its E twin is the A7
         [ws_cumul_pbE_LetIn_pb] (the A5 [ws_cumul_pbE_LetIn] is at [Conv] on the body). *)
      eapply ws_cumul_pbE_LetIn_pb; eauto.
      1,2: destruct Hu12 as (? & ? & ? & _); cbn in *; now eapply wt_cumul_pb_reflE.
      now specialize (p3 _ Hu3') as [? ?].

    - eapply inversion_AppE in hA as [na [dom [codom [tydom [tyarg tycodom]]]]] => //; auto.
      destruct (IHu2 _ _ tyarg).
      destruct (IHu1 _ _ tydom).
      destruct (p _ tyarg) as [w t]. destruct (p0 _ tydom) as [w0 t0].
      (* T8 [Prod_r] (base: [ws_cumul_pb_Prod_r_inv]); [x0 : tSort _] by validity of [t0]. *)
      destruct (validityE t0) as (_ & sx & hsx & _).
      destruct (T8_Prod_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsx w0) as [x1 [A' [B' [redA eqann u1eq hB']]]].
      clear w0 hsx.
      exists (subst [u2] 0 B').
      intros ? hB.
      eapply inversion_AppE in hB as [na' [dom' [codom' [tydom' [tyarg' tycodom']]]]] => //; auto.
      destruct (p0 _ tydom') as [w1 t1].
      destruct (p _ tyarg') as [w2 t2].
      destruct (validityE t1) as (_ & sx' & hsx' & _).
      destruct (T8_Prod_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsx' w1) as [x2 [A'' [B'' [redA' eqann' u1eq' hB'']]]].
      clear w1 hsx'.
      destruct (closed_red_confluence_cb redA redA') as [nfprod [redl redr]].
      eapply invert_red_prod_cb in redl as [x3 [x4 [e rA rB]]] => //. subst.
      eapply invert_red_prod_cb in redr as [x5 [x6 [e rA' rB']]] => //. noconf e.
      assert(Σ ;;; Γ ⊢E A' = A'').
      { transitivity x3 => //; eauto using red_ws_cumul_pbE.
        symmetry. now apply red_ws_cumul_pbE. }
      assert(Σ ;;; Γ ,, vass x1 A' ⊢E B' = B'').
      { transitivity x4 => //.
        - now eapply red_ws_cumul_pbE.
        - symmetry. eapply ws_cumul_pbE_ws_cumul_ctx.
          2:eapply red_ws_cumul_pbE; tea.
          eapply ws_cumul_ctx_pbE_vass; [exact (typing_closed_contextE t1)|reflexivity|now symmetry]. }
      split.
      etransitivity; [|exact tycodom'].
      eapply (substitution0_ws_cumul_pbE (na:=na') (T:=dom')).
      { exact (subject_is_open_termE tyarg'). }
      have convctx : ws_cumul_ctx_pbE Conv Σ (Γ ,, vass x1 A') (Γ ,, vass na' dom').
      { eapply ws_cumul_ctx_pbE_vass; [exact (typing_closed_contextE t1)|now apply eq_binder_annot_sym|].
        transitivity A'' => //. }
      transitivity B''.
      { eapply ws_cumul_pbE_ws_cumul_ctx; tea. now apply ws_cumul_pbE_eq_le. }
      exact hB''.
      eapply type_App'E.
      eapply type_reductionE; eauto. eapply redA.
      eapply (type_ws_cumul_pbE (pb:=Cumul)); eauto.
      { eapply validityE in t0; auto.
        eapply isType_redE in t0; [|exact redA].
        eapply isTypeRelE_isTypeE.
        eapply isType_tProdE in t0 as [? ?]; eauto. }
      transitivity dom' => //. transitivity A''.
      all:apply ws_cumul_pbE_eq_le; symmetry => //.

    - eapply inversion_ConstE in hA as [decl ?] => //; auto.
      repeat outtimes.
      eexists; int inversion_ConstE.
      destruct hB as [decl' [wf [declc' [cu cum]]]].
      unshelve epose proof (d_ := declared_constant_to_gen d); eauto.
      unshelve epose proof (declc'_ := declared_constant_to_gen declc'); eauto.
      now rewrite -(declared_constant_inj _ _ d_ declc'_) in cum.

    - eapply inversion_IndE in hA as [mdecl [idecl [? [Hdecl ?]]]] => //; auto.
      repeat outtimes.
      exists (subst_instance u (ind_type idecl)).
      int inversion_IndE. destruct hB as [mdecl' [idecl' [? [Hdecl' ?]]]] => //.
      unshelve eapply declared_inductive_to_gen in Hdecl, Hdecl'; eauto.
      red in Hdecl, Hdecl'. destruct Hdecl as [? ?].
      destruct Hdecl' as [? ?]. red in H, H1.
      rewrite H1 in H; noconf H.
      rewrite H2 in H0; noconf H0.
      repeat intimes; eauto. now destruct p.

    - eapply inversion_ConstructE in hA as [mdecl [idecl [? [? [Hdecl ?]]]]] => //; auto.
      repeat outtimes.
      exists (type_of_constructor mdecl x (i, n) u).
      int inversion_ConstructE. destruct hB as [mdecl' [idecl' [? [? [Hdecl' [? ?]]]]]] => //.
      unshelve eapply declared_constructor_to_gen in Hdecl, Hdecl'; eauto.
      red in Hdecl, Hdecl'.
      destruct Hdecl as [[? ?] ?].
      destruct Hdecl' as [[? ?] ?].
      red in H, H2. rewrite H2 in H. noconf H.
      rewrite H3 in H0. noconf H0.
      rewrite H4 in H1. now noconf H1.

    - assert (wfE Σ) by auto.
      eapply inversion_CaseE in hA as (mdecl&idecl&isdecl&indices&[]&?); auto.
      destruct (IHu _ _ scrut_ty) as [? p0].
      destruct (p0 _ scrut_ty) as [w0 tsc].
      (* T8 [Ind_r] (base: [ws_cumul_pb_Ind_r_inv]); [x : tSort _] by validity of [tsc]. *)
      destruct (validityE tsc) as (_ & sx & hsx & _).
      destruct (T8_Ind_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsx w0) as [u' [x0' [redr redu hargs]]].
      clear w0 hsx.
      (* [ws_cumul_pbE] is a one-constructor record, so base's [repeat split] would open it. *)
      exists (mkApps ptm (indices ++ [u])); intros b hB; split; auto.
      2:econstructor; eauto.
      eapply inversion_CaseE in hB as (mdecl'&idecl'&isdecl'&indices'&[]&?); tea. clear brs_ty0.
      unshelve eapply declared_inductive_to_gen in isdecl, isdecl'; eauto.
      destruct (declared_inductive_inj isdecl isdecl') as [-> ->].
      destruct (p0 _ scrut_ty0) as [w1 tsc'].
      destruct (validityE tsc') as (_ & sx' & hsx' & _).
      destruct (T8_Ind_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsx' w1) as [u'' [x9' [redr' redu' hargs']]].
      clear w1 hsx'.
      assert (hx : ws_cumul_pbE_terms Σ Γ x0' x9').
      { destruct (closed_red_confluence_cb redr redr') as [nf [r r0]].
        eapply invert_red_mkApps_tInd_cb in r as [args' [? ? a1]]; auto.
        eapply invert_red_mkApps_tInd_cb in r0 as [args'' [? ? a2]]; auto.
        subst. solve_discr.
        transitivity args'; auto using red_terms_ws_cumul_pbE_terms.
        now symmetry; apply red_terms_ws_cumul_pbE_terms. }
      clear redr redr'.
      etransitivity; [|tea].
      eapply ws_cumul_pbE_mkApps; auto. rewrite /ptm /predctx.
      * eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE in pret_ty.
        eapply ws_cumul_pbE_eq_le, wt_cumul_pb_reflE. eapply pret_ty.
      * unfold ws_cumul_pbE_terms. eapply All2_app. 2:constructor; auto.
        assert (hpi : ws_cumul_pbE_terms Σ Γ (pparams p ++ indices) (pparams p ++ indices')).
        { transitivity x9'; tea. transitivity x0' => //. now symmetry. }
        eapply All2_app_inv in hpi as [] => //.
        eapply wt_cumul_pb_reflE; tea.
      * split; eauto.
      * split; eauto.

    - destruct s as [ind k pars]; simpl in *.
      eapply inversion_ProjE in hA=>//; auto.
      repeat outsum. repeat outtimes.
      simpl in *.
      specialize (IHu _ _ t) as [C HP].
      destruct (HP _ t) as [w0 t0].
      (* T8 [Ind_r] (base: [ws_cumul_pb_Ind_r_inv]); [C : tSort _] by validity of [t0]. *)
      destruct (validityE t0) as (_ & sC & hsC & _).
      destruct (T8_Ind_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsC w0) as [u' [x0' [redr redu hargs]]].
      clear w0 hsC.
      exists (subst0 (u :: List.rev x0') (subst_instance u' (proj_type x3))).
      intros B hB.
      eapply inversion_ProjE in hB=>//; auto.
      repeat outsum. repeat outtimes.
      simpl in *.
      unshelve epose proof (d_ := declared_projection_to_gen d); eauto.
      unshelve epose proof (d0_ := declared_projection_to_gen d0); eauto.
      destruct (declared_projection_inj d_ d0_) as [-> [-> [-> ?]]]. subst x9.
      destruct (HP _ t1) as [w1 t2].
      destruct (validityE t2) as (_ & sC' & hsC' & _).
      destruct (T8_Ind_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsC' w1) as [u'' [x0'' [redr' redu' hargs']]].
      clear w1 hsC'.
      split; cycle 1.
      eapply type_reductionE in t0. 2:exact redr.
      eapply (typeE_Proj _ _ _ _ _ _ _ _ _ _ d0); simpl; auto.
      now rewrite (All2_length hargs).
      destruct (closed_red_confluence_cb redr redr') as [nf [redl redr'']].
      eapply invert_red_mkApps_tInd_cb in redl as [? [-> conv]]; auto.
      eapply invert_red_mkApps_tInd_cb in redr'' as [? [[=] conv']]; auto.
      solve_discr.
      etransitivity; eauto.
      (* Route (statement unchanged): base types the two substitutions with
         [projection_subslet] (copy 16) and the projection context with [wf_projection_context];
         here, as in [BDFromPCUICEta]'s Proj case, the substitutions are untyped
         ([untyped_subslet_projection_contextE]), the context is closed by
         [is_closed_projection_contextE], the instances' consistency comes from
         [isType_mkApps_Ind_invE] ([ValForecastCopy16]) in place of base
         [invert_type_mkApps_ind], and base's two steps (the arguments, then the instances) are
         one [substitution_ws_cumul_pbE_subst_conv]. *)
      have decli : declared_inductive Σ ind x6 x7 := MRProd.proj1 (MRProd.proj1 d).
      assert (cu' : consistent_instance_ext Σ (ind_universes x6) u').
      { eapply type_reductionE in t2. 2:eapply redr.
        destruct (isType_mkApps_Ind_invE wfΣ' decli (typingE_wf_local t2) (validityE t2)) as (? & ? & hs).
        cbv zeta in hs. now destruct hs. }
      assert (cu : consistent_instance_ext Σ (ind_universes x6) x5).
      { destruct (isType_mkApps_Ind_invE wfΣ' decli (typingE_wf_local t1) (validityE t1)) as (? & ? & hs).
        cbv zeta in hs. now destruct hs. }
      set (p := {| proj_ind := ind; proj_npars := k; proj_arg := pars |}).
      assert (hx : ws_cumul_pbE_terms Σ Γ x0' x10).
      { transitivity x0'' => //.
        transitivity x0. auto using red_terms_ws_cumul_pbE_terms.
        symmetry. auto using red_terms_ws_cumul_pbE_terms. }
      have hlen' : #|x0'| = ind_npars x6 by rewrite (All2_length hargs).
      pose proof (typing_closed_contextE t1) as clΓ.
      have onud : PCUICWeakeningEnv.on_udecl_prop Σ (ind_universes x6).
      { unshelve eapply declared_projection_to_gen in d ; eauto.
        eapply (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ _ (wfΣ' : wfE _) (MRProd.proj1 (MRProd.proj1 (MRProd.proj1 d)))). }
      (* The universe clause of [Ind_r] at full application ([finst_ind_glue_full]): validity
         types [mkApps (tInd ind x5) x10] at a sort. *)
      pose proof (isTypeE_mkApps_Ind_head_arity (typingE_wf_local t1) (validityE t1)) as harity.
      have hcmp : cmp_ind_universes Σ ind (ind_npars x6) u' x5.
      { rewrite -e0. exact (finst_ind_glue_full Σ.1 _ Cumul ind _ _ _ harity redu'). }
      exact (substitution_ws_cumul_pbE_subst_conv (Δ := [])
        (untyped_subslet_projection_contextE (p := p) u' d hlen')
        (untyped_subslet_projection_contextE (p := p) x5 d e0)
        (All2_cons (ws_cumul_pbE_refl clΓ (subject_is_open_termE t1)) (All2_rev _ _ _ _ _ hx))
        (PCUICInductiveInversion.is_closed_context_weaken _ _ clΓ (is_closed_projection_contextE x5 d))
        (weaken_ws_cumul_pbE Γ clΓ (projection_cumulative_indicesE d onud cu' cu hcmp))).

    - pose proof (typingE_wf_local hA).
      apply inversion_FixE in hA as [decl [hguard [nthe [wfΓ [? [? ?]]]]]]=>//; auto.
      exists (dtype decl).
      intros B hB.
      eapply inversion_FixE in hB as [decl' [hguard' [nthe' [wfΓ' [? [? ?]]]]]]=>//; auto.
      rewrite nthe' in nthe; noconf nthe.
      split; eauto.
      eapply typeE_Fix; eauto.

    - pose proof (typingE_wf_local hA).
      apply inversion_CoFixE in hA as [decl [hguard [nthe [wfΓ [? [? ?]]]]]]=>//; auto.
      exists (dtype decl).
      intros B hB.
      eapply inversion_CoFixE in hB as [decl' [hguard' [nthe' [wfΓ' [? [? ?]]]]]]=>//; auto.
      rewrite nthe' in nthe; noconf nthe.
      split; eauto.
      eapply typeE_CoFix; eauto.
    - apply inversion_PrimE in hA as [prim_ty [cdecl []]] => //; pcuic.
      exists (prim_type p prim_ty).
      intros B hB.
      apply inversion_PrimE in hB as [prim_ty' [cdecl' []]] => //; pcuic.
      econstructor; tea; fvs.
  Qed.

  (** Base [common_typing] ([PCUICPrincipality.v:354]): a weaker version that is often
      convenient to use. *)
  Lemma common_typingE {Γ u A B} : Σ ;;; Γ |-E u : A -> Σ ;;; Γ |-E u : B ->
    ∑ C, Σ ;;; Γ ⊢E C ≤ A × Σ ;;; Γ ⊢E C ≤ B × Σ ;;; Γ |-E u : C.
  Proof.
    intros hA hB.
    destruct (principal_typeE hA) as [P HP]; eauto.
    exists P; split; eauto.
    eapply HP; eauto.
  Qed.

End Principality.

(** Base [principal_type_ind] ([PCUICPrincipality.v:365]). T8 [Ind_r] twice; base's
    [cmp_ind_universes] clause at [#|args|] is T8's [cmp_global_instance_finst] at the full
    application ([finst_ind_glue_full]), since validity types [mkApps (tInd ind u) args] at a
    sort ([isTypeE_mkApps_Ind_head_arity]). *)
Lemma principal_type_indE {cf:checker_flags} {Σ Γ c ind ind' u u' args args'} {wfΣ: wf_extE Σ} :
  Σ ;;; Γ |-E c : mkApps (tInd ind u) args ->
  Σ ;;; Γ |-E c : mkApps (tInd ind' u') args' ->
  (∑ ui',
    cmp_ind_universes Σ ind #|args| ui' u *
    cmp_ind_universes Σ ind' #|args'| ui' u') *
  ws_cumul_pbE_terms Σ Γ args args' *
  (ind = ind').
Proof.
  intros h h'.
  have wfΣ' : wfE Σ := wfΣ.1. have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ.
  destruct (common_typingE _ wfΣ h h') as [C [l [r ty]]].
  destruct (validityE ty) as (_ & sC & hsC & _).
  have wfΓ := typingE_wf_local h.
  pose proof (isTypeE_mkApps_Ind_head_arity wfΓ (validityE h)) as ha.
  pose proof (isTypeE_mkApps_Ind_head_arity wfΓ (validityE h')) as ha'.
  destruct (T8_Ind_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsC l) as [ui' [l' [red Ru eqargs]]].
  destruct (T8_Ind_r_plug _ Σ _ _ _ _ _ _ _ wfΣ' hsC r) as [ui'' [l'' [red' Ru' eqargs']]].
  apply (finst_ind_glue_full Σ.1 _ Cumul ind _ _ _ ha) in Ru.
  apply (finst_ind_glue_full Σ.1 _ Cumul ind' _ _ _ ha') in Ru'.
  destruct (closed_red_confluence_cb red red') as [nf [redl redr]].
  eapply invert_red_mkApps_tInd_cb in redl as [args'' [-> eq0]]; auto.
  eapply invert_red_mkApps_tInd_cb in redr as [args''' [eqnf eq1]]; auto.
  solve_discr.
  repeat split; eauto.
  assert (#|args| = #|args'|).
  now rewrite -(All2_length eqargs) -(All2_length eqargs') (All2_length a) (All2_length a0).
  transitivity l'. now symmetry.
  transitivity args'' => //. now apply red_terms_ws_cumul_pbE_terms.
  transitivity l''. symmetry. auto using red_terms_ws_cumul_pbE_terms.
  now symmetry.
Qed.

(** Base [typing_leq_term] ([PCUICPrincipality.v:445]). The six syntactic lemmas of base's file
    ([eq_term_leq_term] … [eq_context_upto_inst_case_context], :391-441) are used from base,
    qualified. Routes that differ from base (the statement does not):
    - context conversion: base's [context_conversion] over the algorithmic [conv_context] →
      [closed_context_conversionE] (copy 9) over [ws_cumul_ctx_pbE], whose declaration
      comparisons are base's [eq_term] lifted by [ws_cumul_pb_incl_E];
    - the comparisons built from [eq_term]/[leq_term] ([constructor] of base's [ws_cumul_pb] or
      of [cumulAlgo]) → [ws_cumul_pb_incl_E] of [ws_cumul_pb_compare], or
      [eq_term_upto_univ_cumulSpecE] where the typing rule takes the specification;
    - substitutions (App, Construct, Proj): base types them ([subslet], [projection_subslet],
      [wf_arities_context_inst], [wf_projection_context]; the last three are copy 16) → untyped
      ([untyped_subslet_assumption_context], [untyped_subslet_projection_contextE]) with
      [substitution_ws_cumul_pbE_subst_conv];
    - Proj: base's [principal_type_ind] there gives only [#|args| = #|args'|], which the typing
      premise [#|args| = ind_npars mdecl] already gives; it is not called;
    - Prim (:741): base's [ws_cumul_pb_Axiom_l_inv] reads a REDUCT of [T']; over η the landed
      [ws_cumul_pbE_Axiom_l_inv] gives a chain from [canon T'] to the axiom spine, and the site
      needs only [T' =E] the spine, which [chain_ws_cumul_pbE_Conv] gives with no typing
      premise. No T8 form (no [Axiom_l] T8) is used. *)
Lemma typing_leq_termE {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' :
  wfE Σ.1 ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |-E t : T ->
  Σ ;;; Γ |-E t' : T' ->
  leq_term empty_global_env Σ t' t ->
  (* No cumulativity of inductive types, as they can relate
    inductives in different sorts. *)
  Σ ;;; Γ |-E t' : T.
Proof.
  intros wfΣ onu Ht.
  revert Σ wfΣ Γ t T Ht onu t' T'.
  eapply (typingE_ind_env
  (fun Σ Γ t T =>
    forall (onu : on_udecl Σ.1 Σ.2),
    forall t' T' : term, Σ ;;; Γ |-E t' : T' -> leq_term empty_global_env Σ t' t -> Σ;;; Γ |-E t' : T)
  (fun Σ Γ j =>
    on_udecl Σ.1 Σ.2 ->
    lift_typing0 (fun t T =>
      forall t' T' : term, Σ ;;; Γ |-E t' : T' -> leq_term empty_global_env Σ t' t -> Σ;;; Γ |-E t' : T)
    j)
  (fun Σ Γ => wf_localE Σ Γ)).
  { intros ???? H ?; apply lift_typing_impl with (1 := H) => ??[] HT IH //. now apply IH. }
  1: now auto.

  all: intros Σ wfΣ Γ wfΓ; intros.

  1-13:match goal with
    [ H : leq_term _ _ _ _ |- _ ] => depelim H
    end.
  all:try solve [econstructor; eauto].
  all: have cbΣ : ClosedBodies Σ := @wfE_ClosedBodies _ Σ wfΣ.

  - eapply inversion_SortE in X0 as [wf [wfs cum]]; auto.
    have hsup : isTypeE Σ Γ (tSort (Sort.super u)) by (eapply isType_SortE; [now apply PCUICWfUniverses.wf_sort_super|exact wfΓ]).
    destruct hsup as (_ & ss & hss & _).
    eapply (typeE_Cumul _ _ _ (tSort (Sort.super s)) _ ss); [constructor; auto|exact hss|].
    apply cumulE_Sort. now apply leq_sort_super.

  - eapply inversion_ProdE in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    apply PCUICPrincipality.eq_term_empty_leq_term in X5_1 as X5_1'.
    apply PCUICPrincipality.eq_term_empty_eq_term in X5_1.
    destruct (closed_snoc_vass_inv _ _ _ (typing_closed_contextE X2)) as [clΓ clt].
    pose proof (unlift_TypUniv Ha) as Ha'.
    assert (hat : ws_cumul_pbE Conv Σ Γ a t) by
      exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ (subject_is_open_termE Ha') clt X5_1)).
    pose proof Hb as Hb0.
    eapply closed_context_conversionE in Hb;
      [|exact (typingE_wf_local X2)|exact (ws_cumul_ctx_pbE_vass clΓ e hat)].
    specialize (X3 onu _ _ Hb X5_2).
    eapply typeE_Prod.
    { specialize (X1 onu). rewrite e. apply lift_sorting_it_impl_gen with X1 => // IH. eapply IH; tea. 1: now eapply unlift_TypUniv in Ha. }
    eapply closed_context_conversionE; [exact X3|exact (typingE_wf_local Hb0)|].
    exact (ws_cumul_ctx_pbE_vass clΓ (eq_binder_annot_sym _ _ e) (ws_cumul_pbE_sym_pb hat)).

  - eapply inversion_LambdaE in X4 as (B & dom & codom & cum); auto.
    apply PCUICPrincipality.eq_term_empty_eq_term in X5_1.
    apply PCUICPrincipality.eq_term_empty_leq_term in X5_2.
    destruct (closed_snoc_vass_inv _ _ _ (typing_closed_contextE X2)) as [clΓ clt].
    destruct (closed_snoc_vass_inv _ _ _ (typing_closed_contextE codom)) as [_ clty].
    assert (hty : ws_cumul_pbE Conv Σ Γ ty t) by
      exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ clty clt X5_1)).
    specialize (X3 onu t0 B).
    forward X3 by exact (closed_context_conversionE _ codom (typingE_wf_local X2) (ws_cumul_ctx_pbE_vass clΓ e hty)).
    specialize (X3 X5_2).
    eapply (type_ws_cumul_pbE (pb:=Conv)).
    * eapply typeE_Lambda; [exact dom|].
      instantiate (1 := bty).
      eapply closed_context_conversionE; [exact X3|exact (typingE_wf_local codom)|].
      exact (ws_cumul_ctx_pbE_vass clΓ (eq_binder_annot_sym _ _ e) (ws_cumul_pbE_sym_pb hty)).
    * have tyl := typeE_Lambda _ _ _ _ _ _ X0 X2.
      now eapply validityE in tyl.
    * eapply ws_cumul_pbE_Prod; [exact e|exact hty|].
      eapply ws_cumul_pbE_refl. now eapply typing_closed_contextE in codom.
      eapply type_closedE, closedn_on_free_vars in X2.
      now len in X2; len.

  - eapply inversion_LetInE in X4 as (A & dombod & codom & cum); auto.
    apply unlift_TermTyp in dombod as dombod', X0 as X0'.
    apply PCUICPrincipality.eq_term_empty_eq_term in X5_1.
    apply PCUICPrincipality.eq_term_empty_eq_term in X5_2.
    apply PCUICPrincipality.eq_term_empty_leq_term in X5_3.
    pose proof (typing_closed_contextE X2) as clΓb.
    destruct (closed_snoc_vdef_inv _ _ _ _ clΓb) as [clΓ clb clbty].
    destruct (closed_snoc_vdef_inv _ _ _ _ (typing_closed_contextE codom)) as [_ clt clty].
    assert (htb : ws_cumul_pbE Conv Σ Γ t b) by exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ clt clb X5_1)).
    assert (htyb : ws_cumul_pbE Conv Σ Γ ty b_ty) by exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ clty clbty X5_2)).
    assert(hctx : ws_cumul_ctx_pbE Conv Σ (Γ ,, vdef na0 t ty) (Γ ,, vdef na b b_ty)).
    { constructor; [exact (ws_cumul_ctx_pbE_refl Γ clΓ)|]. constructor; assumption. }
    specialize (X3 onu u A).
    forward X3 by exact (closed_context_conversionE _ codom (typingE_wf_local X2) hctx).
    specialize (X3 X5_3).
    eapply PCUICPrincipality.leq_term_empty_leq_term in X5_3.
    have uty : Σ ;;; Γ ,, vdef na0 t ty |-E u : b'_ty.
    { eapply closed_context_conversionE; [exact X3|exact (typingE_wf_local codom)|].
      constructor; [exact (ws_cumul_ctx_pbE_refl Γ clΓ)|].
      constructor; [exact (eq_binder_annot_sym _ _ e)|exact (ws_cumul_pbE_sym_pb htb)|exact (ws_cumul_pbE_sym_pb htyb)]. }
    eapply type_ws_cumul_pbE.
    * econstructor. eauto.
      now instantiate (1 := b'_ty).
    * eapply validityE; eauto.
      econstructor; eauto.
    * eapply (ws_cumul_pbE_LetIn (pb:=Conv)); [exact e|exact htb|exact htyb|].
      apply ws_cumul_pbE_refl; [exact (typing_closed_contextE uty)|].
      eapply type_closedE, closedn_on_free_vars in X2.
      now len in X2; len.

  - eapply inversion_AppE in X6 as (na' & A' & B' & hf & ha & cum); auto.
    unfold leq_term in X1.
    eapply eq_term_upto_univ_empty_impl in X7_1.
    specialize (X3 onu _ _ hf X7_1). all:try typeclasses eauto.
    specialize (X5 onu _ _ ha (PCUICPrincipality.eq_term_empty_leq_term X7_2)).
    eapply PCUICPrincipality.leq_term_empty_leq_term in X7_1.
    eapply PCUICPrincipality.eq_term_empty_eq_term in X7_2.
    pose proof (typing_closed_contextE X2) as clΓ.
    eapply type_ws_cumul_pbE.
    * eapply type_App'E; [eapply X3|eapply X5].
    * eapply validityE.
      eapply typeE_App; eauto.
    * eapply ws_cumul_pbE_eq_le.
      eapply validityE in X2; auto.
      apply isType_tProdE in X2 as [tyA tyB].
      eapply (substitution_ws_cumul_pbE_subst_conv (Γ0 := [vass na A]) (Γ1 := [vass na A]) (Δ := [])).
      + repeat constructor.
      + repeat constructor.
      + constructor; [|constructor].
        exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ (subject_is_open_termE X5) (subject_is_open_termE X4) X7_2)).
      + exact (closed_snoc_vass Γ na A clΓ (PCUICClosedTypEta.isTypeRel_is_open_termE tyA)).
      + apply ws_cumul_pbE_refl; [exact (closed_snoc_vass Γ na A clΓ (PCUICClosedTypEta.isTypeRel_is_open_termE tyA))|].
        exact (PCUICClosedTypEta.isType_is_open_termE tyB).

  - eapply inversion_ConstE in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    have hv : isTypeE Σ Γ (cst_type decl)@[u] by (eapply validityE; econstructor; eauto).
    destruct hv as (_ & sv & hsv & _).
    eapply (typeE_Cumul _ _ _ _ _ sv); [econstructor; eauto|exact hsv|].
    eapply eq_term_upto_univ_cumulSpecE.
    unshelve epose proof (H_ := declared_constant_to_gen H); eauto.
    unshelve epose proof (declc_ := declared_constant_to_gen declc); eauto.
    pose proof (declared_constant_inj _ _ H_ declc_); subst decl'.
    eapply PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.

  - eapply inversion_IndE in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    have hv : isTypeE Σ Γ (ind_type idecl)@[u] by (eapply validityE; econstructor; eauto).
    destruct hv as (_ & sv & hsv & _).
    eapply (typeE_Cumul _ _ _ _ _ sv); [econstructor; eauto|exact hsv|].
    eapply eq_term_upto_univ_cumulSpecE.
    unshelve epose proof (isdecl_ := declared_inductive_to_gen isdecl); eauto.
    unshelve epose proof (declc_ := declared_inductive_to_gen declc); eauto.
    pose proof (declared_inductive_inj isdecl_ declc_) as [-> ->].
    eapply PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.

  - eapply inversion_ConstructE in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    eapply (type_ws_cumul_pbE (pb:=Conv)); eauto.
    econstructor; eauto.
    eapply validityE; eauto.
    econstructor; eauto.
    unshelve epose proof (isdecl_ := declared_constructor_to_gen isdecl); eauto.
    unshelve epose proof (declc_ := declared_constructor_to_gen declc); eauto.
    pose proof (declared_constructor_inj isdecl_ declc_) as [-> [-> ->]].
    unfold type_of_constructor.
    pose proof (wf_local_closed_contextE wf) as clΓ.
    (* Base's [declared_minductive_closed_arities] and [declared_constructor_closed_gen_type]
       (Typing/PCUICClosedTyp.v:619, 638) take base [wf]; their two-line proofs over the landed
       [declared_minductive_closedE] / [declared_constructor_closedE]. *)
    have clar : closed_ctx (arities_context (ind_bodies mdecl)).
    { pose proof (declared_minductive_closedE (MRProd.proj1 (MRProd.proj1 declc))) as h.
      move/andP: h => [] _ clbs.
      induction (ind_bodies mdecl) => //.
      rewrite /arities_context /= rev_map_spec /=.
      move: clbs; simpl. move=> /andP[] cla clbs.
      rewrite closedn_ctx_app /=. apply/andP; split; auto.
      rewrite /test_decl /=. now move/andP: cla => [] /andP[] /andP[].
      eapply closedn_ctx_upwards. rewrite -rev_map_spec. eapply IHl => //. lia. }
    have clctx : forall v, is_closed_context (Γ ,,, (arities_context (ind_bodies mdecl))@[v]).
    { intros v. rewrite on_free_vars_ctx_app. apply /andP ; split => //.
      erewrite PCUICOnFreeVars.on_free_vars_ctx_subst_instance.
      now eapply closed_ctx_on_free_vars in clar. }
    have cld : is_open_term (Γ ,,, arities_context (ind_bodies mdecl)) (cstr_type cdecl').
    { pose proof (declared_constructor_closedE declc) as h.
      move/andP: h => [/andP [hargs hindices]] cl.
      eapply closedn_on_free_vars in cl. len.
      rewrite -shiftnP_add. len in cl. exact cl. }
    have uss : forall v w, untyped_subslet Γ (inds (inductive_mind ind) v (ind_bodies mdecl))
      (arities_context (ind_bodies mdecl))@[w].
    { intros v w. apply untyped_subslet_assumption_context.
      - apply assumption_context_subst_instance, assumption_context_arities_context.
      - now rewrite inds_length; len. }
    transitivity (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u0 cdecl'.(cstr_type))).
    * eapply (substitution_ws_cumul_pbE_subst_conv (Γ0 := (arities_context (ind_bodies mdecl))@[u0])
        (Γ1 := (arities_context (ind_bodies mdecl))@[u]) (Δ := [])); [apply uss|apply uss| | |].
      + cbn. eapply conv_indsE => //.
      + apply clctx.
      + simpl. eapply ws_cumul_pbE_refl; [apply clctx|].
        rewrite on_free_vars_subst_instance. move: cld. now len.
    * apply ws_cumul_pb_incl_E. constructor; auto.
      { eapply PCUICOnFreeVars.on_free_vars_subst. eapply inds_is_open_terms.
        len. len in cld. rewrite shiftnP_add.
        now rewrite on_free_vars_subst_instance. }
      { eapply PCUICOnFreeVars.on_free_vars_subst. eapply inds_is_open_terms.
        len. len in cld. rewrite shiftnP_add.
        now rewrite on_free_vars_subst_instance. }
      eapply PCUICEquality.subst_eq_term.
      eapply PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.

  - eassert (PCUICTyping.ctx_inst _ _ _ _) as Hctxi by now eapply PCUICTyping.ctx_inst_impl with (1 := X5).
    assert (hty : isTypeE Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validityE. econstructor; eauto. all:split; eauto.
      solve_all. }
    eapply inversion_CaseE in X9 as (mdecl' & idecl' & decli' & indices' & data & cum); auto.
    unshelve epose proof (isdecl_ := declared_inductive_to_gen isdecl); eauto.
    unshelve epose proof (decli'_ := declared_inductive_to_gen decli'); eauto.
    destruct (declared_inductive_inj isdecl_ decli'_). subst mdecl' idecl'.
    destruct data.
    pose proof (X7 onu _ _ scrut_ty (PCUICPrincipality.eq_term_empty_leq_term X10)) as hc0.
    pose proof (PCUICPrincipality.eq_term_empty_eq_term X10) as eqc.
    destruct e as [eqpars [eqinst [eqpctx eqpret]]].
    eapply PCUICPrincipality.eq_term_empty_eq_term in eqpret.
    pose proof (typing_closed_contextE X6) as clΓ.
    eapply type_ws_cumul_pbE.
    * econstructor; eauto. all:split; eauto.
    * exact hty.
    * clear brs_ty.
      eapply ws_cumul_pbE_eq_le.
      eapply ws_cumul_pbE_mkApps.
      { apply ws_cumul_pb_incl_E. constructor; [exact clΓ| | |].
        - eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE in pret_ty. subst predctx0.
          exact (subject_is_open_termE pret_ty).
        - eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE in pret. subst predctx.
          exact (subject_is_open_termE pret).
        - rewrite /ptm.
          eapply PCUICEquality.eq_term_upto_univ_it_mkLambda_or_LetIn; tea; tc.
          rewrite /predctx.
          rewrite /case_predicate_context /case_predicate_context_gen.
          eapply eq_context_upto_names_map2_set_binder_name. tea.
          rewrite /pre_case_predicate_context_gen.
          eapply PCUICPrincipality.eq_context_upto_inst_case_context => //. }
      unfold ws_cumul_pbE_terms. eapply All2_app.
      2:{ constructor; [|constructor].
          exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ (subject_is_open_termE scrut_ty)
            (subject_is_open_termE X6) eqc)). }
      destruct (principal_type_indE (wfΣ := (wfΣ, onu)) scrut_ty hc0) as [[_ indconv] _].
      eapply All2_app_inv in indconv as [convpars convinds] => //.
      exact (All2_length eqpars).

  - eapply inversion_ProjE in X3 as (u' & mdecl' & idecl' & cdecl' & pdecl' & args' & [hdecl' [hc0 [hlen' hcum]]]); auto.
    pose proof (X2 onu _ _ hc0 (PCUICPrincipality.eq_term_empty_leq_term X4)) as hc0'.
    eapply PCUICPrincipality.eq_term_empty_eq_term in X4.
    pose proof (typing_closed_contextE X1) as clΓ.
    eapply (type_ws_cumul_pbE (pb:=Conv)).
    * exact (typeE_Proj _ _ p c0 u mdecl idecl cdecl pdecl args isdecl hc0' H).
    * eapply validityE; eauto.
      eapply typeE_Proj; eauto.
    * pose proof (PCUICInductiveInversion.is_closed_context_weaken _ _ clΓ (is_closed_projection_contextE (p := p) u isdecl)) as clctx.
      eapply (substitution_ws_cumul_pbE_subst_conv (Δ := []));
        [exact (untyped_subslet_projection_contextE u isdecl H)
        |exact (untyped_subslet_projection_contextE u isdecl H)| |exact clctx|].
      + constructor.
        { exact (ws_cumul_pb_incl_E (ws_cumul_pb_compare _ _ _ _ _ clΓ (subject_is_open_termE hc0')
            (subject_is_open_termE X1) X4)). }
        eapply All2_rev. eapply WT_refl => //.
        pose proof (type_is_open_termE X1) as hX1.
        rewrite on_free_vars_mkApps in hX1. now move/andP: hX1 => [].
      + eapply ws_cumul_pbE_refl => //.
        epose proof (declared_projection_closedE isdecl).
        rewrite on_free_vars_subst_instance; len. len.
        rewrite -(declared_minductive_ind_nparsE (MRProd.proj1 (MRProd.proj1 (MRProd.proj1 isdecl)))).
        eapply closedn_on_free_vars in H0.
        now rewrite -plus_Sn_m -shiftnP_add.

  - match goal with Hty : _ ;;; _ |-E tFix _ _ : _ |- _ =>
      eapply inversion_FixE in Hty as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum)
    end; auto.
    have hv : isTypeE Σ Γ (dtype decl) by (eapply isTypeRelE_isTypeE; now eapply All_nth_error in X0).
    destruct hv as (_ & sv & hsv & _).
    eapply (typeE_Cumul _ _ _ _ _ sv); [econstructor; eauto|exact hsv|].
    eapply All2_nth_error in e; eauto.
    destruct e as (eqty & _).
    apply eq_term_upto_univ_cumulSpecE. eapply PCUICPrincipality.eq_term_empty_leq_term in eqty.
    now eapply PCUICPrincipality.leq_term_empty_leq_term.

  - match goal with Hty : _ ;;; _ |-E tCoFix _ _ : _ |- _ =>
      eapply inversion_CoFixE in Hty as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum)
    end; auto.
    have hv : isTypeE Σ Γ (dtype decl) by (eapply isTypeRelE_isTypeE; now eapply All_nth_error in X0).
    destruct hv as (_ & sv & hsv & _).
    eapply (typeE_Cumul _ _ _ _ _ sv); [econstructor; eauto|exact hsv|].
    eapply All2_nth_error in e; eauto.
    destruct e as (eqty & _).
    apply eq_term_upto_univ_cumulSpecE. apply PCUICPrincipality.eq_term_empty_leq_term in eqty.
    now eapply PCUICPrincipality.leq_term_empty_leq_term.

  - epose proof (typeE_Prim _ _ _ _ _ X H H0 H1 X0). eapply validityE in X4.
    depelim X1; depelim X3; depelim o.
    1-3:econstructor; tea.
    depelim X0. destruct X4 as (_ & s & ? & _).
    econstructor; tea.
    eapply inversion_PrimE in X2 as [prim_ty' [cdecl' []]]; eauto.
    rewrite e2 in H. noconf H.
    unshelve eapply declared_constant_to_gen in H0, d; tea.
    pose proof (declared_constant_inj _ _ H0 d). subst cdecl'.
    simp prim_type in w |- *.
    (* The guard on ws_cumul_pbE_Axiom_l_inv: prim_ty is a registered primitive
       TYPE constant, which §4.2(a)1 keeps out of the operation table. *)
    assert (hnop : PCUICEnvironment.prim_op_of Σ prim_ty = None).
    { pose proof wfΣ as [_ [wfr _]]. eapply prim_op_of_primitive_constant; tea. }
    destruct (ws_cumul_pbE_Axiom_l_inv (args := [_]) (declared_constant_from_gen H0) ltac:(eapply p) hnop w)
      as [u' [args' [hch a3 c0]]].
    apply ws_cumul_pbE_forget_spec.
    etransitivity.
    { apply ws_cumul_pbE_eq_le. exact (chain_ws_cumul_pbE_Conv _ _ _ (wsE_ctx w) (wsE_right w) hch). }
    eapply All2_tip_l in a3 as [y' [-> Heq]]. red in c0.
    eapply Forall2_tip_l in c0. cbn. eapply ws_cumul_pbE_eq_le.
    eapply (ws_cumul_pbE_mkApps (args := [_]) (args' := [_])).
    * apply ws_cumul_pbE_Const; [exact (wsE_ctx w)|]. red. destruct c0 as [? [-> eq]]. constructor. symmetry.
      etransitivity; tea. now symmetry. constructor.
    * constructor; [|constructor]. symmetry. etransitivity; tea.
      apply ws_cumul_pb_incl_E. constructor; fvs. symmetry.
      now eapply PCUICPrincipality.eq_term_empty_eq_term.

  - eapply (typeE_Cumul _ _ _ A B s); [eapply X1; eauto|exact X2|exact X4].

Qed.

(** Base [typing_eq_term] ([PCUICPrincipality.v:756]). *)
Lemma typing_eq_termE {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' :
  wf_extE Σ ->
  Σ ;;; Γ |-E t : T ->
  Σ ;;; Γ |-E t' : T' ->
  eq_term empty_global_env Σ t t' ->
  Σ ;;; Γ |-E t' : T.
Proof.
  intros wfΣ ht ht' eq.
  eapply typing_leq_termE; [exact wfΣ.1|exact wfΣ.2|exact ht|exact ht'|].
  now eapply PCUICPrincipality.eq_term_empty_leq_term.
Qed.

End PrincipalityEta.
