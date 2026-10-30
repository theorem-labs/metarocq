(* Distributed under the terms of the MIT license. *)

(** * Classification over [typingE] (row T6): the E copy of [PCUICClassification]

  The E twin of every declaration of base [PCUICClassification] whose statement mentions
  typing, conversion, [wf] or [isType]: [typing] → [typingE], [wf] → [wfE], [wf_local] →
  [wf_localE], [isType] → [isTypeE] ([PCUICTypingEtaNotions]), [isTypeRel] → [isTypeRelE],
  [PCUICArities.typing_spine] → [PCUICAritiesEta.typing_spineE] (always written qualified: the
  non-canonical [PCUICGenerationEta.typing_spineE] is loaded too), [wf_fixpoint] /
  [wf_cofixpoint] → [wf_fixpointE] / [wf_cofixpointE], [conv_witness] → [conv_witnessE],
  [Σ ;;; Γ ⊢ A ≤[pb] B] ([ws_cumul_pb]) → [Σ ;;; Γ ⊢E A ≤[pb] B] ([ws_cumul_pbE]). Reduction
  ([Σ ;;; Γ ⊢ t ⇝ u], [red]), [Is_conv_to_Arity] (defined by reduction), [eval], [value] and
  [whnf] are unchanged. Each name takes the suffix [E] (plan [t0-plan.md] §2, D1). The section
  structure and [Set Default Proof Using "Type*"] are base's, so a lemma takes [wfΣ : wfE Σ]
  exactly where base's compiled lemma takes [wfΣ : wf Σ].

  Imported from base, not copied (they mention none of the relations and base's compiled
  forms take no environment premise): [negb_False], [isArity_subst], [closedn_mkApps],
  [isArity_ind], [on_free_vars_it_mkLambda_or_LetIn], [assumption_context_assumptions],
  [firstn_subst_context], [assumption_context_firstn], [axiom_free], [axiom_free_value],
  [axiom_free_axiom_free_value], [axiom_free_value_mkApps], [notCoInductive],
  [value_axiom_free], the tactics [destruct_sigma] and [redt].

  Copied although they mention no relation, because base's compiled forms take [wf Σ] (the
  section variable, through [Proof using Type*]) and a [wfE] context cannot supply it:
  [Is_conv_to_Arity_indE], [value_whnfE], [eval_whneE], [check_recursivity_kind_injE].

  Name shared by two declarations, as in base: [typing_spine_nth_errorE] is the twin of
  [PCUICClassification.typing_spine_nth_error] here and of [PCUICSpine.typing_spine_nth_error]
  in [PCUICSpineEta]; both are written qualified.

  ** Statement changes (NOT TWIN rows; classes of cross-lane-commitments.md M3/M8)

  - The arity corollaries: i20 [invert_cumul_arity_rE] and i21 [invert_cumul_arity_lE] (base
    [PCUICConversion.v:1231], [:1249], no environment premise) and x2
    [invert_cumul_arity_l_genE], x3 [invert_cumul_arity_r_genE] (base [:83], [:93], section
    [wf Σ]) each ADD [isTypeE Σ Γ X] of the side that is not an arity (Class A',
    [t8-consumers.md] §3.3, §7.1). i20 and i21 also add [wfE Σ] (the T8 forms they use need
    it; base has no environment premise). Why: untyped, the base forms are FALSE over η
    ([invert_cumul_arity_lE_untyped_false], [invert_cumul_arity_rE_untyped_false] below: the
    untypable witness [λx:Prop. (tSort Prop) x], η-related to the arity [tSort Prop] and
    red-normal); the witness refutes only the untyped forms. With the premise, each is proved
    from typed T8 ([T8_Sort_l_plug] here and [PCUICPrincipalityEta.T8_Prod_l_plug], from the
    proved [_r] forms; [BDFromPCUICEta.T8_Sort_r_plug], [T8_Prod_r_plug]). Consumers: [isArity_typing_spineE]
    (supplies it from the spine's [isTypeE] fields). The other consumers are erasure copies
    (X6, off the F2 path), named in [t8-consumers.md] §3.3 and §4.
  - [mfix_on_ind_spine_witness] (base [:132], generic over a [ShapeCheck] check) is copied
    once per check, [mfix_on_ind_spine_witnessE_fix] and [mfix_on_ind_spine_witnessE_cofix],
    the two checks of its two consumers [wf_fixpoint_spineE] and [wf_cofixpoint_spineE]. The
    route is the ruled typed-reduct route ([t0-plan.md] §6 risk 5, row [PCUICFixWitness],
    option (i)): [BDFromPCUICEta.mfix_body_on_conv_redE_fix]/[_cofix], proved with E subject
    reduction, never the closed-only form (false: [PCUICFixWitnessEtaCounter.v]). The proof
    reads the structure of each check, as [BDFromPCUICEta]'s; [ShapeCheck]'s reduction field
    is stated over base [wf] and base reduction only and says nothing of η, so it gives no
    route for the generic form.

  ** Helpers with no base twin in a copied file

  - [eval_closed_cb]: base [PCUICWcbvEval.eval_closed] ([PCUICWcbvEval.v:949]) with
    [ClosedBodies Σ] in place of [wf Σ] (Class B: the proof reads [wf] only for closed constant
    bodies). [PCUICWcbvEval] has no E copy.
  - [arity_spine_len], [arity_spine_len_subst]: the measure of the induction in the proofs of
    i20 and i21 (base inducts on the algorithmic cumulativity derivation, which [ws_cumul_pbE]
    does not have).
  - [T8_Sort_l_plug]: the left T8 form at a sort, derived from the proved right form as in
    [lanes/eta/meta/inventory-sweep.md] ([T8_*_l_of_r]; that file does not land), with
    [PCUICPrincipalityEta.chain_ws_cumul_pbE_Conv]. Its type is the pinned
    [PCUICEtaT8Probe.T8_Sort_l_statement], checked by [T8_Sort_l_plug_fit]. The product form and
    the chain lemma are [PCUICPrincipalityEta]'s ([T8_Prod_l_plug], [chain_ws_cumul_pbE_Conv]),
    required, not imported, and written qualified.

  ** Proof routes that differ from base (statements do not)

  - [typing_spine_nth_error_NoneE], the empty-spine case: base inverts [tProd .. ≤ T'] into a
    reduct of [T'] ([ws_cumul_pb_Prod_l_inv]) and rebuilds the same comparison; the goal is the
    premise itself, so the E proof uses it directly.
  - [invert_fix_indE]: base inverts [tProd .. ≤ mkApps (tInd ..) ..] into a reduct; the E
    proof uses the head-clash row [invert_cumul_prod_indE] ([PCUICEtaA6Ind]).
  - Untyped reduction facts under [wfE] use base's [_cb] variants through the instance
    [wfE_ClosedBodies] ([invert_red_prod_cb], [invert_red_mkApps_tInd_cb],
    [closed_red_untyped_substitution_cb], [red_red_cb], [closed_red_open_right_cb]).

  ** No forecast class

  T1's [SRForecastCopy18] (it entered through [subject_reductionE], [isType_redE] and the T8
  forms) was a section premise until copy 18b landed (frac/eta 3e6b422d); it was deleted after a
  compiled-form identity check of each field. Copy 16 landed earlier (frac/eta 0fb43f10): T2a's
  [ValForecastCopy16], T1's [SRForecastCopy16] and this file's [ClassifForecastCopy16] were
  deleted the same way, and [PCUICInductivesEta] is imported. No lemma takes a class. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion PCUICViews
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICFixWitness
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICClassification.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningEnvTypEta
  PCUICWeakeningTypEta PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICEtaC1aR
  PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5A2 PCUICEtaC1b
  PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
  PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICContextConversionEta PCUICWsCumulEtaCtx
  PCUICWsCumulEtaCtxTyp PCUICInversionEta PCUICSREtaConv
  PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta
  PCUICWsCumulEtaInstancesGlobal PCUICInductivesEta PCUICValidityEta PCUICSREta.
From MetaRocq.PCUIC.Typing Require Import PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require PCUICGenerationEta PCUICEtaT8Probe BDFromPCUICEta PCUICPrincipalityEta.

Local Existing Instance config.extraction_checker_flags.

From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.

Set Default Proof Using "Type*".

(** ** Helpers with no class *)

(** Base [PCUICWcbvEval.eval_closed] ([PCUICWcbvEval.v:949]) with [ClosedBodies Σ] in place of
    [wf Σ] (Class B). *)
Section EvalClosedCb.
  Context (Σ : global_env).

  Lemma eval_closed_cb `{checker_flags} {cbΣ : ClosedBodies Σ} :
    forall t u, closed t -> eval Σ t u -> closed u.
  Proof using Type.
    move=> t u Hc ev. move: Hc.
    induction ev; simpl in *; auto;
      (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
    - eapply IHev3. unshelve eapply closed_beta. 3:eauto. exact na. simpl. eauto.
    - eapply IHev2. now rewrite closed_csubst.
    - apply IHev. rewrite PCUICClosed.closedn_subst_instance.
      eapply (closed_bodies (Σ := Σ)); [apply declared_constant_from_gen|]; eauto.
    - apply IHev2.
      eapply closed_iota; tea.
      move/andP: Hc => [] /andP [] //.
      now eapply IHev1. rewrite e1.
      now rewrite -e3 e2 /cstr_arity.
    - eapply IHev2.
      specialize (IHev1 Hc).
      rewrite closedn_mkApps in IHev1.
      move/andP: IHev1 => [Hcons Hargs]. solve_all.
      eapply All_nth_error in Hargs; eauto.
    - eapply IHev3.
      apply/andP.
      split; [|easy].
      specialize (IHev1 Hc).
      rewrite closedn_mkApps in IHev1.
      move/andP: IHev1 => [clfix clargs].
      rewrite closedn_mkApps clargs andb_true_r.
      eapply closed_unfold_fix; [easy|].
      now rewrite closed_unfold_fix_cunfold_eq.
    - apply andb_true_iff.
      split; [|easy].
      solve_all.
    - eapply IHev2. solve_all. rewrite !closedn_mkApps in H0 |- *. solve_all.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - eapply IHev2. solve_all. rewrite !closedn_mkApps in H0 |- *. solve_all.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - rewrite closedn_mkApps /=. specialize (IHev1 Hc). specialize (IHev2 Hc').
      move: IHev1. rewrite closedn_mkApps /= forallb_app => -> /=. now rewrite IHev2.
    - apply/andP; split; auto.
    - solve_all. depelim X; depelim Hc; constructor; intuition eauto; solve_all.
  Qed.
End EvalClosedCb.

(** The measure of the inductions of i20 and i21: the number of products and let-ins on the
    spine of an arity. *)
Fixpoint arity_spine_len (t : term) : nat :=
  match t with
  | tProd _ _ B | tLetIn _ _ _ B => S (arity_spine_len B)
  | _ => 0
  end.

Lemma arity_spine_len_subst s k t :
  isArity t -> arity_spine_len (subst s k t) = arity_spine_len t.
Proof.
  induction t in k |- *; cbn; intros h; try discriminate h; try reflexivity; f_equal; auto.
Qed.

Section ClassificationEta.

(** ** Typed T8, left form at a sort

  [_l] from [_r]: the [_l] inversion's chain shows [T] E-convertible to a head form, so [_r] at
  [Conv] gives the reduct, and the head-against-head inversion compares the heads. The type is
  the pinned [PCUICEtaT8Probe.T8_Sort_l_statement] ([_fit] below). The product form is
  [PCUICPrincipalityEta.T8_Prod_l_plug]. *)
Lemma T8_Sort_l_plug :
  forall (cf : checker_flags) (Σ : global_env_ext),
  forall Γ pb T s s',
    wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
    ws_cumul_pbE pb Σ Γ (tSort s) T ->
    ∑ s'', Σ ;;; Γ ⊢ T ⇝ tSort s'' × compare_sort Σ pb s s''.
Proof using.
  intros cf Σ Γ pb T s s' wfΣ hT hc.
  have cb : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  destruct (ws_cumul_pbE_Sort_l_inv (Σ := Σ) pb hc) as (s1 & hch & _).
  have hconv := PCUICPrincipalityEta.chain_ws_cumul_pbE_Conv (cb := cb) Γ T _ (wsE_ctx hc) (wsE_right hc) hch.
  destruct (BDFromPCUICEta.T8_Sort_r_plug cf Σ Γ Conv T s1 s' wfΣ hT hconv) as (s2 & hred & _).
  exists s2. split; [exact hred|].
  have h2 : ws_cumul_pbE pb Σ Γ (tSort s) (tSort s2) :=
    ws_cumul_pbE_trans (Σ := Σ) (wfΣ := cb) _ _ _ hc (red_ws_cumul_pbE (wfΣ := cb) hred).
  exact (ws_cumul_pbE_Sort_inv (Σ := Σ) pb h2).
Qed.

Definition T8_Sort_l_plug_fit (cf : checker_flags) (Σ : global_env_ext) :
  @PCUICEtaT8Probe.T8_Sort_l_statement cf Σ := T8_Sort_l_plug cf Σ.

(** ** The arity corollaries i20 and i21 ([PCUICConversion.v:1231], [:1249]), Class A' *)

Section ArityCorollariesE.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** i20, with [isTypeE Σ Γ C] (Class A') and [wfE Σ]. *)
  Lemma invert_cumul_arity_rE :
    forall (Γ : context) (C : term) T,
      isArity T ->
      Σ ;;; Γ ⊢E C ≤ T ->
      isTypeE Σ Γ C ->
      Is_conv_to_Arity Σ Γ C.
  Proof using Type*.
    intros Γ C T a h isC.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    remember (arity_spine_len T) as n eqn:hn.
    have hle : arity_spine_len T <= n by lia.
    clear hn.
    induction n as [|n IH] in Γ, C, T, a, h, isC, hle |- *;
      (destruct T as [| | |s|na A B| |na b ty B| | | | | | | | |]; cbn in a;
       try discriminate a; try (exfalso; exact (Nat.nle_succ_0 _ hle))).
    1,2: (* a sort *)
      have isC' := isC; destruct isC' as (_ & sC & tyC & _);
      destruct (BDFromPCUICEta.T8_Sort_r_plug _ Σ Γ Cumul C s sC wfΣ tyC h) as (s'' & r & _);
      exists (tSort s''); split; [now sq|reflexivity].
    - (* a product: T8 [Prod_r], then the codomain *)
      have isC' := isC. destruct isC' as (_ & sC & tyC & _).
      destruct (BDFromPCUICEta.T8_Prod_r_plug _ Σ Γ Cumul C na A B sC wfΣ tyC h)
        as (na' & A' & B' & [r ena hA hB]).
      assert (isP : isTypeE Σ Γ (tProd na' A' B')) by exact (isType_redE isC (clrel_rel r)).
      destruct (fst (isType_tProdE (wfΣ := wfΣ)) isP) as [isA' isB'].
      have clΓ := wsE_ctx h.
      have clΓ' : is_closed_context (Γ ,, vass na' A') :=
        closed_snoc_vass Γ na' A' clΓ (wsE_left hA).
      have hB' : Σ ;;; Γ ,, vass na' A' ⊢E B' ≤ B.
      { eapply ws_cumul_pbE_bodies; [|exact clΓ'|exact hB].
        apply upto_domain_r_bodies_vass, upto_domain_r_bodies_refl. }
      destruct (IH (Γ ,, vass na' A') B' B a hB' isB' (le_S_n _ _ hle)) as (B'' & [rB] & aB).
      exists (tProd na' A' B''). split; [|exact aB]. sq.
      etransitivity; [exact r|]. now eapply closed_red_prod_codom.
    - (* a let-in: zeta on the arity side *)
      have h' : Σ ;;; Γ ⊢E C ≤ B {0 := b} :=
        ws_cumul_pbE_red_r_inv (wfΣ := cbΣ) _ h (red1_red _ _ _ _ (red_zeta _ _ na b ty B)).
      eapply (IH Γ C (B {0 := b})); tea.
      + now apply isArity_subst.
      + rewrite /subst1 arity_spine_len_subst //. exact (le_S_n _ _ hle).
  Qed.

  (** i21, with [isTypeE Σ Γ T] (Class A') and [wfE Σ]. *)
  Lemma invert_cumul_arity_lE :
    forall (Γ : context) (C : term) T,
      isArity C ->
      Σ ;;; Γ ⊢E C ≤ T ->
      isTypeE Σ Γ T ->
      Is_conv_to_Arity Σ Γ T.
  Proof using Type*.
    intros Γ C T a h isT.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    remember (arity_spine_len C) as n eqn:hn.
    have hle : arity_spine_len C <= n by lia.
    clear hn.
    induction n as [|n IH] in Γ, C, T, a, h, isT, hle |- *;
      (destruct C as [| | |s|na A B| |na b ty B| | | | | | | | |]; cbn in a;
       try discriminate a; try (exfalso; exact (Nat.nle_succ_0 _ hle))).
    1,2: (* a sort *)
      have isT' := isT; destruct isT' as (_ & sT & tyT & _);
      destruct (T8_Sort_l_plug _ Σ Γ Cumul T s sT wfΣ tyT h) as (s'' & r & _);
      exists (tSort s''); split; [now sq|reflexivity].
    - (* a product: T8 [Prod_l], then the codomain *)
      have isT' := isT. destruct isT' as (_ & sT & tyT & _).
      destruct (PCUICPrincipalityEta.T8_Prod_l_plug _ Σ Γ Cumul T na A B sT wfΣ tyT h)
        as (na' & A' & B' & [r ena hA hB]).
      assert (isP : isTypeE Σ Γ (tProd na' A' B')) by exact (isType_redE isT (clrel_rel r)).
      destruct (fst (isType_tProdE (wfΣ := wfΣ)) isP) as [isA' isB'].
      have clΓ := wsE_ctx h.
      have clΓ' : is_closed_context (Γ ,, vass na' A') :=
        closed_snoc_vass Γ na' A' clΓ (wsE_right hA).
      have hB' : Σ ;;; Γ ,, vass na' A' ⊢E B ≤ B'.
      { eapply ws_cumul_pbE_bodies; [|exact clΓ'|exact hB].
        apply upto_domain_r_bodies_vass, upto_domain_r_bodies_refl. }
      destruct (IH (Γ ,, vass na' A') B B' a hB' isB' (le_S_n _ _ hle)) as (B'' & [rB] & aB).
      exists (tProd na' A' B''). split; [|exact aB]. sq.
      etransitivity; [exact r|]. now eapply closed_red_prod_codom.
    - (* a let-in: zeta on the arity side *)
      have h' : Σ ;;; Γ ⊢E B {0 := b} ≤ T :=
        ws_cumul_pbE_red_l_inv (wfΣ := cbΣ) _ h (red1_red _ _ _ _ (red_zeta _ _ na b ty B)).
      eapply (IH Γ (B {0 := b}) T); tea.
      + now apply isArity_subst.
      + rewrite /subst1 arity_spine_len_subst //. exact (le_S_n _ _ hle).
  Qed.

End ArityCorollariesE.

(** Base [isArity_typing_spine] ([:39]). The premise [isTypeE] of i21 comes from the spine's
    fields (the target in the empty case, the product in the other). *)
Lemma isArity_typing_spineE {cf:checker_flags} {Σ : global_env_ext} {Γ L T T'} {wfΣ : wfE Σ} :
  wf_localE Σ Γ ->
  PCUICAritiesEta.typing_spineE Σ Γ T' L T ->
  Is_conv_to_Arity Σ Γ T' ->
  Is_conv_to_Arity Σ Γ T.
Proof using Type*.
  intros wfΓ sp.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  induction sp as [ty ty' isty isty' w|ty hd tl na A B B' isty isP w hhd sp IHsp]; intros isc.
  - destruct isc as (x & [r] & ar).
    assert (w' : Σ ;;; Γ ⊢E x ≤ ty') by exact (ws_cumul_pbE_trans _ _ _ (red_ws_cumul_pbE_inv r) w).
    exact (invert_cumul_arity_lE Γ x ty' ar w' isty').
  - eapply IHsp.
    destruct isc as (x & [r] & ar).
    assert (w' : Σ ;;; Γ ⊢E x ≤ tProd na A B) by exact (ws_cumul_pbE_trans _ _ _ (red_ws_cumul_pbE_inv r) w).
    destruct (invert_cumul_arity_lE Γ x _ ar w' isP) as (x' & [r'] & ar').
    eapply invert_red_prod_cb in r' as (dom' & codom' & [-> rdom rcodom]).
    exists (codom' {0 := hd}). split; [sq|now eapply isArity_subst].
    eapply (closed_red_untyped_substitution_cb (Δ := [_]) (Γ' := [])); eauto.
    + econstructor. econstructor.
    + cbn. now rewrite (subject_is_open_termE hhd).
Qed.

Section AritiesE.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wfE Σ}.

  (** x2, base [invert_cumul_arity_l_gen] ([:83]), with [isTypeE Σ Γ T] (Class A'). *)
  Lemma invert_cumul_arity_l_genE (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ ;;; Γ ⊢E C ≤ T -> isTypeE Σ Γ T -> Is_conv_to_Arity Σ Γ T.
  Proof using Type*.
    intros [ar [red isA]]. sq.
    intros cum isT.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    have: Σ ;;; Γ ⊢E ar ≤ T.
    { eapply ws_cumul_pbE_red_l_inv; tea. exact red. }
    intros h. now eapply invert_cumul_arity_lE.
  Qed.

  (** x3, base [invert_cumul_arity_r_gen] ([:93]), with [isTypeE Σ Γ T] (Class A'). *)
  Lemma invert_cumul_arity_r_genE (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ;;; Γ ⊢E T ≤ C -> isTypeE Σ Γ T -> Is_conv_to_Arity Σ Γ T.
  Proof using Type*.
    intros [ar [red isA]]. sq.
    intros cum isT.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    have: Σ ;;; Γ ⊢E T ≤ ar.
    { eapply ws_cumul_pbE_red_r_inv; tea. exact red. }
    intros h. now eapply invert_cumul_arity_rE.
  Qed.

  (** Base [Is_conv_to_Arity_ind] ([:106]). *)
  Lemma Is_conv_to_Arity_indE Γ ind i args : Is_conv_to_Arity Σ Γ (mkApps (tInd ind i) args) -> False.
  Proof.
    intros [ar [red eq]]. sq.
    eapply invert_red_mkApps_tInd_cb in red as (? & []); auto. subst ar.
    now eapply isArity_ind in eq.
  Qed.

  (** Base [typing_spine_arity_mkApps_Ind] ([:113]). *)
  Lemma typing_spine_arity_mkApps_IndE Γ T l i u args :
    wf_localE Σ Γ ->
    PCUICAritiesEta.typing_spineE Σ Γ T l (mkApps (tInd i u) args) ->
    Is_conv_to_Arity Σ Γ T -> False.
  Proof using Type*.
    intros wf sp isc.
    eapply (isArity_typing_spineE wf sp) in isc.
    now eapply Is_conv_to_Arity_indE.
  Qed.

End AritiesE.

Section SpinesE.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.
  Context (wfΣ : wfE Σ.1).

  (** Base [mfix_on_ind_spine_witness] ([:132]) at [check_one_fix]. The reduct comes from
      the typed-reduct route ([BDFromPCUICEta.mfix_body_on_conv_redE_fix]).
      NOT TWIN (specialised): base's statement is generic over a [ShapeCheck] check; here one
      lemma per check, the two checks of its consumers. Generic form: truth open, no route
      ([ShapeCheck]'s reduction field speaks of base [wf] and base reduction only), no
      refutation built. *)
  Lemma mfix_on_ind_spine_witnessE_fix {ok} Γ mfix idx decl args ty :
    mfix_on_ind check_one_fix (conv_witnessE Σ Γ) ok mfix ->
    nth_error mfix idx = Some decl ->
    isTypeE Σ Γ (dtype decl) ->
    PCUICAritiesEta.typing_spineE Σ Γ (dtype decl) args ty ->
    ∑ mind tw,
      [× Σ ;;; Γ ⊢ dtype decl ⇝ tw, check_one_fix (def_with_type decl tw) = Some mind, ok mind,
         isTypeE Σ Γ tw & PCUICAritiesEta.typing_spineE Σ Γ tw args ty].
  Proof using Type*.
    move=> [mind [_ [hall hck]]] nthe isty sp.
    have wfΓ : wf_localE Σ Γ := isType_wf_localE isty.
    assert (clΓ : is_closed_context Γ) by exact (wf_local_closed_contextE wfΓ).
    assert (opd : is_open_term Γ (dtype decl)) by exact (PCUICClosedTypEta.isType_is_open_termE isty).
    eapply nth_error_all in hall; tea.
    destruct (BDFromPCUICEta.mfix_body_on_conv_redE_fix wfΓ isty hall) as [tw [ck r]].
    have r' : Σ ;;; Γ ⊢ dtype decl ⇝ tw := into_closed_red r clΓ opd.
    assert (istw : isTypeE Σ Γ tw) by exact (isType_redE isty r).
    exists mind, tw; split => //.
    eapply typing_spine_strengthenE; [exact sp|exact istw|].
    now eapply red_ws_cumul_pbE_inv.
  Qed.

  (** Base [mfix_on_ind_spine_witness] ([:132]) at [check_one_cofix]. NOT TWIN (specialised),
      as [mfix_on_ind_spine_witnessE_fix]: generic form: truth open, no route, no refutation
      built. *)
  Lemma mfix_on_ind_spine_witnessE_cofix {ok} Γ mfix idx decl args ty :
    mfix_on_ind check_one_cofix (conv_witnessE Σ Γ) ok mfix ->
    nth_error mfix idx = Some decl ->
    isTypeE Σ Γ (dtype decl) ->
    PCUICAritiesEta.typing_spineE Σ Γ (dtype decl) args ty ->
    ∑ mind tw,
      [× Σ ;;; Γ ⊢ dtype decl ⇝ tw, check_one_cofix (def_with_type decl tw) = Some mind, ok mind,
         isTypeE Σ Γ tw & PCUICAritiesEta.typing_spineE Σ Γ tw args ty].
  Proof using Type*.
    move=> [mind [_ [hall hck]]] nthe isty sp.
    have wfΓ : wf_localE Σ Γ := isType_wf_localE isty.
    assert (clΓ : is_closed_context Γ) by exact (wf_local_closed_contextE wfΓ).
    assert (opd : is_open_term Γ (dtype decl)) by exact (PCUICClosedTypEta.isType_is_open_termE isty).
    eapply nth_error_all in hall; tea.
    destruct (BDFromPCUICEta.mfix_body_on_conv_redE_cofix wfΓ isty hall) as [tw [ck r]].
    have r' : Σ ;;; Γ ⊢ dtype decl ⇝ tw := into_closed_red r clΓ opd.
    assert (istw : isTypeE Σ Γ tw) by exact (isType_redE isty r).
    exists mind, tw; split => //.
    eapply typing_spine_strengthenE; [exact sp|exact istw|].
    now eapply red_ws_cumul_pbE_inv.
  Qed.

  (** Base [cumul_it_mkProd_or_LetIn_smash] ([:164]). *)
  Lemma cumul_it_mkProd_or_LetIn_smashE Γ Δ T :
    is_closed_context Γ ->
    is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
    Σ ;;; Γ ⊢E it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T) = it_mkProd_or_LetIn Δ T.
  Proof using Type*.
    intros clΓ clp. symmetry. eapply red_ws_cumul_pbE.
    now apply red_it_mkProd_or_LetIn_to_smashE.
  Qed.

  (** Base [typing_spine_smash] ([:173]). *)
  Lemma typing_spine_smashE Γ Δ T args T' :
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'.
  Proof using Type*.
    intros sp.
    pose proof (typing_spine_isType_domE sp) as ty.
    pose proof (red_it_mkProd_or_LetIn_to_smashE (wfΣ := wfΣ) Γ Δ T
      (wf_local_closed_contextE (isType_wf_localE ty)) (PCUICClosedTypEta.isType_is_open_termE ty)) as r.
    eapply typing_spine_strengthenE; tea.
    eapply isType_redE; tea. eapply r.
    eapply ws_cumul_pbE_eq_le; symmetry.
    now eapply red_ws_cumul_pbE.
  Qed.

  (** Base [typing_spine_nth_error] ([:195]); the twin of [PCUICSpine.typing_spine_nth_error]
      is [PCUICSpineEta.typing_spine_nth_errorE]. *)
  Lemma typing_spine_nth_errorE Γ Δ T args T' n arg decl :
    assumption_context Δ ->
    wf_localE Σ (Γ ,,, Δ) ->
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = Some arg ->
    nth_error (List.rev Δ) n = Some decl ->
    Σ ;;; Γ |-E arg : subst (List.rev (firstn n args)) 0 decl.(decl_type).
  Proof.
    intros ass wf sp hnth hdecl.
    eapply PCUICSpineEta.typing_spine_nth_errorE in sp; tea.
    2:{ eapply nth_error_Some_length in hdecl. len in hdecl.
        move: (context_assumptions_bound Δ).
        pose proof (assumption_context_assumptions ass). lia. }
    destruct sp as [decl' [hdecl' harg]].
    pose proof (nth_error_Some_length hdecl).
    rewrite (smash_assumption_context _ ass) in hdecl'.
    rewrite nth_error_rev // List.rev_involutive in hdecl.
    len in hdecl. rewrite (assumption_context_assumptions ass) in hdecl'.
    rewrite hdecl in hdecl'. noconf hdecl'. exact harg.
  Qed.

  (** Base [typing_spine_all_inv] ([:216]). *)
  Lemma typing_spine_all_invE Γ Δ T args T' :
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    #|args| = context_assumptions Δ ->
    (Σ ;;; Γ ⊢E subst (List.rev args) 0 (expand_lets Δ T) ≤ T') * (isTypeE Σ Γ T').
  Proof.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    induction Δ in args, T |- * using ctx_length_rev_ind.
    - simpl. destruct args => // sp _ /=; rewrite subst_empty expand_lets_nil.
      now depelim sp.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_invE in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp).
        forward X by now len.
        now rewrite expand_lets_vdef.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => hargs. simpl in hargs.
        rewrite Nat.add_1_r in hargs. destruct args => //.
        depelim sp. noconf hargs.
        eapply ws_cumul_pbE_Prod_Prod_inv in w as [eqna dom codom].
        rewrite expand_lets_vass. simpl.
        eapply (substitution0_ws_cumul_pbE (t:=t)) in codom; [|now eapply subject_is_open_termE].
        eapply typing_spine_strengthenE in sp. 3:tea.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [t] 0 Γ0) ltac:(len; reflexivity) (subst [t] #|Γ0| T) _ sp).
        forward X by now len.
        rewrite subst_app_simpl /=; len; rewrite H.
        now rewrite -(expand_lets_subst_comm _ _ _).
        eapply isType_applyE in i; tea.
        eapply (type_ws_cumul_pbE (pb:=Conv)); tea. 2:now symmetry.
        eapply isTypeRelE_isTypeE.
        now eapply isType_tProdE in i as [].
  Qed.

  (** Base [typing_spine_more_inv] ([:251]). *)
  Lemma typing_spine_more_invE Γ Δ ind u args args' T' :
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
    #|args'| > context_assumptions Δ -> False.
  Proof.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    induction Δ in args, args' |- * using ctx_length_rev_ind.
    - simpl. destruct args' using rev_case => /= // sp hargs // /=; try lia.
      depelim sp. eapply (f_equal (@length _)) in H; simpl in H; len in H; simpl in H.
      now eapply invert_cumul_ind_prodE in w.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_invE in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp). now len.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => /= hargs.
        rewrite Nat.add_1_r in hargs. destruct args'; simpl in * => //. lia.
        depelim sp.
        eapply ws_cumul_pbE_Prod_Prod_inv in w as [eqna dom codom].
        eapply (substitution0_ws_cumul_pbE (t:=t)) in codom; [|now eapply subject_is_open_termE].
        eapply typing_spine_strengthenE in sp. 3:tea.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [t] 0 Γ0) ltac:(len; reflexivity) _ _ sp).
        now len.
        eapply isType_applyE in i; tea.
        eapply (type_ws_cumul_pbE (pb:=Conv)); tea. 2:now symmetry.
        eapply isTypeRelE_isTypeE.
        now eapply isType_tProdE in i as [].
  Qed.

  (** Base [typing_spine_nth_error_None] ([:302]). *)
  Lemma typing_spine_nth_error_NoneE Γ Δ T args T' :
    assumption_context Δ ->
    wf_localE Σ (Γ ,,, Δ) ->
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args #|Δ| = None ->
    Σ ;;; Γ ⊢E (subst0 (List.rev args) (it_mkProd_or_LetIn (firstn (#|Δ| - #|args|) Δ) T)) ≤ T'.
  Proof.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    induction Δ in args, T |- * using ctx_length_rev_ind.
    { intros. eapply nth_error_None in H0. simpl in H0 |- *. destruct args => //; simpl in H0; try lia.
      rewrite subst_empty. simpl in X0. now depelim X0. }
    destruct d as [na [b|] ty]; intros ass; eapply assumption_context_app in ass as [assΓ ass].
    * exfalso; depelim ass.
    * simpl. rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= //.
      intros wf sp.
      pose proof (All_local_env_app_inv wf) as [_ wfty].
      eapply All_local_env_app_inv in wfty as [wfty _]. depelim wfty.
      intros Hargs. eapply nth_error_None in Hargs.
      len in Hargs. len; simpl.
      depelim sp.
      + simpl. rewrite subst_empty. simpl; len.
        simpl. rewrite Nat.sub_0_r firstn_app_2. simpl.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        exact w.
      + eapply ws_cumul_pbE_Prod_Prod_inv in w as [eqna dom codom].
        assert (Σ ;;; Γ |-E hd : ty).
        { eapply type_ws_cumul_pbE; tea.
          - eapply isTypeRelE_isTypeE. now eapply isType_tProdE in i as [].
          - eapply ws_cumul_pbE_eq_le. now symmetry. }
        eapply (substitution0_ws_cumul_pbE (t:=hd)) in codom; [|now eapply subject_is_open_termE].
        eapply typing_spine_strengthenE in sp. 3:eauto.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        simpl. replace (#|Γ0| + 1 - S #|tl|) with (#|Γ0| - #|tl|) by lia.
        rewrite firstn_app. rewrite (firstn_0 _ (_ - _ - _)); try lia; rewrite app_nil_r.
        move: Hargs; simpl; rewrite Nat.add_1_r => hlen.
        specialize (X (subst_context [hd] 0 Γ0) ltac:(len; reflexivity) (subst [hd] #|Γ0| T) tl).
        forward X by now eapply assumption_context_fold.
        forward X.
        { eapply substitution_wf_localE; eauto. constructor. constructor. now rewrite subst_empty.
          now rewrite app_context_assoc in wf. }
        specialize (X sp).
        forward X. len. apply nth_error_None. lia.
        rewrite subst_app_simpl.
        simpl. rewrite subst_it_mkProd_or_LetIn.
        simpl. len.
        len in X.
        rewrite firstn_length_le. lia.
        replace (#|Γ0| - #|tl| + #|tl|)%nat with #|Γ0| by lia.
        rewrite firstn_subst_context in X => //.
        eapply isType_applyE; tea.
  Qed.

  (** Base [typing_spine_nth_error_None_prod] ([:363]). *)
  Lemma typing_spine_nth_error_None_prodE Γ Δ T args T' n decl :
    assumption_context Δ ->
    wf_localE Σ (Γ ,,, Δ) ->
    PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = None ->
    nth_error (List.rev Δ) n = Some decl ->
    ∑ na dom codom, Σ ;;; Γ ⊢E tProd na dom codom ≤ T'.
  Proof.
    intros ass wf sp nth nth'.
    eapply typing_spine_nth_error_NoneE in sp; eauto;
    eapply nth_error_None in nth;
    eapply nth_error_Some_length in nth'; len in nth'.
    rewrite subst_it_mkProd_or_LetIn in sp.
    2:{ eapply nth_error_None. lia. }
    set (ctx := subst_context (List.rev args) 0 (firstn (#|Δ| - #|args|) Δ)) in *.
    assert (#|ctx| > 0).
    { rewrite /ctx; len. rewrite firstn_length_le; lia. }
    assert (assumption_context ctx).
    { rewrite /ctx. apply assumption_context_fold. now apply assumption_context_firstn. }
    destruct ctx using rev_case; simpl in *. lia.
    rewrite it_mkProd_or_LetIn_app in sp.
    move/assumption_context_app: H0 => [ass' assx].
    destruct x as [na [b|] ty]. exfalso. depelim assx.
    rewrite /mkProd_or_LetIn in sp.
    eexists _, _, _; eauto. eapply sp.
  Qed.

  (** Base [wf_fixpoint_spine] ([:390]). *)
  Lemma wf_fixpoint_spineE Γ mfix idx decl args ty :
    wf_fixpointE Σ Γ mfix ->
    nth_error mfix idx = Some decl ->
    isTypeE Σ Γ (dtype decl) ->
    PCUICAritiesEta.typing_spineE Σ Γ (dtype decl) args ty ->
    match nth_error args decl.(rarg) with
    | Some arg =>
      ∑ ind u indargs,
      (Σ ;;; Γ |-E arg : mkApps (tInd ind u) indargs) *
      check_recursivity_kind (lookup_env Σ) (inductive_mind ind) Finite
    | None => ∑ na dom codom, Σ ;;; Γ ⊢E tProd na dom codom ≤ ty
    end.
  Proof using Type*.
    move=> [_ [_ hm]] nthe isty sp.
    destruct (mfix_on_ind_spine_witnessE_fix _ _ _ _ _ _ hm nthe isty sp)
      as [mind' [tw [r cfix ck istw sp']]].
    clear sp isty. rename sp' into sp.
    destruct decl as [dna dty dbod rarg]; cbn in *.
    rewrite /check_one_fix /def_with_type /= in cfix.
    case E: (decompose_prod_assum [] tw) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst tw.
    destruct (nth_error _ rarg) eqn:Hnth => //.
    pose proof (nth_error_Some_length Hnth).
    len in H. simpl in H.
    eapply typing_spine_smashE in sp.
    destruct (nth_error args rarg) eqn:hargs.
    - (* This file's [typing_spine_nth_errorE] (above), not [PCUICSpineEta]'s: while its
         Section is open it is named by the Section's name, [SpinesE.typing_spine_nth_errorE]. *)
      eapply SpinesE.typing_spine_nth_errorE in sp; eauto; cycle 1.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_endE; eauto.
        destruct istw as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetInE in Hs; eauto.
        now eapply typingE_wf_local.
      * destruct (decompose_app (decl_type c)) as [hd tl] eqn:da.
        destruct (destInd hd) as [[i u]|] eqn:di => //.
        destruct i as [mind i]. noconf cfix.
        eapply decompose_app_inv in da. rewrite da in sp.
        rewrite subst_mkApps in sp.
        destruct hd => //; noconf di. simpl in sp.
        eexists _, ui, _; intuition eauto.
    - eapply typing_spine_nth_error_None_prodE in sp; eauto.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_endE; eauto.
        destruct istw as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetInE in Hs; eauto.
        now eapply typingE_wf_local.
  Qed.

  (** Base [wf_cofixpoint_spine] ([:441]). *)
  Lemma wf_cofixpoint_spineE Γ mfix idx decl args ty :
    wf_cofixpointE Σ Γ mfix ->
    nth_error mfix idx = Some decl ->
    isTypeE Σ Γ (dtype decl) ->
    PCUICAritiesEta.typing_spineE Σ Γ (dtype decl) args ty ->
    ∑ Γ' T, (Σ ;;; Γ ⊢ dtype decl ⇝ it_mkProd_or_LetIn Γ' T) *
    ∑ ind u indargs, (T = mkApps (tInd ind u) indargs) *
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite *
    if #|args| <? context_assumptions Γ' then
      (Σ ;;; Γ ⊢E subst0 (List.rev args)
      (it_mkProd_or_LetIn (firstn (context_assumptions Γ' - #|args|) (smash_context [] Γ'))
        (expand_lets Γ' T)) ≤ ty)
    else
      (#|args| = context_assumptions Γ') *
      (Σ ;;; Γ ⊢E subst (List.rev args) 0 (expand_lets Γ' T) ≤ ty).
  Proof using Type*.
    move=> hm nthe isty sp.
    destruct (mfix_on_ind_spine_witnessE_cofix _ _ _ _ _ _ hm nthe isty sp)
      as [mind' [tw [r cfix ck istw sp']]].
    clear sp isty. rename sp' into sp. cbn in ck.
    rewrite /check_one_cofix /def_with_type /= in cfix.
    case E: (decompose_prod_assum [] tw) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst tw. exists Γ', concl. split; auto.
    destruct (decompose_app concl) as [hd tl] eqn:da.
    destruct (destInd hd) as [[mind i]|] eqn:di => //.
    destruct mind => //. destruct hd => //.
    noconf di. noconf cfix.
    eapply decompose_app_inv in da.
    eexists _, _, _; intuition eauto.
    destruct (Nat.ltb #|args| (context_assumptions Γ')) eqn:lt; [
      eapply Nat.ltb_lt in lt|eapply Nat.ltb_nlt in lt; destruct (Nat.eqb #|args| (context_assumptions Γ')) eqn:eq;
      [eapply Nat.eqb_eq in eq|eapply Nat.eqb_neq in eq]].
    - eapply typing_spine_smashE in sp.
      destruct (nth_error args #|args|) eqn:hargs.
      { rewrite (proj2 (nth_error_None _ _)) // in hargs. }
      destruct (nth_error (List.rev (smash_context [] Γ')) #|args|) as [decl'|] eqn:hnth.
      eapply typing_spine_nth_error_NoneE in sp; eauto.
      * len in sp.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_endE; eauto.
        destruct istw as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetInE in Hs; eauto.
        now eapply typingE_wf_local.
      * len; simpl. eapply nth_error_None in hargs => //.
        eapply nth_error_None. lia.
      * eapply nth_error_None in hnth => //. len in hnth.
    - eapply typing_spine_all_invE in sp => //.
      subst concl.
      rewrite expand_lets_mkApps subst_mkApps /= in sp.
      destruct sp. split; auto.
      now rewrite expand_lets_mkApps subst_mkApps /=.
    - subst concl; eapply typing_spine_more_invE in sp; try lia.
  Qed.

End SpinesE.

Section classificationE.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wfE Σ}.

  Notation wh_neutral := (whne RedFlags.default).
  Notation wh_normal := (whnf RedFlags.default).

  Transparent construct_cofix_discr.

  (** Base [value_whnf] ([:552]). *)
  Lemma value_whnfE t : closed t -> value Σ t -> wh_normal Σ [] t.
  Proof.
    intros cl ev.
    induction ev in cl |- * using value_values_ind.
    destruct t; simpl in H; try discriminate; try solve [constructor; constructor].
    - eapply (whnf_indapp _ _ [] _ _ []).
    - eapply (whnf_cstrapp _ _ [] _ _ _ []).
    - eapply (whnf_fixapp _ _ [] _ _ []).
      destruct nth_error as [rarg|] => /= //; [|easy].
      left ; eexists; split; eauto.
      now rewrite nth_error_nil.
    - eapply (whnf_cofixapp _ _ [] _ _ []).
    - eapply whnf_prim.
    - destruct X => //.
      pose proof cl as cl'.
      rewrite closedn_mkApps in cl'. move/andP: cl' => [clfix _].
      rewrite -closed_unfold_fix_cunfold_eq in e => //.
      rewrite /unfold_fix in e.
      destruct nth_error eqn:nth => //. noconf e.
      eapply whnf_fixapp. rewrite nth. left; eexists; split; eauto.
      now eapply nth_error_None.
  Qed.

  (** Base [eval_whne] ([:575]). *)
  Lemma eval_whneE t t' : closed t -> eval Σ t t' -> wh_normal Σ [] t'.
  Proof.
    intros cl ev.
    pose proof (eval_closed_cb Σ _ _ cl ev).
    eapply eval_to_value in ev.
    now eapply value_whnfE.
  Qed.

  (** Base [typing_var] ([:583]). *)
  Lemma typing_varE {Γ n ty} : Σ ;;; Γ |-E (tVar n) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  (** Base [typing_evar] ([:586]). *)
  Lemma typing_evarE {Γ n l ty} : Σ ;;; Γ |-E (tEvar n l) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  (** Base [typing_cofix_coind] ([:589]). *)
  Lemma typing_cofix_coindE {Γ mfix idx args ind u indargs} :
    Σ ;;; Γ |-E mkApps (tCoFix mfix idx) args : mkApps (tInd ind u) indargs ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.
  Proof using Type*.
    intros tyarg.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    eapply inversion_mkAppsE in tyarg as [A [Hcof sp]]; auto.
    eapply inversion_CoFixE in Hcof as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto.
    simpl in a.
    apply isTypeRelE_isTypeE in a.
    eapply typing_spine_strengthenE in sp; eauto.
    eapply wf_cofixpoint_spineE in sp as (Γ' & concl & _ & ?); eauto.
    move: s => [ind' [u' [indargs' [[ceq ccum] ck]]]].
    subst concl.  move: ck.
    elim: Nat.ltb_spec => Hargs.
    - rewrite subst_it_mkProd_or_LetIn; len.
      set (ctx := subst_context _ _ _).
      assert(assumption_context ctx).
      eapply assumption_context_fold, assumption_context_firstn, smash_context_assumption_context; constructor.
      assert (#|ctx| > 0).
      { rewrite /ctx; len; rewrite firstn_length_le. len; lia. lia. }
      destruct ctx as [|ctx [na [b|] ty]] using rev_case. simpl in H0; lia.
      exfalso; move/assumption_context_app: H => [ass assd]; depelim assd.
      move/assumption_context_app: H => [ass assd]; depelim assd.
      rewrite it_mkProd_or_LetIn_app /mkProd_or_LetIn /= => cum.
      now eapply invert_cumul_prod_indE in cum.
    - move=> [hargs ccum'].
      rewrite expand_lets_mkApps subst_mkApps /= in ccum'.
      eapply invert_cumul_ind_indE in ccum' as ((hind & r) & _).
      eapply ReflectEq.eqb_eq in hind. now subst ind'.
  Qed.

  (** Base [check_recursivity_kind_inj] ([:621]). *)
  Lemma check_recursivity_kind_injE {mind rk rk'} :
    check_recursivity_kind (lookup_env Σ) mind rk ->
    check_recursivity_kind (lookup_env Σ) mind rk' -> rk = rk'.
  Proof.
    rewrite /check_recursivity_kind.
    case: lookup_env => //; case => // m.
    elim: ReflectEq.eqb_spec;
    elim: ReflectEq.eqb_spec; congruence.
  Qed.

  (** Base [wt_closed_red_refl] ([:631]). *)
  Lemma wt_closed_red_reflE {Γ t T} : Σ ;;; Γ |-E t : T -> Σ ;;; Γ ⊢ t ⇝ t.
  Proof.
    intros Hs.
    eapply closed_red_refl.
    now eapply typingE_wf_local, wf_local_closed_contextE in Hs.
    now eapply subject_is_open_termE.
  Qed.

  (** Base [invert_ind_ind] ([:639]). *)
  Lemma invert_ind_indE Γ ind u args ind' u' args' :
    Σ;;; Γ |-E mkApps (tInd ind u) args : mkApps (tInd ind' u') args' -> False.
  Proof using Type*.
    intros typ.
    eapply inversion_mkAppsE in typ as (?&?&?); auto.
    eapply inversion_IndE in t as (?&?&wfΓ&decl&cu&?); auto.
    eapply typing_spine_strengthenE in t0; eauto.
    eapply (typing_spine_ind_type_invE decl) in t0; tea.
    rewrite it_mkProd_or_LetIn_app !subst_instance_it_mkProd_or_LetIn in t0.
    eapply typing_spine_arity_mkApps_IndE in t0; eauto.
    eapply typing_spine_isType_domE in t0 as (_ & s & Hs & _).
    eexists; split; [sq|].
    - now eapply wt_closed_red_reflE.
    - now do 2 eapply isArity_it_mkProd_or_LetIn.
    - now eapply isTypeRelE_isTypeE, (declared_inductive_valid_typeE decl).
  Qed.

  (** Base [invert_fix_ind] ([:655]). *)
  Lemma invert_fix_indE Γ mfix i args ind u args' :
    match unfold_fix mfix i with
    | Some (rarg, _) => nth_error args rarg = None
    | _ => True
    end ->
    Σ;;; Γ |-E mkApps (tFix mfix i) args : mkApps (tInd ind u) args' -> False.
  Proof using Type*.
    intros no_arg typ.
    eapply inversion_mkAppsE in typ as (?&?&?); eauto.
    eapply inversion_FixE in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRelE_isTypeE in a.
    eapply typing_spine_strengthenE in t0; eauto.
    unfold unfold_fix in no_arg.
    rewrite e in no_arg.
    eapply (wf_fixpoint_spineE wfΣ) in t0; eauto.
    rewrite no_arg in t0. destruct t0 as [na [dom [codom cum]]].
    now eapply invert_cumul_prod_indE in cum.
  Qed.

  (** Base [wh_neutral_empty_gen] ([:688]). *)
  Lemma wh_neutral_empty_genE Γ free t ty :
    axiom_free_value Σ free t ->
    wh_neutral Σ [] t ->
    Σ ;;; Γ |-E t : ty ->
    Γ = [] ->
    False.
  Proof using Type*.
    intros axfree ne typed.
    induction ne in free, t, ty, axfree, ne, typed |- *; intros ->; simpl in *; try discriminate.
    - apply inversion_RelE in typed as (?&?&?&?); auto.
      rewrite nth_error_nil in e0; discriminate.
    - now eapply typing_varE in typed.
    - now eapply typing_evarE in typed.
    - apply inversion_ConstE in typed as [decl' [wfd [declc [cu cum]]]]; eauto.
      unshelve eapply declared_constant_to_gen in declc; eauto.
      red in declc. rewrite declc in e, axfree.
      noconf e.
      destruct decl; cbn in *.
      rewrite e0 in axfree; congruence.
    - eapply inversion_AppE in typed as [na [A [B [Hf _]]]]; eauto.
    - eapply inversion_mkAppsE in typed as (? & ? & ?); eauto.
      eapply inversion_FixE in t as (? & ? & ? & ? & ? & ? & ?); auto.
      eapply nth_error_all in a; eauto. apply isTypeRelE_isTypeE in a.
      eapply typing_spine_strengthenE in t0; eauto.
      rewrite /unfold_fix in e. rewrite e1 in e. noconf e.
      eapply (wf_fixpoint_spineE wfΣ) in t0; eauto.
      rewrite e0 in t0. destruct t0 as [ind [u [indargs [tyarg ckind]]]].
      rewrite axiom_free_value_mkApps in axfree.
      cbn in axfree.
      rewrite e1 nth_nth_error nth_error_app1 in axfree.
      1: { rewrite length_map.
           apply nth_error_Some_length in e0; auto. }
      rewrite nth_error_map e0 in axfree.
      cbn in axfree.
      eauto.
    - eapply inversion_CaseE in typed as (? & ? & ? & ? & [] & ?); tas; eauto.
    - eapply inversion_ProjE in typed as (? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    (* whne_primapp_stuck / whne_primapp_inert: the head is a bodiless
       registered constant, which [axiom_free_value] sends to [false]. *)
    - rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
    - rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
  Qed.

  (** Base [wh_neutral_empty] ([:735]). *)
  Lemma wh_neutral_emptyE t ty :
    axiom_free_value Σ [] t ->
    wh_neutral Σ [] t ->
    Σ ;;; [] |-E t : ty ->
    False.
  Proof using Type*. eauto using wh_neutral_empty_genE. Qed.

  (** Base [whnf_classification'] ([:742]). *)
  Lemma whnf_classification'E t i u args :
    axiom_free_value Σ [] t ->
    wh_normal Σ [] t ->
    Σ ;;; [] |-E t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t).
  Proof using Type*.
    intros axfree ne typed.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    pose proof (subject_closedE typed) as cl.
    depelim ne; simpl in *.
    - exfalso. eauto using wh_neutral_emptyE.
    - eapply inversion_SortE in typed as (? & ? & e); auto.
      now eapply invert_cumul_sort_indE in e.
    - eapply inversion_ProdE in typed as (? & ? & ? & ? & e); auto.
      now eapply invert_cumul_sort_indE in e.
    - eapply inversion_LambdaE in typed as (? & ? & ? & e); auto.
      now eapply invert_cumul_prod_indE in e.
    - now rewrite head_mkApps /= /head /=.
    - exfalso; eapply invert_ind_indE; eauto.
    - exfalso; eapply invert_fix_indE; eauto.
      unfold unfold_fix. destruct nth_error; [|easy].
      destruct o as [[? [? ?]]|]; [|easy]. inversion H; eauto.
    - now rewrite head_mkApps /head /=.
    - eapply inversion_PrimE in typed as [prim_ty [cdecl [? hpc ? ? hp]]]; eauto.
      (* The guard on the axiom inversions: prim_ty is a registered primitive
         TYPE constant, which §4.2(a)1 keeps out of the operation table. *)
      assert (hnop : prim_op_of Σ prim_ty = None).
      { pose proof wfΣ as [_ [wfr _]].
        exact (prim_op_of_primitive_constant _ _ _ wfr hpc). }
      destruct p as [? []]; simp prim_type in w.
      1-3:eapply (invert_cumul_axiom_indE (args := [])) in w; eauto; destruct p0 as [? []]; eauto.
      eapply (invert_cumul_axiom_indE (args := [array_type a0])) in w; eauto. destruct p0 as [s []]; eauto.
    (* whnf_primapp_partial / whnf_primapp_rigid: the head is a bodiless
       registered constant, which [axiom_free_value] sends to [false]. *)
    - exfalso. rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
    - exfalso. rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
  Qed.

  (** Base [whnf_classification] ([:783]). *)
  Lemma whnf_classificationE t i u args :
    axiom_free Σ ->
    wh_normal Σ [] t ->
    Σ ;;; [] |-E t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t).
  Proof using Type*.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply whnf_classification'E; eauto.
  Qed.

  (** Base [ind_whnf_classification'] ([:796]). *)
  Lemma ind_whnf_classification'E t ind u indargs :
    axiom_free_value Σ [] t -> notCoInductive Σ ind ->
    Σ ;;; [] |-E t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t.
  Proof using Type*.
    intros axfree ck typed whnf.
    rewrite /isConstruct_app.
    eapply whnf_classification'E in whnf; eauto.
    rewrite /head in whnf.
    destruct (decompose_app t) as [hd tl] eqn:da; simpl in *.
    destruct hd eqn:eqh => //. subst hd.
    eapply decompose_app_inv in da. subst.
    eapply typing_cofix_coindE in typed.
    congruence.
  Qed.

  (** Base [ind_whnf_classification] ([:813]). *)
  Lemma ind_whnf_classificationE t ind u indargs :
    axiom_free Σ -> notCoInductive Σ ind ->
    Σ ;;; [] |-E t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t.
  Proof using Type*.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply ind_whnf_classification'E; eauto.
  Qed.

  (** Base [fix_app_is_constructor] ([:823]). *)
  Lemma fix_app_is_constructorE {mfix idx args ty narg fn} :
    Σ;;; [] |-E mkApps (tFix mfix idx) args : ty ->
    unfold_fix mfix idx = Some (narg, fn) ->
    match nth_error args narg return Type with
    | Some a => axiom_free_value Σ [] a -> wh_normal Σ [] a -> isConstruct_app a
    | None => ∑ na dom codom, Σ ;;; [] ⊢E tProd na dom codom ≤ ty
    end.
  Proof using Type*.
    intros typed unf.
    eapply inversion_mkAppsE in typed as (? & ? & ?); eauto.
    eapply inversion_FixE in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRelE_isTypeE in a.
    eapply typing_spine_strengthenE in t0; eauto.
    rewrite /unfold_fix in unf. rewrite e in unf.
    noconf unf.
    eapply (wf_fixpoint_spineE wfΣ) in t0; eauto.
    rewrite /is_constructor. destruct (nth_error args (rarg x0)) eqn:hnth; [|assumption].
    destruct_sigma t0.
    intros axfree norm.
    eapply ind_whnf_classification'E in t1; eauto.
    intros chk.
    pose proof (check_recursivity_kind_injE chk t0).
    discriminate.
  Qed.

  (** Evaluation on well-typed terms corresponds to reduction (base comment, [:869]). *)

  Import PCUICGlobalEnv.

  (** Base [wcbveval_red] ([:878]). *)
  Lemma wcbveval_redE t ty u :
    Σ ;;; [] |-E t : ty ->
    eval Σ t u -> red Σ [] t u.
  Proof using Type*.
    intros Hc He.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    revert ty Hc.
    induction He; simpl; move=> ty Ht;
      try solve[econstructor; eauto].

    - eapply inversion_AppE in Ht as (? & ? & ? & ? & ? & ?); auto.
      redt (tApp (tLambda na t b) a); eauto.
      eapply red_app; eauto.
      redt (tApp (tLambda na t b) a'). eapply red_app; eauto.
      specialize (IHHe1 _ t0). specialize (IHHe2 _ t1).
      redt (csubst a' 0 b).
      rewrite (closed_subst a' 0 b).
      eapply eval_closed_cb; eauto. now eapply subject_closedE in t1.
      eapply red1_red. constructor.
      pose proof (subject_closedE t1); auto.
      eapply eval_closed_cb in H; eauto.
      eapply subject_reductionE in IHHe1. 2-3:eauto.
      eapply inversion_LambdaE in IHHe1 as (? & ? & ? & e); eauto.
      eapply (substitution0E (Γ := [])) in t2; eauto.
      eapply IHHe3.
      rewrite (closed_subst a' 0 b); auto.
      rewrite /subst1 in t2. eapply t2.
      eapply (type_ws_cumul_pbE (pb:=Conv)); eauto.
      eapply subject_reductionE in IHHe2; eauto.
      now eapply isTypeRelE_isTypeE.
      eapply ws_cumul_pbE_Prod_Prod_inv in e as [eqna dom codom]; eauto.
      now symmetry.

    - eapply inversion_LetInE in Ht as (? & ? & ? & ?); auto.
      apply unlift_TermTyp in l as t0'.
      redt (tLetIn na b0' t b1); eauto.
      eapply red_letin; eauto.
      redt (b1 {0 := b0'}); auto.
      do 2 econstructor.
      specialize (IHHe1 _ t0').
      rewrite /subst1.
      rewrite -(closed_subst b0' 0 b1).
      eapply subject_reductionE in t0'; eauto. eapply subject_closedE in t0'; eauto.
      eapply IHHe2.
      rewrite closed_subst.
      eapply subject_reductionE in t0'; eauto. eapply subject_closedE in t0'; eauto.
      pose proof (subject_is_open_termE t0).
      eapply substitution_letE in t0; eauto.
      eapply subject_reductionE in t0.
      3:{ eapply (red_red_cb (Δ := [vass na t]) (Γ' := [])); eauto. 3:repeat constructor.
          cbn. rewrite addnP_shiftnP. eapply type_is_open_termE in t0'. now erewrite t0'.
          repeat constructor. cbn. rewrite addnP_shiftnP.
          eapply subject_is_open_termE in t0'. cbn in t0'. now setoid_rewrite shiftnP0 in t0'. }
      apply t0. auto.

    - redt (subst_instance u body); auto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.
      eapply IHHe. eapply subject_reductionE; eauto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.

    - epose proof (subject_reductionE Σ [] _ _ _ wfΣ Ht).
      apply inversion_CaseE in Ht; auto. destruct_sigma Ht.
      unshelve epose proof (isdecl_ := declared_inductive_to_gen isdecl); eauto.
      destruct (declared_inductive_inj d isdecl_); subst mdecl0 idecl0.
      destruct c0.
      specialize (IHHe1 _ scrut_ty).
      assert (red Σ [] (tCase ci p discr brs) (iota_red ci.(ci_npar) p args br)).
      { clear X. redt _.
        eapply red_case; eauto.
        eapply All2_refl; intros; eauto. red.
        eapply All2_refl; split; reflexivity.
        eapply red1_red. destruct p => /= //.
        eapply red_iota; tea.
        rewrite e1 /cstr_arity eq_npars e3 //. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reductionE Σ [] _ _ _ wfΣ Ht).
      apply inversion_ProjE in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      assert (red Σ [] (tProj p discr) a).
      { redt _.
        eapply red_proj_c; eauto.
        eapply red1_red; constructor; auto. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reductionE Σ [] _ _ _ wfΣ Ht).
      apply inversion_AppE in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      epose proof (subject_reductionE Σ [] _ _ _ wfΣ t IHHe1) as Ht2.
      epose proof (subject_reductionE Σ [] _ _ _ wfΣ t0 IHHe2) as Ha2.
      assert (red Σ [] (tApp f4 a) (tApp (mkApps fn argsv) av)).
      { redt _.
        eapply red_app; eauto.
        rewrite -![tApp _ _](mkApps_app _ _ [_]).
        eapply red1_red.
        rewrite -closed_unfold_fix_cunfold_eq in e1.
        { eapply subject_closedE in Ht2; auto.
          rewrite closedn_mkApps in Ht2. now move/andP: Ht2 => [clf _]. }
        eapply red_fix; eauto.
        assert (Σ ;;; [] |-E mkApps (tFix mfix idx) (argsv ++ [av]) : B {0 := av}).
        { rewrite mkApps_app /=. eapply type_App'E; eauto. }
        epose proof (fix_app_is_constructorE X0 e1); eauto.
        rewrite /is_constructor.
        destruct nth_error eqn:hnth => //.
        2:{ eapply nth_error_None in hnth. len in hnth. }
        assert (All (closedn 0) (argsv ++ [av])).
        { eapply subject_closedE in X0; eauto.
          rewrite closedn_mkApps in X0.
          move/andP: X0 => [clfix clargs].
          now eapply forallb_All in clargs. }
        assert (All (value Σ) (argsv ++ [av])).
        { eapply All_app_inv; [|constructor; [|constructor]].
          eapply eval_to_value in He1.
          eapply value_mkApps_inv in He1 as [[-> Hat]|[vh vargs]] => //.
          now eapply eval_to_value in He2. }
        solve_all.
        eapply nth_error_all in X3; eauto. simpl in X3.
        destruct X3 as [cl val]. eapply X1, value_whnfE; auto.
        now eapply value_axiom_free. }
      redt _; eauto.

    - apply inversion_AppE in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      now eapply red_app.

    - epose proof (subject_reductionE Σ [] _ _ _ wfΣ Ht).
      apply inversion_CaseE in Ht; auto; destruct_sigma Ht.
      destruct c.
      specialize (IHHe1 _ scrut_ty).
      unshelve epose proof (subject_reductionE Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closedE X0).
      etransitivity. eapply red_case_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)).
      { eapply red1_red. eapply red_cofix_case.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
      redt _; eauto.
      eapply IHHe2.
      eapply subject_reductionE. 3: eapply X1. eauto.
      eapply subject_reductionE. 3: eapply red_case_c; eauto. all:eauto.
    - epose proof (subject_reductionE Σ [] _ _ _ wfΣ Ht).
      apply inversion_ProjE in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      unshelve epose proof (subject_reductionE Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closedE X0).
      etransitivity. eapply red_proj_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))).
      { eapply red1_red. eapply red_cofix_proj.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
        redt _; eauto.
      eapply IHHe2.
      eapply subject_reductionE. 3: eapply X1. eauto.
      eapply subject_reductionE. 3: eapply red_proj_c; eauto. all:eauto.

    - eapply inversion_AppE in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      rewrite mkApps_app /=. now eapply red_app.

    - eapply inversion_AppE in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      now eapply red_app.

    - eapply inversion_PrimE in Ht as [prim_type [decl []]]; eauto.
      depelim X. 1-3:reflexivity.
      depelim p1. specialize (r _ hdef).
      eapply red_primArray_congr; eauto.
      eapply All2_undep in a. solve_all.
  Qed.

  (** Base [subject_reduction_eval] ([:1055]). *)
  Theorem subject_reduction_evalE {t u T} :
    Σ ;;; [] |-E t : T -> eval Σ t u -> Σ ;;; [] |-E u : T.
  Proof using Type*.
    intros Hty Hred.
    eapply wcbveval_redE in Hred; eauto. eapply subject_reductionE; eauto.
  Qed.

  (** Base [value_classification] ([:1062]). *)
  Lemma value_classificationE {t i u args} :
    Σ ;;; [] |-E t : mkApps (tInd i u) args ->
    value Σ t ->
    construct_cofix_discr (head t).
  Proof using Type*.
    intros Ht Hvalue.
    eapply value_axiom_free in Hvalue as H.
    eapply whnf_classification'E; eauto.
    eapply eval_whneE.
    2: eapply value_final; eauto.
    eapply @subject_closedE with (Γ := []); eauto.
  Qed.

  (** Base [eval_classification] ([:1075]). *)
  Lemma eval_classificationE {t i u args} :
    Σ ;;; [] |-E t : mkApps (tInd i u) args ->
    forall t', eval Σ t t' ->
    construct_cofix_discr (head t').
  Proof using Type*.
    intros Ht t' eval.
    pose proof (subject_closedE Ht).
    eapply subject_reductionE in Ht. 3:eapply wcbveval_redE; eauto. 2:auto.
    eapply eval_to_value in eval as axfree.
    eapply value_axiom_free in axfree.
    eapply eval_whneE in eval; auto.
    eapply whnf_classification'E; eauto.
  Qed.

End classificationE.

End ClassificationEta.

(** ** The untyped arity corollaries are false over η

  Witness: [λx:Prop. (tSort Prop) x] ([cl_T]), η-related to the arity [tSort Prop] in both
  directions by one η step on [canon cl_T], and red-normal, so it reduces only to itself, a λ,
  which is not an arity. The witness is ill-typed: these theorems refute only the untyped
  forms; the typed forms are [invert_cumul_arity_lE] and [invert_cumul_arity_rE] above. *)
Section ArityWitness.
  #[local] Existing Instance default_checker_flags.

  Definition cl_Σ : global_env_ext := (empty_global_env, Monomorphic_ctx).
  Definition cl_T : term := tLambda c1b_na (tSort sProp) (tApp (tSort sProp) (tRel 0)).

  Lemma cl_T_normal Σ v : red1 Σ [] cl_T v -> False.
  Proof.
    unfold cl_T. intros H. inv_red H.
    - eapply red_normal_Sort; eassumption.
    - inv_red H.
      + eapply red_normal_Sort; eassumption.
      + eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma cl_premise_l pb : ws_cumul_pbE pb cl_Σ [] (tSort sProp) cl_T.
  Proof.
    constructor; try reflexivity.
    exists (tSort sProp), (tSort sProp). split; [|split].
    - apply rt_refl.
    - apply rt_step; right. cbn. exact (eta_red canon_la (tSort sProp) canon_dom).
    - apply compare_term_eta_refl.
  Qed.

  Lemma cl_premise_r pb : ws_cumul_pbE pb cl_Σ [] cl_T (tSort sProp).
  Proof.
    constructor; try reflexivity.
    exists (tSort sProp), (tSort sProp). split; [|split].
    - apply rt_step; right. cbn. exact (eta_red canon_la (tSort sProp) canon_dom).
    - apply rt_refl.
    - apply compare_term_eta_refl.
  Qed.

  Lemma cl_not_conv_to_arity : Is_conv_to_Arity cl_Σ [] cl_T -> False.
  Proof.
    intros (T' & [r] & a).
    have e := rt_from_normal _ _ _ (cl_T_normal cl_Σ) (clrel_rel r).
    subst T'. cbn in a. discriminate a.
  Qed.

End ArityWitness.

(** i21 without [isTypeE Σ Γ T] (base [PCUICConversion.invert_cumul_arity_l] over
    [ws_cumul_pbE], under [wfE]). *)
Theorem invert_cumul_arity_lE_untyped_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) Γ C T,
     isArity C -> Σ ;;; Γ ⊢E C ≤ T -> Is_conv_to_Arity Σ Γ T) -> False.
Proof.
  intros H. apply cl_not_conv_to_arity.
  exact (H default_checker_flags cl_Σ (wf_incl_E (@wf_empty_global_env default_checker_flags))
           [] (tSort sProp) cl_T eq_refl (cl_premise_l Cumul)).
Qed.

(** i20 without [isTypeE Σ Γ C] (base [PCUICConversion.invert_cumul_arity_r] over
    [ws_cumul_pbE], under [wfE]). *)
Theorem invert_cumul_arity_rE_untyped_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) Γ C T,
     isArity T -> Σ ;;; Γ ⊢E C ≤ T -> Is_conv_to_Arity Σ Γ C) -> False.
Proof.
  intros H. apply cl_not_conv_to_arity.
  exact (H default_checker_flags cl_Σ (wf_incl_E (@wf_empty_global_env default_checker_flags))
           [] cl_T (tSort sProp) eq_refl (cl_premise_r Cumul)).
Qed.
