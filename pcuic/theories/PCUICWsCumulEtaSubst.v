(* Distributed under the terms of the MIT license. *)

(** * A7: substitution, weakening and universe instances for [ws_cumul_pbE]

  New statements over [JoinE]; base lemmas by import only.

  - [finst_inst]: U1' is stable under any parallel substitution [inst σ] (so under
    [subst] and [lift]): the same [σ] on both sides, compared by reflexivity.
  - [JoinE_map]: a term map that sends scoped [red1] steps to [red] steps, [eta1] steps
    to [eta1] steps, commutes with [canon] up to equality, and preserves the final
    U1' comparison, transports joins.
  - [untyped_substitution_ws_cumul_pbE], [substitution_ws_cumul_pbE],
    [substitution0_ws_cumul_pbE] (vass, any open term: no typing premise),
    [substitution0_ws_cumul_pbE_vdef], [weakening_ws_cumul_pbE].
  - the let-body at [pb], which A5 does not give: [ws_cumul_pbE_LetIn_bo_pb],
    [ws_cumul_pbE_LetIn_pb], [ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb] over every
    context.

**The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]);
  [untyped_subslet Γ s Δ] by [s := []], [Δ := []]; the scoping premises by any
  scoped context and terms; every [ws_cumul_pbE] premise by reflexivity; the
  [valid_constraints] premise of [subst_instance_ws_cumul_pbE] by an environment
  without universe constraints. Instances: [PCUICEtaFracInstances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICSigmaCalculus PCUICEquality PCUICReduction PCUICOnFreeVars PCUICTyping
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICWellScopedCumulativity
     PCUICSubstitution PCUICConversion PCUICSpine PCUICUnivSubst PCUICUnivSubstitutionConv
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaConfluence
     PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICClosedBodies.

(** ** U1' under substitution *)

Section Inst.

  Context {cf : checker_flags} (Σ : global_env_ext) (r : finst_construct_rule).

  Local Notation RF pb n := (eq_term_upto_univ_eta_napp r Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).

  Lemma finst_inst pb n t u σ : RF pb n t u -> RF pb n t.[σ] u.[σ].
  Proof.
    intros h.
    induction t in u, pb, n, σ, h |- * using term_forall_list_ind.
    all: depelim h.
    all: try solve [ simpl ; constructor ; eauto ].
    - simpl. apply compare_term_eta_refl.
    - simpl. constructor.
      induction X in a, args' |- *.
      + inversion a. constructor.
      + inversion a. subst. simpl. constructor.
        all: eauto.
    - simpl. constructor. all: eauto.
      * rewrite /inst_predicate.
        destruct X; destruct e as [? [? [ectx ?]]].
        rewrite (All2_length ectx). red.
        intuition auto; simpl; solve_all.
      * unfold eq_branches, eq_branch in *; solve_all.
        rewrite (All2_length a1).
        now eapply b0.
    - simpl. constructor.
      apply All2_length in e as eq. rewrite <- eq.
      generalize #|m|. intro k. unfold eq_mfixpoint in *.
      eapply All2_map. simpl. solve_all.
    - simpl. constructor.
      apply All2_length in e as eq. rewrite <- eq.
      generalize #|m|. intro k. unfold eq_mfixpoint in *.
      eapply All2_map. simpl. solve_all.
    - simpl. constructor.
      eapply onPrims_map_prop; tea. cbn; intuition eauto.
  Qed.

  Lemma finst_subst pb n s k t u : RF pb n t u -> RF pb n (subst s k t) (subst s k u).
  Proof. intros h. rewrite !subst_inst. now apply finst_inst. Qed.

  Lemma finst_lift pb n m k t u : RF pb n t u -> RF pb n (lift m k t) (lift m k u).
  Proof. intros h. rewrite !lift_rename (rename_inst _ t) (rename_inst _ u). now apply finst_inst. Qed.

End Inst.

(** ** Transporting joins along a term map *)

Section Map.

  (** Source environment [Σ], target [Σ'] (they differ only for universe instances). *)
  Context {cf : checker_flags} (Σ Σ' : global_env_ext) (wfΣ : ClosedBodies Σ) (r : finst_construct_rule).

  Local Notation RF Σ pb n := (eq_term_upto_univ_eta_napp r Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).
  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation BE' Γ := (clos_refl_trans (be_step Σ' Γ)).

  Lemma RE_map_BE Γ Γ' (f : term -> term) :
    is_closed_context Γ ->
    (forall x y, is_open_term Γ x -> red1 Σ Γ x y -> red Σ' Γ' (f x) (f y)) ->
    (forall x y, eta1 x y -> eta1 (f x) (f y)) ->
    (forall x y, canon x = canon y -> canon (f x) = canon (f y)) ->
    forall a b, is_open_term Γ a -> clos_refl_trans (RE Γ) a b -> BE' Γ' (f a) (f b).
  Proof.
    intros hΓ hr he hc a b ha h. apply clos_rt_rt1n_iff in h.
    induction h as [a|a a1 b s _ IH]; [apply rt_refl|].
    eapply rt_trans; [|apply IH; exact (step_open Σ wfΣ Γ a a1 hΓ ha s)].
    destruct s as [[b0 [hr0 ->]]|he0].
    - eapply rt_trans; [exact (BE_red Σ' Γ' _ _ (hr a b0 ha hr0))|].
      apply rt_step; right. apply hc. symmetry. apply canon_idem.
    - apply rt_step; left; right. exact (he _ _ he0).
  Qed.

  Lemma JoinE_map Γ Γ' (f : term -> term) pb t u :
    is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
    (forall x y, is_open_term Γ x -> red1 Σ Γ x y -> red Σ' Γ' (f x) (f y)) ->
    (forall x y, eta1 x y -> eta1 (f x) (f y)) ->
    (forall x y, canon x = canon y -> canon (f x) = canon (f y)) ->
    (forall x y, RF Σ pb 0 x y -> RF Σ' pb 0 (canon (f x)) (canon (f y))) ->
    JoinE r Σ Γ pb t u -> JoinE r Σ' Γ' pb (f t) (f u).
  Proof.
    intros hΓ ht hu hr he hc hrf (v & v' & hv & hv' & e).
    apply (BE_JoinE Σ' r Γ' pb (f t) (f u) (f v) (f v')).
    - eapply rt_trans; [apply rt_step; right; apply hc; symmetry; apply canon_idem|].
      exact (RE_map_BE Γ Γ' f hΓ hr he hc _ _ (canon_is_open_term Γ t ht) hv).
    - eapply rt_trans; [apply rt_step; right; apply hc; symmetry; apply canon_idem|].
      exact (RE_map_BE Γ Γ' f hΓ hr he hc _ _ (canon_is_open_term Γ u hu) hv').
    - exact (hrf v v' e).
  Qed.

End Map.

(** ** Substitution and weakening for [ws_cumul_pbE] *)

Section A7.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ} {r : finst_construct_rule}.

  Local Notation WS pb Γ := (ws_cumul_pbE r pb Σ Γ).

  Lemma untyped_substitution_ws_cumul_pbE {pb Γ Δ Γ'' s M N} :
    untyped_subslet Γ s Δ -> forallb (is_open_term Γ) s ->
    WS pb (Γ ,,, Δ ,,, Γ'') M N ->
    WS pb (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
  Proof.
    intros hs hs' [hΓ hM hN j].
    have hlen := untyped_subslet_length hs.
    constructor.
    - eapply is_closed_subst_context; tea.
    - eapply is_open_term_subst; tea.
    - eapply is_open_term_subst; tea.
    - eapply (JoinE_map Σ Σ wfΣ r (Γ ,,, Δ ,,, Γ'') _ (subst s #|Γ''|)); try eassumption.
      + intros x y hx h.
        have hcr : Σ ;;; Γ ,,, Δ ,,, Γ'' ⊢ x ⇝ y.
        { split; [exact hΓ|exact hx|apply red1_red; exact h]. }
        exact (clrel_rel (untyped_closed_red_subst_cb hs hs' hcr)).
      + intros x y h. exact (eta1_subst_step s x y h _).
      + intros x y e. rewrite !canon_subst. now rewrite e.
      + intros x y e. rewrite !canon_subst. apply finst_subst. exact (RF_canon Σ r _ _ _ _ e).
  Qed.

  Lemma substitution_ws_cumul_pbE {pb Γ Δ Γ'' s M N} :
    subslet Σ Γ s Δ -> forallb (is_open_term Γ) s ->
    WS pb (Γ ,,, Δ ,,, Γ'') M N ->
    WS pb (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
  Proof. intros hs. apply untyped_substitution_ws_cumul_pbE. exact (subslet_untyped_subslet _ _ _ _ hs). Qed.

  (** One assumption, any open term: no typing premise. *)
  Lemma substitution0_ws_cumul_pbE {pb Γ na T t M N} :
    is_open_term Γ t -> WS pb (Γ ,, vass na T) M N -> WS pb Γ (M {0 := t}) (N {0 := t}).
  Proof.
    intros ht h.
    have hs : untyped_subslet Γ [t] [vass na T] by repeat constructor.
    have := @untyped_substitution_ws_cumul_pbE pb Γ [vass na T] [] [t] M N hs.
    cbn. rewrite ht. intros H. exact (H eq_refl h).
  Qed.

  Lemma substitution0_ws_cumul_pbE_vdef {pb Γ na b T M N} :
    is_open_term Γ b -> WS pb (Γ ,, vdef na b T) M N -> WS pb Γ (M {0 := b}) (N {0 := b}).
  Proof.
    intros hb h.
    have hs : untyped_subslet Γ [subst0 [] b] [vdef na b T] by repeat constructor.
    rewrite subst_empty in hs.
    have := @untyped_substitution_ws_cumul_pbE pb Γ [vdef na b T] [] [b] M N hs.
    cbn. rewrite hb. intros H. exact (H eq_refl h).
  Qed.

  Lemma weakening_ws_cumul_pbE {pb Γ Γ' Γ'' M N} :
    WS pb (Γ ,,, Γ') M N -> is_closed_context (Γ ,,, Γ'') ->
    WS pb (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
  Proof.
    intros [hΓ hM hN j] hΓ''. constructor.
    - eapply is_closed_context_lift; tea.
    - eapply is_open_term_lift; tea.
    - eapply is_open_term_lift; tea.
    - eapply (JoinE_map Σ Σ wfΣ r (Γ ,,, Γ') _ (lift #|Γ''| #|Γ'|)); try eassumption.
      + intros x y hx h.
        have hcr : Σ ;;; Γ ,,, Γ' ⊢ x ⇝ y.
        { split; [exact hΓ|exact hx|apply red1_red; exact h]. }
        exact (clrel_rel (weakening_closed_red_cb hcr hΓ'')).
      + intros x y h. exact (eta1_lift _ x y h _).
      + intros x y e. rewrite !canon_lift. now rewrite e.
      + intros x y e. rewrite !canon_lift. apply finst_lift. exact (RF_canon Σ r _ _ _ _ e).
  Qed.

  (** ** A5's tracked gap: the let-body at [pb] *)

  Lemma ws_cumul_pbE_LetIn_bo_pb {pb Γ na t A u u'} :
    WS pb (Γ ,, vdef na t A) u u' -> WS pb Γ (tLetIn na t A u) (tLetIn na t A u').
  Proof.
    intros h. destruct (closed_snoc_vdef_inv Γ na t A (wsE_ctx h)) as [hΓ ht hA].
    have hl : is_open_term Γ (tLetIn na t A u).
    { cbn [on_free_vars]. now rewrite ht hA (open_snoc_inv Γ _ u (wsE_left h)). }
    have hr : is_open_term Γ (tLetIn na t A u').
    { cbn [on_free_vars]. now rewrite ht hA (open_snoc_inv Γ _ u' (wsE_right h)). }
    eapply red_ws_cumul_pbE_left.
    { split; [exact hΓ|exact hl|apply red1_red; apply red_zeta]. }
    eapply red_ws_cumul_pbE_right.
    { split; [exact hΓ|exact hr|apply red1_red; apply red_zeta]. }
    exact (substitution0_ws_cumul_pbE_vdef ht h).
  Qed.

  Lemma ws_cumul_pbE_LetIn_pb {pb Γ na na' t t' A A' u u'} :
    eq_binder_annot na na' -> WS Conv Γ t t' -> WS Conv Γ A A' -> WS pb (Γ ,, vdef na t A) u u' ->
    WS pb Γ (tLetIn na t A u) (tLetIn na' t' A' u').
  Proof.
    intros hna ht hA hu.
    transitivity (tLetIn na t A u').
    - exact (ws_cumul_pbE_LetIn_bo_pb hu).
    - apply ws_cumul_pbE_LetIn; [exact hna|exact ht|exact hA|].
      apply ws_cumul_pbE_refl; [exact (wsE_ctx hu)|exact (wsE_right hu)].
  Qed.

  Lemma ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb {pb Δ Γ B B'} :
    WS pb (Δ ,,, Γ) B B' -> WS pb Δ (it_mkProd_or_LetIn Γ B) (it_mkProd_or_LetIn Γ B').
  Proof.
    induction Γ as [|[na [b|] A] Γ IH] in B, B' |- *; cbn; intros h; [exact h| |].
    - apply IH. exact (ws_cumul_pbE_LetIn_bo_pb h).
    - apply IH. exact (ws_cumul_pbE_Prod_r h).
  Qed.

End A7.

(** ** Universe instances *)

Lemma subst_instance_eta_redex u na A t :
  subst_instance u (eta_redex na A t) = eta_redex na (subst_instance u A) (subst_instance u t).
Proof. rewrite -subst_instance_lift. reflexivity. Qed.

Lemma eta1_subst_instance u t t' : eta1 t t' -> eta1 (subst_instance u t) (subst_instance u t').
Proof.
  intros H. revert t t' H.
  apply (eta1_ind_all (fun t t' => eta1 (subst_instance u t) (subst_instance u t'))); intros.
  1: rewrite subst_instance_eta_redex; apply eta_red.
  all: cbn.
  - apply abs_eta_l; auto.
  - apply abs_eta_r; auto.
  - apply letin_eta_def; auto.
  - apply letin_eta_ty; auto.
  - apply letin_eta_body; auto.
  - eapply case_eta_param. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy).
  - eapply case_eta_return. cbn. auto.
  - apply case_eta_discr; auto.
  - eapply case_eta_brs. induction X; cbn.
    + constructor. destruct p0 as [[He HP] Heq]. split; cbn; [exact HP|exact Heq].
    + now constructor.
  - apply proj_eta; auto.
  - apply app_eta_l; auto.
  - apply app_eta_r; auto.
  - apply prod_eta_l; auto.
  - apply prod_eta_r; auto.
  - eapply evar_eta. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy).
  - eapply fix_eta_ty. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * exact HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - eapply fix_eta_body. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * exact HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - eapply cofix_eta_ty. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * exact HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - eapply cofix_eta_body. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * exact HP.
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - eapply array_eta_val. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy).
  - eapply array_eta_def; cbn; auto.
  - eapply array_eta_type; cbn; auto.
Qed.

Lemma cmp_opt_variance_impl (cu cu' : conv_pb -> Universe.t -> Universe.t -> Prop) pb v :
  (forall pb, RelationClasses.subrelation (cu pb) (cu' pb)) ->
  forall i i', cmp_opt_variance cu pb v i i' -> cmp_opt_variance cu' pb v i i'.
Proof.
  intros h i i'. destruct v as [| |v]; cbn; auto.
  - apply cmp_universe_instance_impl'. apply h.
  - intros [H|H]; [left|right].
    + eapply cmp_universe_instance_impl'; [apply h|exact H].
    + eapply Forall3_impl; [exact H|]. intros x y z. apply cmp_universe_variance_impl; apply h.
Qed.

(** The F-inst instance comparison under a universe instance (base
    [precompose_subst_instance_global], one direction, at F-inst's mode). *)
Lemma precompose_subst_instance_finst r Σ cmp_universe pb gr napp u i i' :
  cmp_global_instance_eta r Σ (fun pb => precompose (cmp_universe pb) (subst_instance_universe u)) pb gr napp i i' ->
  cmp_global_instance_eta r Σ cmp_universe pb gr napp (subst_instance u i) (subst_instance u i').
Proof.
  unfold cmp_global_instance_eta, cmp_opt_variance.
  destruct (global_variance_eta r Σ gr napp) as [| |v].
  - apply precompose_subst_instance__2.
  - unfold subst_instance. cbn. now rewrite !length_map.
  - intros [H|H]; [left|right].
    + now apply precompose_subst_instance__2.
    + unfold subst_instance, cmp_universe_instance_variance in *. cbn.
      rewrite -(map_id v); apply Forall3_map.
      apply Forall3_impl with (1 := H); clear v i i' H; intros v ??.
      destruct v => //=; unfold on_rel in *.
      all: rewrite !subst_instance_universe_make //.
Qed.

Section UnivInst.

  Context {cf : checker_flags} (r : finst_construct_rule) (Σ : global_env) (φ φ' : ConstraintSet.t)
          (i : Instance.t) (HH : valid_constraints φ' (subst_instance_cstrs i φ)).
  Local Notation RF φ pb n := (eq_term_upto_univ_eta_napp r Σ (compare_universe φ) (compare_sort φ) pb n).

  Lemma univinst_hu pb : RelationClasses.subrelation (compare_universe φ pb)
                           (precompose (compare_universe φ' pb) (subst_instance i)).
  Proof. exact (compare_universe_subst_instance pb φ φ' i HH). Qed.

  Lemma univinst_hs pb : RelationClasses.subrelation (compare_sort φ pb)
                           (precompose (compare_sort φ' pb) (subst_instance i)).
  Proof. exact (compare_sort_subst_instance pb φ φ' i HH). Qed.

  (** The primitive-array case of [finst_subst_instance]. *)
  Lemma finst_subst_instance_array (a a' : array_model term) :
    (forall pb n u, RF φ pb n (array_default a) u -> RF φ' pb n (subst_instance i (array_default a)) (subst_instance i u)) ->
    (forall pb n u, RF φ pb n (array_type a) u -> RF φ' pb n (subst_instance i (array_type a)) (subst_instance i u)) ->
    All2 (fun x y => RF φ' Conv 0 (subst_instance i x) (subst_instance i y)) (array_value a) (array_value a') ->
    eq_universe φ (Universe.make' (array_level a)) (Universe.make' (array_level a')) ->
    RF φ Conv 0 (array_default a) (array_default a') ->
    RF φ Conv 0 (array_type a) (array_type a') ->
    onPrims (RF φ' Conv 0) (eq_universe φ')
      (primArray; primArrayModel (mapu_array_model (subst_instance_level i) (subst_instance i) a))
      (primArray; primArrayModel (mapu_array_model (subst_instance_level i) (subst_instance i) a')).
  Proof.
    intros hd ht hv el ed et. constructor; cbn.
    - first [ exact (univinst_hu Conv _ _ el)
            | rewrite /= -!subst_instance_universe_make; exact (univinst_hu Conv _ _ el) ].
    - exact (hd _ _ _ ed).
    - exact (ht _ _ _ et).
    - apply All2_map. exact hv.
  Qed.

  Lemma finst_subst_instance pb n t u :
    eq_term_upto_univ_eta_napp r Σ (compare_universe φ) (compare_sort φ) pb n t u ->
    eq_term_upto_univ_eta_napp r Σ (compare_universe φ') (compare_sort φ') pb n
      (subst_instance i t) (subst_instance i u).
  Proof.
    have hu := univinst_hu. have hs := univinst_hs.
    induction t in pb, n, u |- * using term_forall_list_ind;
      intros h; depelim h; cbn; constructor;
      eauto using precompose_subst_instance__2, cmp_universe_instance_impl'.
    all: unfold eq_predicate, eq_branches, eq_branch, eq_mfixpoint in *.
    all: try (apply All2_map; eapply All2_impl'; tea; eapply All_impl; eauto; cbn; intros; rdest; eauto with univ_subst).
    all: try solve [apply hs; assumption].
    all: try solve [eapply precompose_subst_instance__2;
                    eapply cmp_universe_instance_impl'; [apply hu|assumption]].
    all: try solve [eapply precompose_subst_instance_finst; eapply cmp_opt_variance_impl; [|eassumption];
                    intros pb' x y hxy; exact (hu pb' x y hxy)].
    all: try (match goal with o : onPrims _ _ ?p _ |- _ =>
                destruct p as [? []]; depelim o; cbn in *; try now constructor;
                match goal with X : tPrimProp _ _ |- _ => destruct X as (hty & hdef & harr) end;
                constructor; cbn; eauto;
                [rewrite /= -!subst_instance_universe_make; now eapply hu|solve_all] end).
    all: try solve [constructor].
    all: try (eapply finst_subst_instance_array; eassumption).
    all: repeat match goal with e : _ × _ |- _ => destruct e end.
    all: lazymatch goal with
         | |- onPrims _ _ (primArray; _) _ =>
             eapply finst_subst_instance_array; try eassumption;
             first
               [ match goal with av : All2 (fun x y => (_ * _)%type) (array_value ?a) (array_value ?a') |- _ =>
                   eapply All2_impl; [exact av|]; cbn; intros ? ? [IH h]; exact (IH _ _ _ h) end
               | match goal with IHv : All _ (array_value ?a), ev : All2 _ (array_value ?a) (array_value ?a') |- _ =>
                   eapply All2_impl; [exact (All2_All_mix_left IHv ev)|]; cbn;
                   intros ? ? [IH h]; exact (IH _ _ _ h) end ]
         | |- _ => idtac
         end.
    all: repeat split; simpl; eauto; solve_all.
    all: eapply precompose_subst_instance__2; eapply cmp_universe_instance_impl'; [exact (hu Conv)|assumption].
  Qed.

End UnivInst.

Lemma subst_instance_ws_cumul_pbE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}
  {r : finst_construct_rule} univs u {pb Γ A B} :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  ws_cumul_pbE r pb Σ Γ A B ->
  ws_cumul_pbE r pb (Σ.1, univs) (subst_instance u Γ) (subst_instance u A) (subst_instance u B).
Proof.
  intros HH [hΓ hA hB j].
  have hl : #|subst_instance u Γ| = #|Γ| by apply subst_instance_length.
  constructor.
  - rewrite on_free_vars_ctx_subst_instance. exact hΓ.
  - rewrite hl on_free_vars_subst_instance. exact hA.
  - rewrite hl on_free_vars_subst_instance. exact hB.
  - eapply (JoinE_map Σ (Σ.1, univs) wfΣ r Γ (subst_instance u Γ) (subst_instance u)); try eassumption.
    + intros x y hx h. apply rt_step. exact (red1_subst_instance Σ.1 Γ u x y h).
    + intros x y h. exact (eta1_subst_instance u x y h).
    + intros x y e. rewrite !canon_subst_instance. now rewrite e.
    + intros x y e. rewrite !canon_subst_instance.
      eapply (finst_subst_instance r Σ.1 Σ (global_ext_constraints (Σ.1, univs)) u HH).
      exact (RF_canon Σ r _ _ _ _ e).
Qed.
