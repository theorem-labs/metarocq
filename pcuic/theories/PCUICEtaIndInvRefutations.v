(* Distributed under the terms of the MIT license. *)

(** * C2: two clauses of base's inductive-spine inversions are false over η

  Base inverts a conversion with an inductive spine on one side in
  [ws_cumul_pb_Ind_l_inv] ([PCUICConversion.v:1360]), [ws_cumul_pb_Ind_r_inv]
  ([:1410]), [ws_cumul_pb_Ind_inv] ([:1436]) and [invert_cumul_ind_ind] ([:1774]).
  Two of their clauses are false over [ws_cumul_pbE]. As in
  [PCUICEtaA6Refutations], each theorem takes the false form as a hypothesis and
  derives [False]. The witnesses are well typed in [typingE], in an environment
  proved [wf_ext] and [wf_extE] ([iu_witness_typed]). The main theorems put the
  typing of both related terms, at one common type, among the premises of the
  refuted form, so the forms are false even for well-typed terms; the
  [*_base_false] corollaries refute the untyped base statements, with
  [ws_cumul_pbE] and [ws_cumul_pbE_terms] in place of base's relations.

  - **The universe clause** [cumul_Ind_univ Σ pb ind #|l| u u'].
    The environment [iu_env] declares
    [Polymorphic Cumulative Inductive I@{i} (A : Set) : Set := .] with
    [ind_variance = Some [Irrelevant]], and two global levels [a] and [b] with no
    constraint between them. [tInd I [a]] and [tInd I [b]] both have type
    [Set → Set] ([iu_Ind_typedE]). They are related at every [pb]
    ([iu_univ_premise]): below its arity an inductive head is compared at the
    variance of its full arity ([cmp_global_instance_finst]), here [Irrelevant].
    The η specification relates them too ([iu_univ_spec], through I5); as a chain,
    [tInd I [a] =η λx:Set. I@{a} x =E λx:Set. I@{b} x =η tInd I [b]], where the
    middle step compares the inductive at its full arity. Base's [cumul_Ind_univ]
    at [#|l| = 0] is [AllEqual]
    ([PCUICEquality.v:51-56]), i.e. [a = b], which the valuation [a ↦ 1, b ↦ 2]
    falsifies ([iu_not_cumul_Ind_univ]).
    Refuted: [Ind_inv_univE_false], [Ind_l_inv_univE_false], [Ind_r_inv_univE_false].
  - **The reduct clause** [Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind ui') l'].
    [T := λx:Set. I@{a} x] ([ir_T]) has type [Set → Set] ([ir_T_typedE]) and is
    related to [tInd I [a]] in both directions by one η step on [canon T]
    ([ir_premise_l], [ir_premise_r]). [T] is [red1]-normal: its domain is a sort
    and its body an inductive applied to a variable ([ir_T_normal]). So [T]
    reduces only to itself, a λ, never to an inductive spine.
    Refuted: [Ind_l_inv_reductE_false], [Ind_r_inv_reductE_false].

  **Classification: completeness gaps of base's inversions under η, not
  soundness.** η adds conversions, so inverting a conversion yields fewer
  conclusions; base's inversions read off conclusions that only the η-free
  relation supports. The E relation that relates [I@{a}] and [I@{b}] at
  [Irrelevant] variance is correct and matches the kernel: Rocq's
  [convert_inductives_gen] ([kernel/conversion.ml]) raises [MustExpand] for an
  under-applied cumulative inductive with distinct instances, and its caller
  η-expands both heads and compares them at the full arity. It is not a soundness
  widening.

  **The honest E twins are landed** in [PCUICEtaA6Ind]: [ws_cumul_pbE_Ind_l_inv]
  ([:275]) and [ws_cumul_pbE_Ind_r_inv] ([:294]) conclude that the canonical form
  [canon T] reaches the spine by [(R_c ∪ eta1)*], and compare the instances by
  [cmp_global_instance_finst]; [ws_cumul_pbE_Ind_inv] ([:313]) and
  [invert_cumul_ind_indE] ([:336]) do the same for two spines. Copy 18
  ([PCUICInductiveInversion]) rebuilds its uses of the base clauses through the
  new congruence [ws_cumul_pbE_Ind_finst] of ArityLane, not through these forms.

  Before this file the tree stated the universe-clause failure only in prose (the
  header of [PCUICEtaA6Ind]). Assumptions of every theorem here: Rocq's primitive
  integers, floats and strings and their specification axioms ([Uint63Axioms],
  [FloatAxioms], [PrimStringAxioms]) only; no functional extensionality. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICArityRed PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICWellScopedCumulativity PCUICUnivSubst PCUICWfUniverses
     PCUICEtaDefs PCUICEtaCanon PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICClosedBodies PCUICClosedTyp.

(** ** Spine shapes *)

Lemma red_normal_Ind (Σ : global_env) Γ ind u v : red1 Σ Γ (tInd ind u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma mkApps_Ind_eq_Ind ind ind' u u' l :
  mkApps (tInd ind u) l = tInd ind' u' -> u = u' /\ l = [].
Proof.
  destruct l as [|a l] using rev_ind; cbn.
  - intros e. injection e. intros; subst. split; reflexivity.
  - rewrite mkApps_app. cbn. discriminate.
Qed.

Lemma mkApps_Ind_not_Lambda ind u l na A b : mkApps (tInd ind u) l = tLambda na A b -> False.
Proof.
  destruct l as [|a l] using rev_ind; cbn; [discriminate|].
  rewrite mkApps_app. cbn. discriminate.
Qed.

Section Witnesses.

  #[local] Existing Instance default_checker_flags.

  (** ** The environment *)

  Definition iu_kn : kername := (MPfile ["EtaIndInv"], "I").
  Definition iu_ind : inductive := {| inductive_mind := iu_kn; inductive_ind := 0 |}.
  Definition iu_na : aname := mkBindAnn nAnon Relevant.
  Definition iu_Set : term := tSort Sort.type0.
  Definition iu_arity : term := tProd iu_na iu_Set iu_Set.

  (** Two global levels, with no constraint between them. *)
  Definition iu_a : Level.t := Level.level "a".
  Definition iu_b : Level.t := Level.level "b".
  Definition iu_univs : ContextSet.t :=
    (LevelSet.add iu_a (LevelSet.singleton iu_b), ConstraintSet.empty).

  (** [I@{i}]: one universe, no constraint. *)
  Definition iu_udecl : universes_decl := Polymorphic_ctx ([nNamed "i"], ConstraintSet.empty).

  Definition iu_idecl : one_inductive_body :=
    {| ind_name := "I"; ind_indices := []; ind_sort := Sort.type0; ind_type := iu_arity;
       ind_kelim := IntoAny; ind_ctors := []; ind_projs := []; ind_relevance := Relevant |}.

  Definition iu_mdecl : mutual_inductive_body :=
    {| ind_finite := Finite; ind_npars := 1; ind_params := [vass iu_na iu_Set];
       ind_bodies := [iu_idecl]; ind_universes := iu_udecl;
       ind_variance := Some [Variance.Irrelevant] |}.

  Definition iu_env : global_env :=
    {| universes := iu_univs; declarations := [(iu_kn, InductiveDecl iu_mdecl)];
       retroknowledge := Retroknowledge.empty |}.

  Definition iu_Σ : global_env_ext := (iu_env, Monomorphic_ctx).

  (** The environment the declaration is checked in. *)
  Definition iu_Σ0 : global_env_ext := (mk_global_env iu_univs [] Retroknowledge.empty, iu_udecl).

  (** [a ↦ 1], [b ↦ 2]. *)
  Definition iu_val : valuation :=
    {| valuation_mono := fun s => if bytestring.String.eqb s "b" then 2%positive else 1%positive;
       valuation_poly := fun _ => 0 |}.

  Lemma iu_for_all (f : Level.t -> bool) (s : LevelSet.t) :
    LevelSet.for_all f s = true -> LevelSet.For_all (fun l => f l = true) s.
  Proof.
    intros h. apply LevelSet.for_all_spec; first [exact h | intros x y e; hnf in e; subst; reflexivity].
  Qed.

  (** ** Typing in [iu_Σ0] *)

  Lemma iu_vass0 (Γ : context) (na : aname) A s :
    iu_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing iu_Σ0 Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma iu_vass_s0 (Γ : context) (na : aname) A s :
    iu_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing iu_Σ0 Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma iu_Set_typed0 (Γ : context) :
    wf_local iu_Σ0 Γ -> iu_Σ0 ;;; Γ |- iu_Set : tSort (Sort.super Sort.type0).
  Proof. intros h. apply type_Sort; [exact h|apply wf_sort_type0]. Qed.

  Lemma iu_wf_x0 (Γ : context) : wf_local iu_Σ0 Γ -> wf_local iu_Σ0 (Γ ,, vass iu_na iu_Set).
  Proof.
    intros h. apply localenv_cons_abs; [exact h|].
    exact (iu_vass0 _ iu_na _ _ (iu_Set_typed0 Γ h) eq_refl).
  Qed.

  (** [Π A : Set. Set] is a type, in any well-formed context. *)
  Lemma iu_arity_typed0 (Γ : context) : wf_local iu_Σ0 Γ ->
    iu_Σ0 ;;; Γ |- iu_arity : tSort (Sort.sort_of_product (Sort.super Sort.type0) (Sort.super Sort.type0)).
  Proof.
    intros h. unfold iu_arity. apply type_Prod.
    - exact (iu_vass_s0 _ iu_na _ _ (iu_Set_typed0 Γ h) eq_refl).
    - exact (iu_Set_typed0 _ (iu_wf_x0 Γ h)).
  Qed.

  (** ** The declaration is well-formed *)

  Lemma iu_on_ind_body : on_ind_body cumulSpec0 (lift_typing typing) iu_Σ0 iu_kn iu_mdecl 0 iu_idecl.
  Proof.
    unshelve econstructor.
    - exact [].
    - exists iu_Set. split; [reflexivity|]. apply arity_red_sort. apply whd_stop. reflexivity.
    - exact (iu_vass0 _ (mkBindAnn nAnon rel_of_Type) _ _ (iu_arity_typed0 [] localenv_nil) eq_refl).
    - exact (iu_vass0 _ (mkBindAnn nAnon rel_of_Type) _ _ (iu_arity_typed0 [] localenv_nil) eq_refl).
    - constructor.
    - exact I.
    - split; [constructor|exact I].
    - reflexivity.
    - (* [ind_respects_variance] over the empty index context *)
      cbn. constructor.
  Qed.

  Lemma iu_on_inductive : on_inductive cumulSpec0 (lift_typing typing) iu_Σ0 iu_kn iu_mdecl.
  Proof.
    constructor.
    - constructor; [exact iu_on_ind_body|constructor].
    - exact (iu_wf_x0 [] localenv_nil).
    - reflexivity.
    - (* [on_variance]: the two copies [i'], [i] of the universe are each a
         consistent instance of [I@{i}] in the doubled context *)
      cbn. do 3 eexists. split; [reflexivity| | |reflexivity].
      all: split; [vm_compute; reflexivity|split; [reflexivity|]].
      all: intros v _ c hc; exfalso; eapply ConstraintSet.empty_spec; exact hc.
  Qed.

  Lemma iu_on_udecl : on_udecl iu_univs iu_udecl.
  Proof.
    have hfresh : LevelSet.for_all (fun l => negb (LevelSet.mem l (global_levels iu_univs)))
                    (levels_of_udecl iu_udecl) = true.
    { vm_compute. reflexivity. }
    split; [|split; [|split]].
    - intros l hl hin.
      have h := iu_for_all _ _ hfresh l hl. cbv beta in h.
      have hin' : LevelSet.mem l (global_levels iu_univs) = true := proj2 (LevelSet.mem_spec _ _) hin.
      rewrite hin' in h. cbn in h. discriminate h.
    - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    - exists iu_val. intros x Hx. exfalso.
      apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
    - intros v hv. exists v. split.
      + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
      + intros x Hx. reflexivity.
  Qed.

  Lemma iu_on_udecl_mono : on_udecl iu_univs Monomorphic_ctx.
  Proof.
    split; [|split; [|split]].
    - intros x Hx. exfalso. eapply LevelSet.empty_spec. exact Hx.
    - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    - exists iu_val. intros x Hx. exfalso.
      apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
    - intros v hv. exists v. split.
      + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
      + intros x Hx. reflexivity.
  Qed.

  Lemma iu_wf : wf iu_env.
  Proof.
    split.
    - split; [|split].
      + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
      + have h : LevelSet.for_all (fun l => negb (Level.is_var l)) (global_levels iu_univs) = true.
        { vm_compute. reflexivity. }
        intros l hl. exact (iu_for_all _ _ h l hl).
      + exists iu_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    - (* trunk's wf: the retroknowledge conjunct, then the declarations *)
      split.
      { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                          |intros i h; discriminate h]. }
      apply globenv_decl; [constructor|].
      constructor.
      + constructor.
      + exact iu_on_udecl.
      + exact iu_on_inductive.
      + (* on_prim_decl: no boolean type is registered *)
        cbn. intros i h; discriminate h.
  Qed.

  Lemma iu_wf_ext : wf_ext iu_Σ.
  Proof. split; [exact iu_wf|exact iu_on_udecl_mono]. Qed.

  Lemma iu_wf_extE : wf_extE iu_Σ.
  Proof. exact (wf_ext_incl_E iu_wf_ext). Qed.

  Lemma iu_declared : declared_inductive iu_Σ iu_ind iu_mdecl iu_idecl.
  Proof. split; [left; reflexivity|reflexivity]. Qed.

  (** ** Typing in [iu_Σ] over [typingE] *)

  Lemma iu_consistent l : l = iu_a \/ l = iu_b -> consistent_instance_ext iu_Σ iu_udecl [l].
  Proof.
    intros hl. split; [|split; [reflexivity|]].
    - destruct hl as [->| ->]; vm_compute; reflexivity.
    - intros v _ c hc. exfalso. eapply ConstraintSet.empty_spec. exact hc.
  Qed.

  Lemma iu_arity_closedu : closedu 0 iu_arity.
  Proof. vm_compute. reflexivity. Qed.

  Lemma iu_Set_typedE (Γ : context) :
    wf_localE iu_Σ Γ -> iu_Σ ;;; Γ |-E iu_Set : tSort (Sort.super Sort.type0).
  Proof. intros h. apply typeE_Sort; [exact h|apply wf_sort_type0]. Qed.

  Lemma iu_vassE (Γ : context) : wf_localE iu_Σ Γ -> lift_typing typingE iu_Σ Γ (j_vass iu_na iu_Set).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super Sort.type0).
    split; [exact (iu_Set_typedE Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma iu_wf_xE : wf_localE iu_Σ ([] ,, vass iu_na iu_Set).
  Proof. apply localenv_cons_abs; [constructor|exact (iu_vassE [] localenv_nil)]. Qed.

  Lemma iu_arity_typedE (Γ : context) : wf_localE iu_Σ Γ ->
    iu_Σ ;;; Γ |-E iu_arity : tSort (Sort.sort_of_product (Sort.super Sort.type0) (Sort.super Sort.type0)).
  Proof.
    intros h. unfold iu_arity. apply typeE_Prod.
    - split; [exact tt|]. exists (Sort.super Sort.type0).
      split; [exact (iu_Set_typedE Γ h)|]. split; reflexivity.
    - apply iu_Set_typedE. apply localenv_cons_abs; [exact h|exact (iu_vassE Γ h)].
  Qed.

  (** [I@{a}] and [I@{b}] have type [Set → Set], by [typeE_Ind]. *)
  Lemma iu_Ind_typedE (Γ : context) l : wf_localE iu_Σ Γ -> l = iu_a \/ l = iu_b ->
    iu_Σ ;;; Γ |-E tInd iu_ind [l] : iu_arity.
  Proof.
    intros hΓ hl.
    have h := typeE_Ind _ _ iu_ind [l] iu_mdecl iu_idecl hΓ iu_declared (iu_consistent l hl).
    rewrite (PCUICUnivSubst.closedu_subst_instance [l] (ind_type iu_idecl) iu_arity_closedu) in h.
    exact h.
  Qed.

  Definition iu_a_typed : iu_Σ ;;; [] |-E tInd iu_ind [iu_a] : iu_arity :=
    iu_Ind_typedE [] iu_a localenv_nil (or_introl eq_refl).
  Definition iu_b_typed : iu_Σ ;;; [] |-E tInd iu_ind [iu_b] : iu_arity :=
    iu_Ind_typedE [] iu_b localenv_nil (or_intror eq_refl).

  (** The reduct-clause witness [λx:Set. I@{a} x]. *)
  Definition ir_T : term := tLambda iu_na iu_Set (tApp (tInd iu_ind [iu_a]) (tRel 0)).

  Lemma ir_T_typedE : iu_Σ ;;; [] |-E ir_T : iu_arity.
  Proof.
    have hΓ := iu_wf_xE.
    unfold ir_T, iu_arity. apply typeE_Lambda; [exact (iu_vassE [] localenv_nil)|].
    refine (typeE_App _ _ (tInd iu_ind [iu_a]) iu_na iu_Set iu_Set
              (Sort.sort_of_product (Sort.super Sort.type0) (Sort.super Sort.type0)) (tRel 0) _ _ _).
    - exact (iu_arity_typedE _ hΓ).
    - exact (iu_Ind_typedE _ iu_a hΓ (or_introl eq_refl)).
    - exact (typeE_Rel _ _ 0 (vass iu_na iu_Set) hΓ eq_refl).
  Qed.

  (** The environment is well formed, for the base and for the η typing, and the
      three witnesses have type [Set → Set] over [typingE]. *)
  Lemma iu_witness_typed :
    [× wf_ext iu_Σ, wf_extE iu_Σ,
       iu_Σ ;;; [] |-E tInd iu_ind [iu_a] : iu_arity,
       iu_Σ ;;; [] |-E tInd iu_ind [iu_b] : iu_arity &
       iu_Σ ;;; [] |-E ir_T : iu_arity].
  Proof.
    split; [exact iu_wf_ext|exact iu_wf_extE|exact iu_a_typed|exact iu_b_typed|exact ir_T_typedE].
  Qed.

  (** ** The universe clause *)

  (** Below the arity, F-inst reads the variance of the full arity, [Irrelevant]. *)
  Lemma iu_finst pb :
    cmp_global_instance_finst iu_Σ.1 (compare_universe iu_Σ) pb (IndRef iu_ind) 0 [iu_a] [iu_b].
  Proof.
    change (cmp_opt_variance (compare_universe iu_Σ) Conv (Variance [Variance.Irrelevant]) [iu_a] [iu_b]).
    right. constructor; [exact I|constructor].
  Qed.

  Lemma iu_univ_premise pb : ws_cumul_pbE pb iu_Σ [] (tInd iu_ind [iu_a]) (tInd iu_ind [iu_b]).
  Proof.
    constructor; try reflexivity.
    exists (tInd iu_ind [iu_a]), (tInd iu_ind [iu_b]). split; [|split].
    - apply rt_refl.
    - apply rt_refl.
    - apply eqη_Ind. exact (iu_finst pb).
  Qed.

  (** The η specification relates the pair too, by I5. *)
  Lemma iu_univ_spec pb : iu_Σ ;;; [] ⊢ tInd iu_ind [iu_a] ≤sE[pb] tInd iu_ind [iu_b].
  Proof.
    exact (ws_cumul_pbE_forget_spec (Σ := iu_Σ) (wfΣ := @wf_ClosedBodies _ iu_env iu_wf)
             (iu_univ_premise pb)).
  Qed.

  Lemma iu_sat : satisfies iu_val (global_ext_constraints iu_Σ).
  Proof.
    intros c hc. exfalso. unfold global_ext_constraints in hc.
    apply ConstraintSet.union_spec in hc as [hc|hc]; eapply ConstraintSet.empty_spec; exact hc.
  Qed.

  (** Base's [cumul_Ind_univ] below the arity is [AllEqual], so [a = b]. *)
  Lemma iu_not_cumul_Ind_univ pb : cumul_Ind_univ iu_Σ pb iu_ind 0 [iu_a] [iu_b] -> False.
  Proof.
    intros h.
    change (cmp_universe_instance (compare_universe iu_Σ Conv) [iu_a] [iu_b]) in h.
    inversion h as [|x y l l' hxy hl]; subst.
    have e : val iu_val (Universe.make' iu_a) = val iu_val (Universe.make' iu_b) := hxy iu_val iu_sat.
    vm_compute in e. discriminate e.
  Qed.

  (** ** The reduct clause *)

  Lemma ir_premise_l pb : ws_cumul_pbE pb iu_Σ [] (tInd iu_ind [iu_a]) ir_T.
  Proof.
    constructor; try reflexivity.
    exists (tInd iu_ind [iu_a]), (tInd iu_ind [iu_a]). split; [|split].
    - apply rt_refl.
    - apply rt_step; right. cbn. exact (eta_red canon_la (tInd iu_ind [iu_a]) canon_dom).
    - apply compare_term_eta_refl.
  Qed.

  Lemma ir_premise_r pb : ws_cumul_pbE pb iu_Σ [] ir_T (tInd iu_ind [iu_a]).
  Proof.
    constructor; try reflexivity.
    exists (tInd iu_ind [iu_a]), (tInd iu_ind [iu_a]). split; [|split].
    - apply rt_step; right. cbn. exact (eta_red canon_la (tInd iu_ind [iu_a]) canon_dom).
    - apply rt_refl.
    - apply compare_term_eta_refl.
  Qed.

  (** The invariant: [ir_T] has no [red1] step, in any [Σ]. *)
  Lemma ir_body_normal (Σ : global_env) v :
    red1 Σ ([] ,, vass iu_na iu_Set) (tApp (tInd iu_ind [iu_a]) (tRel 0)) v -> False.
  Proof.
    intros H. inv_red H.
    - eapply red_normal_Ind; eassumption.
    - eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma ir_T_normal (Σ : global_env) v : red1 Σ [] ir_T v -> False.
  Proof.
    unfold ir_T. revert v.
    apply red_normal_lam; [intros w; apply red_normal_Sort|intros w; apply ir_body_normal].
  Qed.

End Witnesses.

(** ** The universe clause, refuted *)

(** Both sides inductive spines. Base: [ws_cumul_pb_Ind_inv] ([PCUICConversion.v:1436])
    and [invert_cumul_ind_ind] ([:1774]). Landed honest E forms:
    [ws_cumul_pbE_Ind_inv] and [invert_cumul_ind_indE] ([PCUICEtaA6Ind.v:313,336]),
    with [cmp_global_instance_finst]. *)
Theorem Ind_inv_univE_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext), wf_ext Σ -> wf_extE Σ ->
   forall Γ ind ind' u u' args args' A,
     Σ ;;; Γ |-E mkApps (tInd ind u) args : A ->
     Σ ;;; Γ |-E mkApps (tInd ind' u') args' : A ->
     ws_cumul_pbE pb Σ Γ (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
     cumul_Ind_univ Σ pb ind #|args| u u') -> False.
Proof.
  intros H. apply (iu_not_cumul_Ind_univ pb).
  exact (H default_checker_flags iu_Σ iu_wf_ext iu_wf_extE [] iu_ind iu_ind [iu_a] [iu_b] [] [] iu_arity
           iu_a_typed iu_b_typed (iu_univ_premise pb)).
Qed.

(** Inductive spine on the left. Base: [ws_cumul_pb_Ind_l_inv]
    ([PCUICConversion.v:1360]). Landed honest E form: [ws_cumul_pbE_Ind_l_inv]
    ([PCUICEtaA6Ind.v:275]). *)
Theorem Ind_l_inv_univE_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext), wf_ext Σ -> wf_extE Σ ->
   forall Γ ind ui l T A,
     Σ ;;; Γ |-E mkApps (tInd ind ui) l : A -> Σ ;;; Γ |-E T : A ->
     ws_cumul_pbE pb Σ Γ (mkApps (tInd ind ui) l) T ->
     ∑ ui' l', red Σ Γ T (mkApps (tInd ind ui') l') × cumul_Ind_univ Σ pb ind #|l| ui ui') -> False.
Proof.
  intros H.
  destruct (H default_checker_flags iu_Σ iu_wf_ext iu_wf_extE [] iu_ind [iu_a] [] (tInd iu_ind [iu_b])
              iu_arity iu_a_typed iu_b_typed (iu_univ_premise pb)) as (ui' & l' & r & hu).
  have e := rt_from_normal _ _ _ (red_normal_Ind iu_Σ [] iu_ind [iu_b]) r.
  destruct (mkApps_Ind_eq_Ind _ _ _ _ _ e) as [-> _].
  exact (iu_not_cumul_Ind_univ pb hu).
Qed.

(** Inductive spine on the right. Base: [ws_cumul_pb_Ind_r_inv]
    ([PCUICConversion.v:1410]). Landed honest E form: [ws_cumul_pbE_Ind_r_inv]
    ([PCUICEtaA6Ind.v:294]). *)
Theorem Ind_r_inv_univE_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext), wf_ext Σ -> wf_extE Σ ->
   forall Γ ind ui l T A,
     Σ ;;; Γ |-E T : A -> Σ ;;; Γ |-E mkApps (tInd ind ui) l : A ->
     ws_cumul_pbE pb Σ Γ T (mkApps (tInd ind ui) l) ->
     ∑ ui' l', red Σ Γ T (mkApps (tInd ind ui') l') × cumul_Ind_univ Σ pb ind #|l| ui' ui) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags iu_Σ iu_wf_ext iu_wf_extE [] iu_ind [iu_b] [] (tInd iu_ind [iu_a])
              iu_arity iu_a_typed iu_b_typed (iu_univ_premise pb)) as (ui' & l' & r & hu).
  have e := rt_from_normal _ _ _ (red_normal_Ind iu_Σ [] iu_ind [iu_a]) r.
  destruct (mkApps_Ind_eq_Ind _ _ _ _ _ e) as [-> _].
  exact (iu_not_cumul_Ind_univ pb hu).
Qed.

(** ** The reduct clause, refuted

    Even the weaker conclusion "[T] reduces to SOME inductive spine" is false. *)

(** Base: [ws_cumul_pb_Ind_l_inv] ([PCUICConversion.v:1360]). Landed honest E form:
    [ws_cumul_pbE_Ind_l_inv] ([PCUICEtaA6Ind.v:275]), where [canon T] reaches the
    spine by [(R_c ∪ eta1)*]. *)
Theorem Ind_l_inv_reductE_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext), wf_ext Σ -> wf_extE Σ ->
   forall Γ ind ui l T A,
     Σ ;;; Γ |-E mkApps (tInd ind ui) l : A -> Σ ;;; Γ |-E T : A ->
     ws_cumul_pbE pb Σ Γ (mkApps (tInd ind ui) l) T ->
     ∑ ind' ui' l', red Σ Γ T (mkApps (tInd ind' ui') l')) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags iu_Σ iu_wf_ext iu_wf_extE [] iu_ind [iu_a] [] ir_T iu_arity
              iu_a_typed ir_T_typedE (ir_premise_l pb)) as (ind' & ui' & l' & r).
  have e := rt_from_normal _ _ _ (ir_T_normal iu_Σ) r.
  exact (mkApps_Ind_not_Lambda _ _ _ _ _ _ e).
Qed.

(** Base: [ws_cumul_pb_Ind_r_inv] ([PCUICConversion.v:1410]). Landed honest E form:
    [ws_cumul_pbE_Ind_r_inv] ([PCUICEtaA6Ind.v:294]). *)
Theorem Ind_r_inv_reductE_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext), wf_ext Σ -> wf_extE Σ ->
   forall Γ ind ui l T A,
     Σ ;;; Γ |-E T : A -> Σ ;;; Γ |-E mkApps (tInd ind ui) l : A ->
     ws_cumul_pbE pb Σ Γ T (mkApps (tInd ind ui) l) ->
     ∑ ind' ui' l', red Σ Γ T (mkApps (tInd ind' ui') l')) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags iu_Σ iu_wf_ext iu_wf_extE [] iu_ind [iu_a] [] ir_T iu_arity
              ir_T_typedE iu_a_typed (ir_premise_r pb)) as (ind' & ui' & l' & r).
  have e := rt_from_normal _ _ _ (ir_T_normal iu_Σ) r.
  exact (mkApps_Ind_not_Lambda _ _ _ _ _ _ e).
Qed.

(** ** The untyped base statements over [ws_cumul_pbE] *)

(** [invert_cumul_ind_ind] ([PCUICConversion.v:1774]) over [ws_cumul_pbE]; honest
    form [invert_cumul_ind_indE] ([PCUICEtaA6Ind.v:336]). *)
Corollary invert_cumul_ind_indE_base_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) Γ ind ind' u u' args args',
     ws_cumul_pbE Cumul Σ Γ (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
     (eqb ind ind' * cumul_Ind_univ Σ Cumul ind #|args| u u' * ws_cumul_pbE_terms Σ Γ args args')%type)
  -> False.
Proof.
  intros H. apply (Ind_inv_univE_false Cumul).
  intros cf Σ wfΣ _ Γ ind ind' u u' args args' A _ _ h.
  exact (snd (fst (H cf Σ (wf_ext_wf Σ wfΣ) Γ ind ind' u u' args args' h))).
Qed.

(** [ws_cumul_pb_Ind_inv] ([PCUICConversion.v:1436]); honest form
    [ws_cumul_pbE_Ind_inv] ([PCUICEtaA6Ind.v:313]). *)
Corollary ws_cumul_pbE_Ind_inv_base_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) Γ ind ind' ui ui' l l',
     ws_cumul_pbE pb Σ Γ (mkApps (tInd ind ui) l) (mkApps (tInd ind' ui') l') ->
     [× ind = ind', cumul_Ind_univ Σ pb ind #|l| ui ui', is_closed_context Γ &
        ws_cumul_pbE_terms Σ Γ l l']) -> False.
Proof.
  intros H. apply (Ind_inv_univE_false pb).
  intros cf Σ wfΣ _ Γ ind ind' u u' args args' A _ _ h.
  destruct (H cf Σ (wf_ext_wf Σ wfΣ) Γ ind ind' u u' args args' h) as [_ hu _ _].
  exact hu.
Qed.

(** [ws_cumul_pb_Ind_l_inv] ([PCUICConversion.v:1360]); honest form
    [ws_cumul_pbE_Ind_l_inv] ([PCUICEtaA6Ind.v:275]). Both of its first two
    clauses fail; this derives [False] from the reduct clause. *)
Corollary ws_cumul_pbE_Ind_l_inv_base_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) Γ ind ui l T,
     ws_cumul_pbE pb Σ Γ (mkApps (tInd ind ui) l) T ->
     ∑ ui' l', [× Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind ui') l', cumul_Ind_univ Σ pb ind #|l| ui ui' &
       All2 (ws_cumul_pbE Conv Σ Γ) l l']) -> False.
Proof.
  intros H. apply (Ind_l_inv_reductE_false pb).
  intros cf Σ wfΣ _ Γ ind ui l T A _ _ h.
  destruct (H cf Σ (wf_ext_wf Σ wfΣ) Γ ind ui l T h) as (ui' & l' & [r _ _]).
  exists ind, ui', l'. exact (clrel_rel r).
Qed.

(** [ws_cumul_pb_Ind_r_inv] ([PCUICConversion.v:1410]); honest form
    [ws_cumul_pbE_Ind_r_inv] ([PCUICEtaA6Ind.v:294]). *)
Corollary ws_cumul_pbE_Ind_r_inv_base_false pb :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) Γ ind ui l T,
     ws_cumul_pbE pb Σ Γ T (mkApps (tInd ind ui) l) ->
     ∑ ui' l', [× Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind ui') l', cumul_Ind_univ Σ pb ind #|l| ui' ui &
       ws_cumul_pbE_terms Σ Γ l' l]) -> False.
Proof.
  intros H. apply (Ind_r_inv_reductE_false pb).
  intros cf Σ wfΣ _ Γ ind ui l T A _ _ h.
  destruct (H cf Σ (wf_ext_wf Σ wfΣ) Γ ind ui l T h) as (ui' & l' & [r _ _]).
  exists ind, ui', l'. exact (clrel_rel r).
Qed.
