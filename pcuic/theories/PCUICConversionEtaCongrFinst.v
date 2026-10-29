(* Distributed under the terms of the MIT license. *)

(** * The inductive-spine congruence of [ws_cumul_pbE] at the F-inst instance comparison

  [ws_cumul_pbE_Ind_finst]: two inductive spines are related at [pb] when their
  instances are related by
  [cmp_global_instance_finst Σ (compare_universe Σ) pb (IndRef ind) #|l|] and their
  arguments are convertible. It is the congruence counterpart of the inversion
  [ws_cumul_pbE_Ind_inv] ([PCUICEtaA6Ind]), which concludes the same instance clause.
  [ws_cumul_pbE_Ind] ([PCUICConversionEtaCongr]) takes base's [cumul_Ind_univ] instead,
  which below the inductive's arity falls back to [AllEqual]; every base instance
  relation gives the F-inst one ([cumul_ind_finst]), so this lemma covers it.

  The proof builds the join directly: the arguments join pairwise
  ([All2_JoinE_ex]), and the final comparison [eq_term_upto_univ_eta_napp] relates the
  heads by [eqη_Ind] at [napp = #|l|], which is the premise.

  **The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed environment
  ([wf_ClosedBodies]); the scoping premise by any closed context; the arguments by
  reflexivity. The instance below ([ws_cumul_pbE_Ind_finst_inst]) relates an
  UNDER-applied inductive [I@{u} (A : Prop) : Prop] with variance [Irrelevant] at two
  different bound levels, in an environment proved [wf] ([if_wf]). There base's
  comparison at [napp = 0] is [AllEqual] and fails ([if_cumul_Ind_univ_fails]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICEtaDefs PCUICEtaCanon PCUICEtaFInst PCUICEtaI5 PCUICEtaI5A2 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr
     PCUICTypingEta PCUICClosedBodies PCUICClosedTyp PCUICArityRed.

Section IndFinst.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Lemma ws_cumul_pbE_Ind_finst {pb Γ ind u u' l l'} :
    cmp_global_instance_finst Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| u u' ->
    is_closed_context Γ -> ws_cumul_pbE_terms Σ Γ l l' ->
    ws_cumul_pbE pb Σ Γ (mkApps (tInd ind u) l) (mkApps (tInd ind u') l').
  Proof.
    intros hu hΓ h. constructor; [exact hΓ| | |].
    - rewrite on_free_vars_mkApps /=. exact (WT_open_left h).
    - rewrite on_free_vars_mkApps /=. exact (WT_open_right h).
    - destruct (All2_JoinE_ex Σ Γ l l' (WT_join h)) as (lx & ly & hlx & hly & hxy).
      apply (BE_JoinE Σ Γ pb _ _ (mkApps (tInd ind u) lx) (mkApps (tInd ind u') ly)).
      + exact (BE_mkApps_args Σ Γ _ _ _ hlx).
      + exact (BE_mkApps_args Σ Γ _ _ _ hly).
      + rewrite !canon_mkApps. cbn [canon]. apply RF_mkApps; [|apply All2_map; exact hxy].
        rewrite Nat.add_0_l length_map. constructor.
        rewrite -(All2_length hlx). exact hu.
  Qed.

End IndFinst.

(** ** A satisfying instance: an under-applied inductive with an irrelevant level *)

Section Instance.

#[local] Existing Instance default_checker_flags.

(** [Inductive I@{u} (A : Prop) : Prop :=.] with variance [Irrelevant] for [u]. *)
Definition if_kn : kername := (MPfile ["IndFinst"], "I").
Definition if_ind : inductive := {| inductive_mind := if_kn; inductive_ind := 0 |}.
Definition if_na : aname := mkBindAnn nAnon Relevant.
Definition if_P : term := tSort sProp.
Definition if_params : context := [vass if_na if_P].
Definition if_arity : term := tProd if_na if_P (tSort sProp).
Definition if_univs : universes_decl := Polymorphic_ctx ([nAnon], ConstraintSet.empty).

Definition if_idecl : one_inductive_body :=
  {| ind_name := "I"; ind_indices := []; ind_sort := sProp; ind_type := if_arity;
     ind_kelim := IntoAny; ind_ctors := []; ind_projs := []; ind_relevance := Relevant |}.

Definition if_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 1; ind_params := if_params; ind_bodies := [if_idecl];
     ind_universes := if_univs; ind_variance := Some [Variance.Irrelevant] |}.

Definition if_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(if_kn, InductiveDecl if_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

(** The declaration is checked in the empty environment, at its own universes. *)
Definition if_Σ0 : global_env_ext :=
  (mk_global_env ContextSet.empty [] Retroknowledge.empty, if_univs).

Definition if_val : valuation := {| valuation_mono := fun _ => 1%positive; valuation_poly := fun n => n |}.

Lemma if_vass (Γ : context) (na : aname) A s :
  if_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typing if_Σ0 Γ (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma if_vass_s (Γ : context) (na : aname) A s :
  if_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typing if_Σ0 Γ (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma if_P_typed (Γ : context) : wf_local if_Σ0 Γ -> if_Σ0 ;;; Γ |- if_P : tSort (Sort.super sProp).
Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

Lemma if_wf_P (Γ : context) : wf_local if_Σ0 Γ -> wf_local if_Σ0 (Γ ,, vass if_na if_P).
Proof.
  intros h. apply localenv_cons_abs; [exact h|].
  exact (if_vass _ if_na _ _ (if_P_typed Γ h) eq_refl).
Qed.

Lemma if_arity_typed :
  if_Σ0 ;;; [] |- if_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  apply type_Prod.
  - exact (if_vass_s _ if_na _ _ (if_P_typed [] localenv_nil) eq_refl).
  - apply type_Sort; [exact (if_wf_P [] localenv_nil)|cbn; trivial].
Qed.

Lemma if_on_ind_body :
  on_ind_body cumulSpec0 (lift_typing typing) if_Σ0 if_kn if_mdecl 0 if_idecl.
Proof.
  unshelve econstructor.
  - exact [].
  - exists (tSort sProp). split; [reflexivity|].
    apply arity_red_sort. apply whd_stop. reflexivity.
  - exact (if_vass _ (mkBindAnn nAnon rel_of_Type) _ _ if_arity_typed eq_refl).
  - exact (if_vass _ (mkBindAnn nAnon rel_of_Type) _ _ if_arity_typed eq_refl).
  - constructor.
  - exact I.
  - reflexivity.
  - reflexivity.
  - cbn. constructor.
Qed.

Lemma if_on_inductive : on_inductive cumulSpec0 (lift_typing typing) if_Σ0 if_kn if_mdecl.
Proof.
  constructor.
  - constructor; [exact if_on_ind_body|constructor].
  - exact (if_wf_P [] localenv_nil).
  - reflexivity.
  - cbn. eexists; eexists; eexists. split.
    + reflexivity.
    + split; [reflexivity|split; [reflexivity|]].
      unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
      vm_compute in Hc. inversion Hc.
    + split; [reflexivity|split; [reflexivity|]].
      unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
      vm_compute in Hc. inversion Hc.
    + reflexivity.
Qed.

Lemma if_on_udecl : on_udecl ContextSet.empty if_univs.
Proof.
  split; [|split; [|split]].
  - intros x Hx H. apply LevelSet.union_spec in H as [H|H].
    + eapply LevelSet.empty_spec. exact H.
    + apply LevelSet.singleton_spec in H. hnf in H. subst x.
      apply LevelSet.mem_spec in Hx. vm_compute in Hx. discriminate Hx.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists if_val. intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma if_wf : wf if_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                            (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx].
      * exfalso. eapply LevelSet.empty_spec. exact Hx.
      * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
    + exists if_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact if_on_udecl.
    + exact if_on_inductive.
    + cbn. intros i h; discriminate h.
Qed.

Definition if_wfE : wfE if_env := wf_incl_E if_wf.
Definition if_cb : ClosedBodies if_env := @wf_ClosedBodies _ if_env if_wf.
#[local] Existing Instance if_cb.

(** Two bound levels, unrelated: [I@{l0}] and [I@{l1}] are compared at [napp = 0]. *)
Definition if_Σ : global_env_ext := (if_env, Polymorphic_ctx ([nAnon; nAnon], ConstraintSet.empty)).

(** At [napp = 0] (below the arity [1]) F-inst reads the variance at the full arity,
    [Irrelevant], so any two instances of length one are related. *)
Lemma if_finst pb :
  cmp_global_instance_finst if_Σ.1 (compare_universe if_Σ) pb (IndRef if_ind) 0
    [Level.lvar 0] [Level.lvar 1].
Proof. cbn. right. repeat constructor. Qed.

(** Base's clause at [napp = 0] is [AllEqual], and [l0 = l1] does not hold. *)
Lemma if_cumul_Ind_univ_fails pb :
  cumul_Ind_univ if_Σ pb if_ind 0 [Level.lvar 0] [Level.lvar 1] -> False.
Proof.
  cbn. intros h. inversion h as [|x y l l' hxy _]; subst.
  specialize (hxy if_val). forward hxy.
  { intros c Hc. exfalso. vm_compute in Hc. inversion Hc. }
  vm_compute in hxy. discriminate hxy.
Qed.

(** In the context [x : Prop], [I@{l0} ≤ I@{l1}]: the under-applied spine at two
    different instances. *)
Lemma ws_cumul_pbE_Ind_finst_inst :
  ws_cumul_pbE Cumul if_Σ [vass if_na if_P]
    (mkApps (tInd if_ind [Level.lvar 0]) []) (mkApps (tInd if_ind [Level.lvar 1]) []).
Proof.
  exact (ws_cumul_pbE_Ind_finst (Σ := if_Σ) (Γ := [vass if_na if_P]) (l := []) (l' := [])
           (if_finst Cumul) eq_refl All2_nil).
Qed.

End Instance.
