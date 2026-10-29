(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICGenerationEta],
    [Typing/PCUICUnivSubstitutionTypEta] and [PCUICWfUniversesEta]

  Each lemma of these files that has a premise is applied here to a concrete
  instance with every premise proved. The environments:
  - [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) :
    Prop := c : I A]), with the typed helpers of [PCUICTypingEtaCopies1Instances];
  - [ci_Σu] of [PCUICWsCumulEtaCtxInstances]: [si_env] with two bound levels
    [l0], [l1] and the constraint [l0 = l1] (satisfiable, [ci_Σu_satisfies]);
  - [up_env] (below): one universe-polymorphic axiom [T@{l0} : Type@{l0}];
  - [um_env] (below): one global level [u] and the global constraint [Set ≤ u];
  - [e0_env]: the empty environment, which [up_env] extends.
  Universe instances map the bound levels to [Set], so each instantiation
  changes the term ([Type@{l0}] becomes [Type@{Set}]). The typing spine
  instance compares [I A] with [(λ_:Prop. I _) A], an η-expansion of the head. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICWeakeningEnv
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICWfUniverses PCUICClosedBodies
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances PCUICWsCumulEtaCtxInstances
     PCUICTypingEtaCopies1Instances
     PCUICTypingEtaNotions PCUICGenerationEta PCUICUnivSubstitutionTypEta PCUICWfUniversesEta.

#[local] Existing Instance default_checker_flags.

(** ** The environments *)

(** A universe-polymorphic axiom [T@{l0} : Type@{l0}]. *)
Definition up_kn : kername := (MPfile ["E3C2"], "T").
Definition up_s0 : sort := sType (Universe.make' (Level.lvar 0)).
Definition up_univs : universes_decl := Polymorphic_ctx ([nAnon], ConstraintSet.empty).
Definition up_cb : constant_body :=
  {| cst_type := tSort up_s0; cst_body := None; cst_universes := up_univs; cst_relevance := Relevant |}.
Definition up_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(up_kn, ConstantDecl up_cb)];
     retroknowledge := Retroknowledge.empty |}.
Definition e0_env : global_env := mk_global_env ContextSet.empty [] Retroknowledge.empty.
Definition up_Σ0 : global_env_ext := (e0_env, up_univs).

Lemma up_wf_sort0 : wf_sort up_Σ0 up_s0.
Proof. apply/(wf_sort_reflect up_Σ0). reflexivity. Qed.

Lemma up_on_udecl : on_udecl ContextSet.empty up_univs.
Proof.
  split; [|split; [|split]].
  - intros x Hx H. apply LevelSet.union_spec in H as [H|H].
    + eapply LevelSet.empty_spec. exact H.
    + apply LevelSet.singleton_spec in H. hnf in H. subst x.
      apply LevelSet.mem_spec in Hx. vm_compute in Hx. discriminate Hx.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists si_val. intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma up_on_constant : on_constant_decl (lift_typing typing) up_Σ0 up_cb.
Proof.
  split; [exact tt|]. exists (Sort.super up_s0).
  split; [apply type_Sort; [constructor|exact up_wf_sort0]|]. split; [exact I|reflexivity].
Qed.

Lemma e0_univs : on_global_univs ContextSet.empty.
Proof.
  split; [|split].
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - intros x Hx.
    change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                          (LevelSet.singleton Level.lzero))) in Hx.
    apply LevelSet.union_spec in Hx as [Hx|Hx].
    + exfalso. eapply LevelSet.empty_spec. exact Hx.
    + apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
  - exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
Qed.

Lemma up_wf : wf up_env.
Proof.
  split; [exact e0_univs|].
  split.
  { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                      |intros i h; discriminate h]. }
  apply globenv_decl; [constructor|].
  constructor.
  - constructor.
  - exact up_on_udecl.
  - exact up_on_constant.
  - cbn. intros i h; discriminate h.
Qed.

Definition up_wfE : wfE up_env := wf_incl_E up_wf.

Lemma e0_wf : wf e0_env.
Proof.
  split; [exact e0_univs|].
  split.
  { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                      |intros i h; discriminate h]. }
  constructor.
Qed.

Definition e0_wfE : wfE e0_env := wf_incl_E e0_wf.

Lemma e0_up_extends : extends e0_env up_env.
Proof.
  eapply extends_strictly_on_decls_extends.
  split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
  now exists [(up_kn, ConstantDecl up_cb)].
Qed.

Definition up_Σp : global_env_ext := (up_env, up_univs).
Definition up_Σm : global_env_ext := (up_env, Monomorphic_ctx).

Lemma up_wf_sort_p : wf_sort up_Σp up_s0.
Proof. apply/(wf_sort_reflect up_Σp). reflexivity. Qed.

Lemma up_s0_typed : up_Σp ;;; [] |-E tSort up_s0 : tSort (Sort.super up_s0).
Proof. apply typeE_Sort; [constructor|exact up_wf_sort_p]. Qed.

Lemma up_udecl_prop (Σ : global_env) : on_udecl_prop Σ up_univs.
Proof. intros c hc. exfalso. eapply ConstraintSet.empty_spec. exact hc. Qed.

Lemma up_udecl_prop_mono (Σ : global_env) : on_udecl_prop Σ Monomorphic_ctx.
Proof. intros c hc. exfalso. eapply ConstraintSet.empty_spec. exact hc. Qed.

Definition up_wk : wf_ext_wkE up_Σp := (up_wfE, up_udecl_prop up_env).
Definition up_wk_m : wf_ext_wkE up_Σm := (up_wfE, up_udecl_prop_mono up_env).

(** The instance [Set] for [l0], from [up_univs] into the monomorphic [up_env]. *)
Lemma up_cu : consistent_instance_ext up_Σm up_univs [Level.lzero].
Proof.
  split; [reflexivity|split; [reflexivity|]].
  unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
  vm_compute in Hc. inversion Hc.
Qed.

(** The abstract instance [l0] of [up_univs], inside [up_Σp]. *)
Lemma up_cu_abs : consistent_instance_ext up_Σp up_univs [Level.lvar 0].
Proof.
  split; [reflexivity|split; [reflexivity|]].
  unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
  vm_compute in Hc. inversion Hc.
Qed.

(** [x : Type@{l0}] is well formed in [up_Σp]. *)
Definition up_Γ : context := [vass si_na (tSort up_s0)].

Lemma up_wf_Γ : wf_localE up_Σp up_Γ.
Proof.
  apply localenv_cons_abs; [constructor|].
  split; [exact tt|]. exists (Sort.super up_s0). split; [exact up_s0_typed|]. split; [exact I|reflexivity].
Defined.

Lemma up_x_typed : up_Σp ;;; up_Γ |-E tRel 0 : lift0 1 (tSort up_s0).
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tSort up_s0)) up_wf_Γ eq_refl). Qed.

Lemma up_isTypeRel_s0 : isTypeRelE up_Σp [] (tSort up_s0) Relevant.
Proof. split; [exact tt|]. exists (Sort.super up_s0). split; [exact up_s0_typed|]. split; [exact I|reflexivity]. Qed.

Lemma up_lookup : lookup_env up_env up_kn = Some (ConstantDecl up_cb).
Proof. reflexivity. Qed.

(** A global level [u] and the global constraint [Set ≤ u]. *)
Definition um_l : Level.t := Level.level "u".
Definition um_c : UnivConstraint.t := (Level.lzero, ConstraintType.Le 0%Z, um_l).
Definition um_env : global_env :=
  {| universes := (LevelSet.singleton um_l, ConstraintSet.singleton um_c); declarations := [];
     retroknowledge := Retroknowledge.empty |}.

Lemma um_wf : wf um_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. apply ConstraintSet.singleton_spec in Hx. subst x.
      split; apply LevelSet.mem_spec; reflexivity.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (LevelSet.singleton um_l) (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx]; apply LevelSet.singleton_spec in Hx; hnf in Hx; subst x;
        reflexivity.
    + exists si_val. intros x Hx. apply ConstraintSet.singleton_spec in Hx. subst x.
      constructor. cbn. lia.
  - split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    constructor.
Qed.

Definition um_wfE : wfE um_env := wf_incl_E um_wf.

Lemma um_c_in : ConstraintSet.In um_c (global_constraints um_env).
Proof. apply ConstraintSet.singleton_spec. reflexivity. Qed.

Lemma um_c_in_ext : ConstraintSet.In um_c (global_ext_constraints (um_env, Monomorphic_ctx)).
Proof. apply ConstraintSet.union_spec. right. exact um_c_in. Qed.

Definition um_wk : wf_ext_wkE (um_env, Monomorphic_ctx) := (um_wfE, up_udecl_prop_mono um_env).

(** [ci_Σu] is a [wf_ext_wkE] environment, and [Set, Set] is an instance of its
    universe context in the monomorphic [si_env]. *)
Lemma ci_udecl_prop : on_udecl_prop si_env ci_Σu.2.
Proof.
  intros c hc. apply ConstraintSet.singleton_spec in hc. subst c.
  split; apply LevelSet.mem_spec; reflexivity.
Qed.

Definition ci_wk : wf_ext_wkE ci_Σu := (si_wfE, ci_udecl_prop).

Lemma ci_cu_set : consistent_instance_ext (si_env, Monomorphic_ctx) ci_Σu.2 [Level.lzero; Level.lzero].
Proof.
  split; [reflexivity|split; [reflexivity|]].
  unfold valid_constraints; cbn. intros v _ c Hc.
  apply ConstraintSet.add_spec in Hc as [->|Hc]; [|now apply ConstraintSet.empty_spec in Hc].
  cbn. constructor. reflexivity.
Qed.

(** The swapped instance [l1, l0] of the same context, inside [ci_Σu]. *)
Lemma ci_cu_swap : consistent_instance_ext ci_Σu ci_Σu.2 [Level.lvar 1; Level.lvar 0].
Proof.
  split; [reflexivity|split; [reflexivity|]].
  unfold valid_constraints; cbn. intros v hv c Hc.
  apply ConstraintSet.add_spec in Hc as [->|Hc]; [|now apply ConstraintSet.empty_spec in Hc].
  have hin : ConstraintSet.In ci_cstr (global_ext_constraints ci_Σu).
  { apply ConstraintSet.union_spec. left. apply ConstraintSet.singleton_spec. reflexivity. }
  have hs := hv _ hin. unfold ci_cstr in hs. inversion hs; subst.
  cbn. constructor. cbn in *. now symmetry.
Qed.

(** ** [PCUICGenerationEta] *)

(** The η-expanded head [λ_:Prop. I _] applied to [∀P:Prop. P], and its typing. *)
Definition g_I : term := tInd si_ind [].
Definition g_A : term := ci_False.
Definition g_T : term := tApp (sp_eta g_I) g_A.

Lemma g_eta_I_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E sp_eta g_I : tProd si_na si_P (tSort sProp).
Proof.
  intros h. unfold sp_eta. apply typeE_Lambda.
  - exact (cp_vass Γ si_na si_P _ (cp_P_typed Γ h) eq_refl).
  - exact (cp_Ix_typed _ 0 (cp_wf_P Γ h) (cp_rel_P _ 0 (vass si_na si_P) (cp_wf_P Γ h) eq_refl eq_refl)).
Qed.

Lemma g_T_typed : si_Σ ;;; [] |-E g_T : tSort sProp.
Proof.
  exact (typeE_App _ _ (sp_eta g_I) si_na si_P (tSort sProp) _ g_A
           (cp_arity_typedE [] localenv_nil) (g_eta_I_typed [] localenv_nil) (ci_False_typed [] localenv_nil)).
Qed.

Lemma g_T_isType : isTypeE si_Σ [] g_T.
Proof. split; [exact tt|]. exists sProp. split; [exact g_T_typed|]. split; exact I. Qed.

(** [I A] against [(λ_:Prop. I _) A]: an η-expansion of the head. *)
Lemma g_cumul : cumulSpecE si_Σ [] (tApp g_I g_A) g_T.
Proof.
  apply cumulE_App; [|apply cumulE_Refl].
  apply cumulE_Sym. apply cumulSpecE_eta_contract.
Qed.

Lemma g_cstr_isType : isTypeE si_Σ [] (tProd si_na si_P (cp_Ix 0)).
Proof.
  split; [exact tt|]. eexists. split; [exact (cp_cstr_prod_typed [] localenv_nil)|]. split; exact I.
Qed.

(** The constructor [c : Π A : Prop. I A] applied to [∀P:Prop. P], at the type
    [(λ_:Prop. I _) (∀P:Prop. P)]. *)
Lemma typing_spineE_inst :
  typing_spineE si_Σ [] (tProd si_na si_P (cp_Ix 0)) [g_A] g_T.
Proof.
  eapply type_spine_consE.
  - exact g_cstr_isType.
  - apply cumulE_Refl.
  - exact (ci_False_typed [] localenv_nil).
  - apply type_spine_nilE; [exact g_T_isType|exact g_cumul].
Qed.

Lemma type_mkAppsE_inst : si_Σ ;;; [] |-E mkApps (tConstruct si_ind 0 []) [g_A] : g_T.
Proof. exact (type_mkAppsE si_Σ [] _ [g_A] g_T _ (cp_cstr_typed [] localenv_nil) typing_spineE_inst). Qed.

(** Abstracting [x : Prop] and the definition [y := x : Prop] over [y]. *)
Definition g_Δ : context := [vdef si_na (tRel 0) si_P; vass si_na si_P].

Lemma g_wf_Δ : wf_localE si_Σ g_Δ.
Proof.
  apply localenv_cons_def; [exact cp_wf_Γ1|].
  split; [exact (cp_rel_P cp_Γ1 0 (vass si_na si_P) cp_wf_Γ1 eq_refl eq_refl)|].
  exists (Sort.super sProp). split; [exact (cp_P_typed cp_Γ1 cp_wf_Γ1)|]. split; reflexivity.
Qed.

Lemma type_it_mkLambda_or_LetInE_inst :
  si_Σ ;;; [] |-E it_mkLambda_or_LetIn g_Δ (tRel 0) : it_mkProd_or_LetIn g_Δ (lift0 1 si_P).
Proof.
  apply (type_it_mkLambda_or_LetInE si_Σ [] g_Δ).
  exact (typeE_Rel _ _ 0 (vdef si_na (tRel 0) si_P) g_wf_Δ eq_refl).
Qed.

(** ** [Typing/PCUICUnivSubstitutionTypEta]: the environment lemmas *)

Definition not_var_global_levelsE_inst := not_var_global_levelsE um_wfE.
Definition wf_ext_wkE_wf_inst := wf_ext_wkE_wf up_Σp up_wk.
Definition not_var_global_ext_levelsE_inst := not_var_global_ext_levelsE um_env um_wk.
Definition levels_global_constraintE_inst := levels_global_constraintE um_env um_wfE um_c um_c_in.
Definition levels_global_ext_constraintE_inst :=
  levels_global_ext_constraintE um_env Monomorphic_ctx um_wk um_c um_c_in_ext.
Definition monomorphic_global_constraintE_inst := monomorphic_global_constraintE um_env um_wfE um_c um_c_in.
Definition monomorphic_global_constraint_extE_inst :=
  monomorphic_global_constraint_extE um_env um_wk um_c um_c_in_ext.

Lemma ci_valid_swap :
  valid_constraints0 (global_ext_constraints ci_Σu)
    (subst_instance_cstrs [Level.lvar 1; Level.lvar 0] (ConstraintSet.singleton ci_cstr)).
Proof. exact (proj2 (proj2 ci_cu_swap)). Qed.

Lemma ci_valid_set :
  valid_constraints0 (global_ext_constraints (si_env, Monomorphic_ctx))
    (subst_instance_cstrs [Level.lzero; Level.lzero] (ConstraintSet.singleton ci_cstr)).
Proof. exact (proj2 (proj2 ci_cu_set)). Qed.

Definition consistent_ext_trans_polymorphic_case_auxE_inst :=
  @consistent_ext_trans_polymorphic_case_auxE _ si_env [nAnon; nAnon] (ConstraintSet.singleton ci_cstr)
    Monomorphic_ctx (ConstraintSet.singleton ci_cstr) [Level.lvar 1; Level.lvar 0] [Level.lzero; Level.lzero]
    ci_wk ci_valid_swap ci_valid_set.

Definition consistent_ext_trans_polymorphic_casesE_inst :=
  consistent_ext_trans_polymorphic_casesE si_env ci_Σu.2 Monomorphic_ctx ([nAnon; nAnon], ConstraintSet.singleton ci_cstr)
    [Level.lvar 1; Level.lvar 0] [Level.lzero; Level.lzero] ci_wk ci_cu_swap ci_cu_set.

Definition consistent_ext_transE_inst :=
  consistent_ext_transE si_env ci_Σu.2 Monomorphic_ctx ci_Σu.2
    [Level.lvar 1; Level.lvar 0] [Level.lzero; Level.lzero] ci_wk ci_cu_swap ci_cu_set.

Definition consistent_instance_valid_constraintsE_inst :=
  consistent_instance_valid_constraintsE si_env ci_Σu.2 [Level.lzero; Level.lzero] Monomorphic_ctx ci_wk ci_cu_set.

(** The context [x : Type@{l0}] of [up_Σp], instantiated at [Set]. *)
Lemma up_Γ_over :
  All_local_env_over (typingE up_Σp)
    (fun Γ0 (_ : wf_localE up_Σp Γ0) t T (_ : up_Σp;;; Γ0 |-E t : T) =>
       forall u univs, wf_ext_wkE up_Σp ->
         consistent_instance_ext (up_Σp.1, univs) up_Σp.2 u ->
         (up_Σp.1, univs) ;;; subst_instance u Γ0 |-E subst_instance u t : subst_instance u T)
    up_Γ up_wf_Γ.
Proof.
  unfold up_wf_Γ. constructor; [constructor|].
  intros u univs wk cu.
  exact (env_propE_typing typing_subst_instanceE up_Σp up_wfE [] _ _ up_s0_typed u univs wk cu).
Qed.

Definition All_local_env_over_subst_instanceE_inst :=
  All_local_env_over_subst_instanceE up_Σp up_Γ up_wf_Γ up_Γ_over [Level.lzero] Monomorphic_ctx up_wk up_cu.

Lemma up_l0_in : LevelSet.In (Level.lvar 0) (global_ext_levels up_Σp).
Proof. apply LevelSet.mem_spec. reflexivity. Qed.

Definition in_var_global_extE_inst := in_var_global_extE 0 up_Σp up_wfE up_l0_in.

Lemma up_wf_universe_l0 : wf_universe up_Σp (Universe.make' (Level.lvar 0)).
Proof. exact up_wf_sort_p. Qed.

Definition wf_universe_subst_instanceE_inst :=
  wf_universe_subst_instanceE up_Σp Monomorphic_ctx [Level.lzero] _ up_wfE up_wf_universe_l0 up_cu.
Definition wf_sort_subst_instanceE_inst :=
  wf_sort_subst_instanceE up_Σp Monomorphic_ctx [Level.lzero] up_s0 up_wfE up_wf_sort_p up_cu.

Definition subst_instance_case_branch_typeE_inst :=
  @subst_instance_case_branch_typeE _ si_env si_wfE [Level.lzero] cp_ci si_mdecl si_idecl cp_mp
    (case_predicate_context si_ind si_mdecl si_idecl cp_mp) cp_br 0 si_cdecl.

Lemma si_declared_minductive : declared_minductive si_env si_kn si_mdecl.
Proof. left; reflexivity. Qed.

Definition declared_inductive_wf_ext_wkE_inst :=
  declared_inductive_wf_ext_wkE si_env si_mdecl si_kn si_wfE si_declared_minductive.
Definition declared_inductive_wf_global_extE_inst :=
  declared_inductive_wf_global_extE si_env si_mdecl si_kn si_wfE si_declared_minductive.

Definition consistent_instance_ext_subst_absE_inst :=
  consistent_instance_ext_subst_absE up_Σp up_univs [Level.lvar 0] up_wk up_cu_abs.

Lemma up_l0_expr_in : LevelSet.In (LevelExpr.get_level (Level.lvar 0, 0)) (global_ext_levels up_Σp).
Proof. exact up_l0_in. Qed.

Definition in_global_ext_subst_abs_levelE_inst :=
  in_global_ext_subst_abs_levelE up_Σp (Level.lvar 0, 0) up_wk up_l0_expr_in.
Definition consistent_instance_ext_subst_abs_univE_inst :=
  consistent_instance_ext_subst_abs_univE up_Σp up_s0 up_wk up_wf_sort_p.
Definition consistent_instance_ext_subst_abs_indsE_inst :=
  consistent_instance_ext_subst_abs_indsE up_Σp up_univs si_kn [Level.lvar 0] (ind_bodies si_mdecl)
    up_wk up_cu_abs.

Definition subst_abstract_instance_idE_inst :=
  env_propE_typing subst_abstract_instance_idE up_Σp up_wfE up_Γ _ _ up_x_typed up_wk.
Definition typed_subst_abstract_instanceE_inst :=
  typed_subst_abstract_instanceE up_Σp up_Γ (tRel 0) _ up_wk up_x_typed.

(** ** [Typing/PCUICUnivSubstitutionTypEta]: the copied lemmas *)

Definition ci_sl0 : term := tSort (sType (Universe.make' (Level.lvar 0))).
Definition ci_sl1 : term := tSort (sType (Universe.make' (Level.lvar 1))).

(** [λ_:Prop. Type@{l0} _] against [Type@{l1}]: an η-contraction whose body
    compares the two sorts under [l0 = l1]. *)
Lemma ci_conv_eta_sorts : ci_Σu ;;; [] ⊢ sp_eta ci_sl0 ≤sE[Conv] ci_sl1.
Proof.
  unfold sp_eta. apply cumul_eta_l. apply cumulE_App; [|apply cumulE_Refl].
  apply cumulE_Sort. exact ci_eq_univ.
Qed.

Definition ci_d : context_decl := vass si_na (sp_eta ci_sl0).
Definition ci_d' : context_decl := vass si_na ci_sl1.

Lemma ci_conv_decls : conv_decls cumulSpecE0 ci_Σu [] [] ci_d ci_d'.
Proof. constructor; [reflexivity|exact ci_conv_eta_sorts]. Qed.

Lemma ci_cumul_decls : cumul_decls cumulSpecE0 ci_Σu [] [] ci_d ci_d'.
Proof. constructor; [reflexivity|]. apply (cumulE_Sym _ _ Cumul). apply cumulE_Sym. exact ci_conv_eta_sorts. Qed.

Definition ci_valid := consistent_instance_valid_constraintsE_inst.

Definition conv_decls_subst_instanceE_inst :=
  conv_decls_subst_instanceE ci_Σu [Level.lzero; Level.lzero] Monomorphic_ctx ci_d ci_d' ci_valid ci_conv_decls.
Definition cumul_decls_subst_instanceE_inst :=
  cumul_decls_subst_instanceE ci_Σu [Level.lzero; Level.lzero] Monomorphic_ctx ci_d ci_d' ci_valid ci_cumul_decls.

Lemma ci_conv_ctx : conv_context cumulSpecE0 ci_Σu [ci_d] [ci_d'].
Proof. constructor; [constructor|exact ci_conv_decls]. Qed.

Lemma ci_cumul_ctx : cumul_context cumulSpecE0 ci_Σu [ci_d] [ci_d'].
Proof. constructor; [constructor|exact ci_cumul_decls]. Qed.

Definition conv_ctx_subst_instanceE_inst :=
  conv_ctx_subst_instanceE ci_Σu [Level.lzero; Level.lzero] Monomorphic_ctx ci_valid ci_conv_ctx.
Definition subst_instance_ws_cumul_ctx_pbE_rel_inst :=
  PCUICUnivSubstitutionTypEta.subst_instance_ws_cumul_ctx_pbE_rel ci_Σu [Level.lzero; Level.lzero]
    Monomorphic_ctx ci_valid ci_cumul_ctx.

Definition subst_instance_mfix_on_indE_inst :=
  subst_instance_mfix_on_indE ci_Σu [] [Level.lzero; Level.lzero] Monomorphic_ctx check_one_cofix
    (fun _ => true) cp_block (subst_instance_check_one_cofix _) ci_valid (cp_block_on_ind ci_Σu).

Definition typing_subst_instanceE_inst :=
  env_propE_typing typing_subst_instanceE up_Σp up_wfE up_Γ _ _ up_x_typed [Level.lzero] Monomorphic_ctx
    up_wk up_cu.
Definition typing_subst_instance'E_inst :=
  typing_subst_instance'E up_env Monomorphic_ctx up_Γ (tRel 0) _ [Level.lzero] up_univs up_wk up_x_typed up_cu.
Definition typing_subst_instance_wf_localE_inst :=
  typing_subst_instance_wf_localE up_env Monomorphic_ctx up_Γ [Level.lzero] up_univs up_wk up_wf_Γ up_cu.
Definition typing_subst_instance''E_inst :=
  typing_subst_instance''E up_env Monomorphic_ctx up_Γ (tRel 0) _ [Level.lzero] up_univs up_wk up_x_typed up_cu.
Definition typing_subst_instance_ctxE_inst :=
  typing_subst_instance_ctxE up_Σm up_Γ (tRel 0) _ ([nAnon], ConstraintSet.empty) [Level.lzero]
    up_wfE (up_udecl_prop up_env) up_x_typed up_cu.
Definition typing_subst_instance_declE_inst :=
  typing_subst_instance_declE up_Σm up_Γ (tRel 0) _ up_kn (ConstantDecl up_cb) [Level.lzero]
    up_wfE up_lookup up_x_typed up_cu.

Definition up_wf_extE : wf_extE (up_env, up_univs) := (up_wfE, up_on_udecl).

Definition wf_local_instantiate_polyE_inst :=
  @wf_local_instantiate_polyE _ up_Σm ([nAnon], ConstraintSet.empty) up_Γ [Level.lzero] up_wf_extE up_cu up_wf_Γ.
Definition wf_local_instantiateE_inst :=
  @wf_local_instantiateE _ up_Σm (ConstantDecl up_cb) up_Γ [Level.lzero] up_kn up_wfE up_lookup up_cu up_wf_Γ.

Definition lift_typing_subst_instance_declE_inst :=
  lift_typing_subst_instance_declE up_Σm [] (j_vass si_na (tSort up_s0)) up_kn (ConstantDecl up_cb) [Level.lzero]
    up_wfE up_lookup up_isTypeRel_s0 up_cu.
Definition isType_subst_instance_declE_inst :=
  isType_subst_instance_declE up_Σm [] (tSort up_s0) up_kn (ConstantDecl up_cb) [Level.lzero]
    up_wfE up_lookup up_isTypeRel_s0 up_cu.
Definition isTypeRel_subst_instance_declE_inst :=
  isTypeRel_subst_instance_declE up_Σm [] (tSort up_s0) Relevant up_kn (ConstantDecl up_cb) [Level.lzero]
    up_wfE up_lookup up_isTypeRel_s0 up_cu.

Definition up_global_ext : wf_global_extE up_env up_univs := up_wk.

Definition wf_local_subst_instanceE_inst :=
  wf_local_subst_instanceE up_Σm up_Γ up_univs [Level.lzero] up_global_ext up_cu up_wf_Γ.
Definition wf_local_subst_instance_declE_inst :=
  wf_local_subst_instance_declE up_Σm up_Γ up_kn (ConstantDecl up_cb) [Level.lzero] up_wfE up_lookup up_wf_Γ up_cu.

Definition isTypeRel_subst_instance_idE_inst :=
  isTypeRel_subst_instance_idE up_Σp [] (tSort up_s0) Relevant up_wk up_isTypeRel_s0.
Definition isType_subst_instance_idE_inst :=
  isType_subst_instance_idE up_Σp [] (tSort up_s0) up_wk up_isTypeRel_s0.

Definition subst_instance_ind_sort_idE_inst :=
  subst_instance_ind_sort_idE si_env si_mdecl si_ind si_idecl si_wfE si_declared_inductive.
Definition subst_instance_ind_type_idE_inst :=
  subst_instance_ind_type_idE si_env si_mdecl si_ind si_idecl si_wfE si_declared_inductive.

(** ** [PCUICWfUniversesEta] *)

Lemma up_wf_instance_set : wf_instance up_Σm [Level.lzero].
Proof. constructor; [apply global_ext_levels_InSet|constructor]. Qed.

Definition wf_universe_subst_instance_univE_inst :=
  wf_universe_subst_instance_univE up_Σp Monomorphic_ctx [Level.lzero] _ up_wfE up_wf_universe_l0 up_wf_instance_set.
Definition wf_sort_subst_instance_sortE_inst :=
  wf_sort_subst_instance_sortE up_Σp Monomorphic_ctx [Level.lzero] up_s0 up_wfE up_wf_sort_p up_wf_instance_set.
Definition wf_sort_instantiateE_inst :=
  wf_sort_instantiateE up_env up_univs up_s0 [Level.lzero] Monomorphic_ctx up_wfE up_wf_sort_p up_wf_instance_set.

Lemma um_levels : Forall (wf_level (um_env, Monomorphic_ctx)) [um_l; Level.lzero].
Proof.
  constructor; [|constructor; [apply global_ext_levels_InSet|constructor]].
  apply LevelSet.mem_spec. reflexivity.
Qed.

Definition wf_level_monoE_inst :=
  wf_level_monoE um_env [um_l; Level.lzero] um_wfE (up_udecl_prop_mono um_env) um_levels.

Lemma up_wf_instance_abs : wf_instance up_Σp [Level.lvar 0].
Proof. constructor; [exact up_l0_in|constructor]. Qed.

Definition wf_instance_subst_instanceE_inst :=
  wf_instance_subst_instanceE up_env up_univs [Level.lzero] [Level.lvar 0] Monomorphic_ctx
    up_wfE (up_udecl_prop up_env) up_wf_instance_abs up_wf_instance_set.

Lemma up_wf_universes_s0 : wf_universes up_Σp (tSort up_s0).
Proof. reflexivity. Qed.

Definition wf_universes_instE_inst :=
  @wf_universes_instE _ up_Σm up_univs (tSort up_s0) [Level.lzero] up_wfE (up_udecl_prop up_env)
    up_wf_instance_set up_wf_universes_s0.

(** Weakening from the empty environment to [up_env], at the bound level [l0]. *)
Lemma e0_wf_universe_l0 : wf_universe up_Σ0 (Universe.make' (Level.lvar 0)).
Proof. exact up_wf_sort0. Qed.

Lemma e0_wf_level_l0 : wf_level up_Σ0 (Level.lvar 0).
Proof. apply LevelSet.mem_spec. reflexivity. Qed.

Lemma e0_wf_instance_l0 : wf_instance up_Σ0 [Level.lvar 0].
Proof. constructor; [exact e0_wf_level_l0|constructor]. Qed.

Definition weaken_wf_universeE_inst :=
  weaken_wf_universeE up_Σ0 up_env _ up_wfE e0_up_extends e0_wf_universe_l0.
Definition weaken_wf_levelE_inst :=
  @weaken_wf_levelE _ up_Σ0 up_env _ e0_wfE up_wfE e0_up_extends e0_wf_level_l0.
Definition weaken_wf_instanceE_inst :=
  @weaken_wf_instanceE _ up_Σ0 up_env _ e0_wfE up_wfE e0_up_extends e0_wf_instance_l0.

Lemma e0_wf_universes_s0 : wf_universes up_Σ0 (tSort up_s0).
Proof. reflexivity. Qed.

Definition weaken_wf_universesE_inst :=
  @weaken_wf_universesE _ up_Σ0 up_env _ e0_wfE up_wfE e0_up_extends e0_wf_universes_s0.

Definition up_wf_level_l0 : wf_level up_Σp (Level.lvar 0) := up_l0_in.

Definition wf_level_closedE_inst :=
  @wf_level_closedE _ up_env up_wfE up_univs (Level.lvar 0) (up_udecl_prop up_env) up_wf_level_l0.
Definition wf_universe_closedE_inst :=
  @wf_universe_closedE _ up_env up_wfE up_univs _ (up_udecl_prop up_env) up_wf_universe_l0.
Definition wf_sort_closedE_inst :=
  @wf_sort_closedE _ up_env up_wfE up_univs up_s0 (up_udecl_prop up_env) up_wf_sort_p.
Definition wf_instance_closedE_inst :=
  @wf_instance_closedE _ up_env up_wfE up_univs [Level.lvar 0] (up_udecl_prop up_env) up_wf_instance_abs.
Definition wf_universes_closeduE_inst :=
  @wf_universes_closeduE _ up_env up_wfE up_univs (tSort up_s0) (up_udecl_prop up_env) up_wf_universes_s0.

Lemma up_wf_ctx_universes : wf_ctx_universes up_Σp up_Γ.
Proof. reflexivity. Qed.

Definition wf_ctx_universes_closedE_inst :=
  @wf_ctx_universes_closedE _ up_env up_wfE up_univs up_Γ (up_udecl_prop up_env) up_wf_ctx_universes.

Lemma si_closedu_params : test_context (closedu #|polymorphic_instance (ind_universes si_mdecl)|) (ind_params si_mdecl).
Proof. reflexivity. Qed.

Lemma si_closedu_indices : test_context (closedu #|polymorphic_instance (ind_universes si_mdecl)|) (ind_indices si_idecl).
Proof. reflexivity. Qed.

Definition closed_ind_predicate_contextE_inst :=
  @closed_ind_predicate_contextE _ si_env si_ind si_mdecl si_idecl si_wfE si_declared_inductive
    si_closedu_params si_closedu_indices.
Definition closedu_indsE_inst := @closedu_indsE _ si_env si_kn si_mdecl si_wfE.

(** The judgement [x : Type@{l0} ⊢ x : Type@{l0}] has well-formed universes. *)
Definition wf_typesE_inst := env_propE_typing wf_typesE up_Σp up_wfE up_Γ _ _ up_x_typed.
Definition typing_wf_universesE_inst := @typing_wf_universesE _ up_Σp up_Γ _ _ up_wfE up_x_typed.
Definition typing_wf_sortE_inst := @typing_wf_sortE _ up_Σp [] _ _ up_wfE up_s0_typed.
Definition isType_wf_universesE_inst := @isType_wf_universesE _ up_Σp [] _ up_wfE up_isTypeRel_s0.
