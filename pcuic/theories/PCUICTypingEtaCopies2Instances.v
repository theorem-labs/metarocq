(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICTypingEtaNotions],
    [PCUICGenerationEta], [Typing/PCUICUnivSubstitutionTypEta], [PCUICWfUniversesEta],
    [PCUICSubstitutionEta], [PCUICContextsEta] and [PCUICAritiesEta]

  Each lemma of these files that has a premise is applied here to a concrete
  instance with every premise proved. The environments:
  - [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) :
    Prop := c : I A]), with the typed helpers of [PCUICTypingEtaCopies1Instances];
  - [ci_Σu] of [PCUICWsCumulEtaCtxInstances]: [si_env] with two bound levels
    [l0], [l1] and the constraint [l0 = l1] (satisfiable, [ci_Σu_satisfies]);
  - [up_env] (below): one universe-polymorphic axiom [T@{l0} : Type@{l0}];
  - [um_env] (below): one global level [u] and the global constraint [Set ≤ u];
  - [e0_env]: the empty environment, which [up_env] extends;
  - [rf_Σ] of [PCUICWsCumulEtaCtx] (the empty environment), with the contexts
    [F : Prop → Prop] and [G : (Prop → Prop) → Prop, F : Prop → Prop], in which
    [G (λy:Prop. F y)] and [G F] are related by one η step.
  Universe instances map the bound levels to [Set], so the instantiation changes the
  term ([Type@{l0}] becomes [Type@{Set}]), except in the instances marked NOT BUILT:
  those on the monomorphic inductive [I] (their missing witness, and what it costs, are
  written where they start) and the weakening instances, whose two environments have the
  same level set. The two rows that reached the same weakness through their DATA rather
  than through [I] are built here instead: the branch-type equation takes a predicate
  returning [Type@{l0}] ([c2_mp_u]) and the instantiated block is at that level
  ([c2_block_u]), so instantiating changes both sides of each. The typing spine
  instances compare [I A] with [(λ_:Prop. I _) A], an η-expansion of the head, and
  [G (λy:Prop. F y)] with [G F]. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICWeakeningEnv
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICWfUniverses PCUICClosedBodies
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances PCUICWsCumulEtaCtxInstances
     PCUICTypingEtaCopies1Instances
     PCUICTypingEtaNotions PCUICGenerationEta PCUICUnivSubstitutionTypEta PCUICWfUniversesEta
     PCUICReduction PCUICSigmaCalculus PCUICSubstitution PCUICContexts PCUICArities PCUICEtaDefs
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICEtaA6 PCUICEtaJoinSpec
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICInstDefEta PCUICInstTypEta PCUICEtaC1b
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICEtaI5.
From MetaRocq.PCUIC Require PCUICInstDef.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

(** ** The environments *)

(** A universe-polymorphic axiom [T@{l0} : Type@{l0}]. *)
Definition up_kn : kername := (MPfile ["UPInst"], "T").
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
  PCUICGenerationEta.typing_spineE si_Σ [] (tProd si_na si_P (cp_Ix 0)) [g_A] g_T.
Proof.
  eapply PCUICGenerationEta.type_spine_consE.
  - exact g_cstr_isType.
  - apply cumulE_Refl.
  - exact (ci_False_typed [] localenv_nil).
  - apply PCUICGenerationEta.type_spine_nilE; [exact g_T_isType|exact g_cumul].
Qed.

Lemma type_mkAppsE_inst : si_Σ ;;; [] |-E mkApps (tConstruct si_ind 0 []) [g_A] : g_T.
Proof. exact (PCUICGenerationEta.type_mkAppsE si_Σ [] _ [g_A] g_T _ (cp_cstr_typed [] localenv_nil) typing_spineE_inst). Qed.

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

(** The predicate of [cp_mp] with its return type AT THE BOUND LEVEL [l0]: the instance
    [[Set]] maps [Type@{l0}] to [Type@{Set}], so both sides of the equation differ from
    the terms they are built from. (The inductive [I] and the branch [cp_br] still mention
    no universe; what the equation computes here is the branch type, which carries the
    predicate's return type.) *)
Definition c2_mp_u : predicate term :=
  {| pparams := pparams cp_mp; puinst := puinst cp_mp; pcontext := pcontext cp_mp;
     preturn := tSort up_s0 |}.

(** The instantiation is not the identity on this predicate, machine-checked. *)
Lemma c2_mp_u_moves :
  eqb (subst_instance [Level.lzero] (preturn c2_mp_u)) (preturn c2_mp_u) = false.
Proof. reflexivity. Qed.

Definition subst_instance_case_branch_typeE_inst :=
  @subst_instance_case_branch_typeE _ si_env si_wfE [Level.lzero] cp_ci si_mdecl si_idecl c2_mp_u
    (case_predicate_context si_ind si_mdecl si_idecl c2_mp_u) cp_br 0 si_cdecl.

Lemma si_declared_minductive : declared_minductive si_env si_kn si_mdecl.
Proof. left; reflexivity. Qed.

(** ** NOT BUILT: the instances that need a universe-polymorphic inductive

  Every row below marked [NOT BUILT (polymorphic inductive)] is applied to [I], which is
  monomorphic: its universe context is empty, its abstract instance is the empty one, and
  the only universe instance that can be applied to it maps every part of the declaration
  to itself. Each such row therefore shows its lemma's premises jointly satisfiable, and
  nothing about what the lemma does to a universe.

  The missing witness is one object: a universe-polymorphic inductive declaration with its
  [wf] and [wfE] proofs, after which these rows move to it unchanged. Its cost, measured on
  the monomorphic declaration this file uses: the data and the well-formedness of [I]
  ([si_cdecl] to [si_wf] of [PCUICCumulativitySpecEtaClosureInstances]) are about 155
  lines, which a polymorphic declaration repeats over a polymorphic [global_env_ext]; on
  top of that comes the polymorphic [on_udecl] (the [up_on_udecl] pattern of this file, 14
  lines, where the monomorphic one is [si_on_udecl]). The [on_variance] obligation adds
  nothing: with [ind_variance := None] it is [unit] over a polymorphic context too, and
  [tt] discharges it. The η content of this file does not depend on it: the
  η steps are in the terms, not in the universes. *)
(* NOT BUILT (polymorphic inductive): proves satisfiability only; the inductive [I] is
   monomorphic, so its universe context is empty and [wf_ext_wkE] holds with nothing to
   check. *)
Definition declared_inductive_wf_ext_wkE_inst :=
  declared_inductive_wf_ext_wkE si_env si_mdecl si_kn si_wfE si_declared_minductive.
(* NOT BUILT (polymorphic inductive): proves satisfiability only; the inductive [I] is
   monomorphic, so its universe context is empty and [wf_global_extE] holds with nothing
   to check. *)
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
(** [Type@{l0}] is fixed by the abstract instance [[l0]] of its universe context. *)
Definition typed_subst_abstract_instanceE_inst :=
  typed_subst_abstract_instanceE up_Σp [] (tSort up_s0) _ up_wk up_s0_typed.

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

(** A cofixpoint block AT THE BOUND LEVEL [l0], so that the instantiation changes the
    block and not only the environment: its declared type is
    [∀ _ : Type@{l0}. (λ_:Prop. I _) Prop], and its witness for [check_one_cofix] is
    [∀ _ : Type@{l0}. I Prop], reached by an η-contraction under the product. *)
Definition c2_dtype_u : term := tProd si_na ci_sl0 (tApp (sp_eta (tInd si_ind [])) si_P).
Definition c2_witness_u : term := tProd si_na ci_sl0 (tApp (tInd si_ind []) si_P).
Definition c2_block_u : mfixpoint term :=
  [{| dname := si_na; dtype := c2_dtype_u; dbody := tRel 0; rarg := 0 |}].

(** The instantiation is not the identity on this block, machine-checked. *)
Lemma c2_block_u_moves :
  eqb (subst_instance [Level.lzero; Level.lzero] c2_dtype_u) c2_dtype_u = false.
Proof. reflexivity. Qed.

Lemma c2_block_u_on_ind :
  mfix_on_ind check_one_cofix (conv_witnessE ci_Σu []) (fun _ => true) c2_block_u.
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists c2_witness_u. split; [reflexivity|]. split; [reflexivity|].
  apply cumulE_Prod; [reflexivity|apply cumulE_Refl|].
  apply cumulE_App; [apply cumulSpecE_eta_contract|apply cumulE_Refl].
Qed.

Definition subst_instance_mfix_on_indE_inst :=
  subst_instance_mfix_on_indE ci_Σu [] [Level.lzero; Level.lzero] Monomorphic_ctx check_one_cofix
    (fun _ => true) c2_block_u (subst_instance_check_one_cofix _) ci_valid c2_block_u_on_ind.

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

(* NOT BUILT (polymorphic inductive): proves satisfiability only; [I] is monomorphic, its
   abstract instance is empty, so the identity it states is trivial on [ind_sort]. *)
Definition subst_instance_ind_sort_idE_inst :=
  subst_instance_ind_sort_idE si_env si_mdecl si_ind si_idecl si_wfE si_declared_inductive.
(* NOT BUILT (polymorphic inductive): proves satisfiability only; [I] is monomorphic, its
   abstract instance is empty, so the identity it states is trivial on [ind_type]. *)
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

(* NOT BUILT (an extension that adds a level), the four [weaken_wf_*E_inst] and the two
   [wf_universes_weaken*E_inst]: proves satisfiability only. [up_env] extends [e0_env] by
   a declaration and by NO universe, so [global_ext_levels] is the same set on both sides
   and each conclusion is the premise's own proposition; the weakening is at the bound
   level [l0], which comes from the shared [up_univs]. The missing witness is a pair of
   environments whose GLOBAL level sets differ, with a global level in the smaller one;
   its cost is a second universe environment beside [um_env] with its [wf]/[wfE] proof
   (the [um_wf] pattern, about 25 lines of LevelSet and ConstraintSet computation) and an
   [extends] proof. That upgrade would make each conclusion a statement about a strictly
   larger level set; it would NOT make the conclusion depend on the lemma, because in a
   concrete finite environment every [wf_level], [wf_universe] and [wf_universes]
   conclusion is decided by computation. The weakness of a weakening instance is
   structural here, not a property of this model. *)
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
Definition wf_universes_weakenE_inst :=
  wf_universes_weakenE e0_env up_env up_univs e0_wfE up_wfE e0_up_extends [] (j_vass si_na (tSort up_s0))
    eq_refl.
Definition wf_universes_weaken_fullE_inst :=
  wf_universes_weaken_fullE up_Σ0 up_env e0_wfE up_wfE e0_up_extends [] (tSort up_s0) (tSort (Sort.super up_s0))
    eq_refl.

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

(* NOT BUILT (polymorphic inductive): proves satisfiability only; [I] is monomorphic, so
   the bound [#|abstract_instance| = 0] is reached by a context with no universe at all. *)
Definition closed_ind_predicate_contextE_inst :=
  @closed_ind_predicate_contextE _ si_env si_ind si_mdecl si_idecl si_wfE si_declared_inductive
    si_closedu_params si_closedu_indices.
(* NOT BUILT (polymorphic inductive): proves satisfiability only; [I] is monomorphic, so
   [inds] carries the empty instance and is universe-closed trivially. *)
Definition closedu_indsE_inst := @closedu_indsE _ si_env si_kn si_mdecl si_wfE.

(** The judgement [x : Type@{l0} ⊢ x : Type@{l0}] has well-formed universes. *)
Definition wf_typesE_inst := env_propE_typing wf_typesE up_Σp up_wfE up_Γ _ _ up_x_typed.
Definition typing_wf_universesE_inst := @typing_wf_universesE _ up_Σp up_Γ _ _ up_wfE up_x_typed.
Definition typing_wf_sortE_inst := @typing_wf_sortE _ up_Σp [] _ _ up_wfE up_s0_typed.
Definition isType_wf_universesE_inst := @isType_wf_universesE _ up_Σp [] _ up_wfE up_isTypeRel_s0.

(** ** [PCUICSubstitutionEta]

  In [si_Σ]: the substitution [x := ∀P:Prop. P] for [x : Prop] ([c2_sub]), its
  let form ([c2_subd]) and the context [x : Prop, y : x] ([c2_Γxy]), whose last
  type mentions the substituted variable. The cumulativity instances are in the
  empty environment [rf_Σ] of [PCUICWsCumulEtaCtx]: [G (λy:Prop. F y)] against
  [G F] in [G : (Prop → Prop) → Prop, F : Prop → Prop], a real η step, under the
  substitution [F := λz:Prop. z]. *)

Definition c2_x : context := [vass si_na fi_P].
Lemma c2_False0 : si_Σ ;;; [] |-E ci_False : fi_P.
Proof. exact (ci_False_typed [] localenv_nil). Qed.

Lemma c2_subs : subsE si_Σ [] [ci_False] c2_x.
Proof. econstructor; [constructor|exact c2_False0]. Qed.
Lemma c2_sub : subsletE si_Σ [] [ci_False] c2_x.
Proof. exact (subslet_ass_tipE c2_False0). Qed.
Lemma c2_subd : subsletE si_Σ [] [ci_False] [vdef si_na ci_False fi_P].
Proof. exact (subslet_def_tipE c2_False0). Qed.

Definition c2_Γxy : context := [vass si_na (tRel 0); vass si_na fi_P].
Lemma c2_wf_Γxy : wf_localE si_Σ c2_Γxy.
Proof. apply localenv_cons_abs; [exact ci_wf_Γ1|exact (ci_vass_Prop fi_Γ1 (tRel 0) ci_x_typed)]. Qed.
Lemma c2_y_typed : si_Σ ;;; c2_Γxy |-E tRel 0 : lift0 1 (tRel 0).
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tRel 0)) c2_wf_Γxy eq_refl). Qed.
Lemma c2_wf_xF : wf_localE si_Σ [vass si_na ci_False].
Proof. apply localenv_cons_abs; [constructor|exact (ci_vass_Prop [] ci_False c2_False0)]. Qed.
Lemma c2_wf_d : wf_localE si_Σ [vdef si_na ci_False fi_P].
Proof.
  apply localenv_cons_def; [constructor|].
  split; [exact c2_False0|]. exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|].
  split; reflexivity.
Qed.

Definition subs_lengthE_inst := subs_lengthE c2_subs.
Lemma subslet_defE_inst : subsletE si_Σ [] [ci_False; ci_False] [vdef si_na (tRel 0) fi_P; vass si_na fi_P].
Proof. exact (subslet_defE (na := si_na) (t := tRel 0) (T := fi_P) c2_sub c2_False0 eq_refl). Qed.
Definition subslet_ass_tipE_inst := c2_sub.
Definition subslet_def_tipE_inst := c2_subd.
Definition subslet_nth_errorE_inst := @subslet_nth_errorE _ si_Σ [] _ _ _ 0 subslet_defE_inst eq_refl.
Definition subslet_lengthE_inst := subslet_lengthE subslet_defE_inst.
Definition subst_lengthE_inst := subst_lengthE si_Σ [] [ci_False] c2_x c2_subs.

Lemma c2_subs_x : subsE si_Σ c2_x [tRel 0] c2_x.
Proof. econstructor; [constructor|exact ci_x_typed]. Qed.
Lemma c2_sub_x : subsletE si_Σ c2_x [tRel 0] c2_x.
Proof. exact (subslet_ass_tipE ci_x_typed). Qed.
Definition subs_nth_error_geE_inst :=
  subs_nth_error_geE si_Σ c2_x c2_x [] 1 [tRel 0] c2_subs_x (le_n 1).
Definition subs_nth_error_ltE_inst :=
  subs_nth_error_ltE si_Σ c2_x c2_x [vass si_na (tRel 0)] 0 [tRel 0] c2_subs_x (le_n 1).
Definition subslet_nth_error_ltE_inst :=
  subslet_nth_error_ltE si_Σ c2_x c2_x [vass si_na (tRel 0)] 0 [tRel 0] c2_sub_x (le_n 1).
Definition typed_substE_inst :=
  typed_substE si_Σ [] ci_False fi_P [tRel 5] 0 si_wfE (le_n 0) c2_False0.
Definition subst_wf_localE_inst := subst_wf_localE si_Σ c2_Γxy [tRel 7] 2 si_wfE c2_wf_Γxy.
Lemma up_declared_constant : declared_constant up_env up_kn up_cb.
Proof. left; reflexivity. Qed.
Definition subst_declared_constantE_inst :=
  subst_declared_constantE up_Σm up_kn up_cb [tRel 0] 0 [Level.lzero] up_wfE up_declared_constant.

Lemma si_declared_minductive' : declared_minductive si_env si_kn si_mdecl.
Proof. left; reflexivity. Qed.
Definition wf_arities_context'E_inst :=
  @wf_arities_context'E _ si_Σ si_wfE si_kn si_mdecl (on_declared_minductiveE si_wfE si_declared_minductive').
Definition wf_arities_contextE_inst :=
  @wf_arities_contextE _ si_env si_wfE si_kn si_mdecl si_declared_minductive'.

(** The constructor [c] of [I] is typed in the arities context, so its type is
    closed there and, once [I] is substituted, closed. *)
Lemma on_constructor_closed_aritiesE_inst :
  closedn #|arities_context (ind_bodies si_mdecl)| si_cdecl.(cstr_type).
Proof.
  destruct (on_declared_constructorE (wfΣ := si_wfE) si_declared_constructor) as [[_ _] [cs [_ hc]]].
  exact (on_constructor_closed_aritiesE (Σ := si_env) (wfΣ := si_wfE) (mind := si_ind) hc).
Qed.
Lemma on_constructor_closedE_inst :
  closed (subst0 (inds (inductive_mind si_ind) [] (ind_bodies si_mdecl)) (subst_instance [] si_cdecl.(cstr_type))).
Proof.
  destruct (on_declared_constructorE (wfΣ := si_wfE) si_declared_constructor) as [[_ _] [cs [_ hc]]].
  exact (on_constructor_closedE (Σ := si_env) (wfΣ := si_wfE) (mind := si_ind) (u := []) hc).
Qed.

Definition subslet_untyped_subsletE_inst := subslet_untyped_subsletE si_Σ [] [ci_False] c2_x c2_sub.
Definition subs_nth_errorE_inst :=
  subs_nth_errorE si_Σ [] [ci_False] c2_x (vass si_na fi_P) 0 ci_False c2_subs eq_refl eq_refl.
Definition subs_usubstE_inst := subs_usubstE si_Σ [] c2_x [vass si_na (tRel 0)] [ci_False] c2_subs.

(** The η pair at [Cumul] and [Conv], well typed. *)
Lemma c2_wc_spec pb (Γ : context) : rf_Σ ;;; Γ ⊢ wc_T ≤sE[pb] wc_U.
Proof.
  apply convSpecE_cumulSpecE.
  unfold wc_T, wc_U. apply cumulE_App; [apply cumulE_Refl|].
  unfold wc_eta_F. apply cumul_eta_l. apply cumulE_Refl.
Qed.
Lemma c2_wc_ws pb : ws_cumul_pbE pb rf_Σ wc_Γ wc_T wc_U.
Proof.
  apply (into_ws_cumul_pbE_spec (wfΣ := @wfE_ClosedBodies _ rf_Σ wc_wfE) (c2_wc_spec pb wc_Γ)).
  - exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_wf_Γ).
  - exact (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_T_typed).
  - exact (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_U_typed).
Qed.
Lemma c2_wc_wt pb : wt_cumul_pbE pb rf_Σ wc_Γ wc_T wc_U.
Proof.
  constructor; [exact (wc_isType _ wc_T_typed)|exact (wc_isType _ wc_U_typed)|].
  exact (wsE_join (c2_wc_ws pb)).
Qed.

Definition wt_cumul_cumE_inst : JoinE rf_Σ wc_Γ Cumul wc_T wc_U := wt_cumul_cumE (c2_wc_wt Cumul).
Definition wt_conv_convE_inst : JoinE rf_Σ wc_Γ Conv wc_T wc_U := wt_conv_convE (c2_wc_wt Conv).

Lemma c2_red_id_x : red1 si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. unfold ci_id. apply red_beta. Qed.
Lemma c2_red1P : red1P (shiftnP 1 xpred0) si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. split; [reflexivity|split; [reflexivity|exact c2_red_id_x]]. Qed.
Definition red1P_on_free_vars_rightE_inst :=
  @red1P_on_free_vars_rightE _ _ si_Σ si_wfE _ _ _ c2_red1P.
Definition isType_wf_localE_inst := isType_wf_localE (ci_on_typeE_Prop fi_Γ1 (tRel 0) ci_x_typed).
Definition subsletE_open_terms_inst := @subsletE_open_terms _ si_Σ si_wfE _ _ _ subslet_defE_inst.
Definition isType_closedPTE_inst :=
  @isType_closedPTE _ si_Σ si_wfE fi_Γ1 (tRel 0) (ci_on_typeE_Prop fi_Γ1 (tRel 0) ci_x_typed).

Lemma c2_open_app : is_open_term ([] ,,, c2_x ,,, []) (tApp ci_id (tRel 0)).
Proof. reflexivity. Qed.
Lemma c2_ctx_x : on_ctx_free_vars (shiftnP #|[] ,,, c2_x ,,, []| xpred0) ([] ,,, c2_x ,,, []).
Proof. reflexivity. Qed.
Definition substitution_red1E_inst :=
  @substitution_red1E _ si_Σ si_wfE [] c2_x [] [ci_False] _ _ c2_subs localenv_nil c2_open_app c2_red_id_x.
Definition substitution_let_redE_inst :=
  @substitution_let_redE _ si_Σ si_wfE [] c2_x [] [ci_False] _ _ c2_sub c2_open_app c2_red_id_x.
Definition substitution_untyped_let_redE_inst :=
  @substitution_untyped_let_redE _ si_Σ si_wfE [] c2_x [] [ci_False] _ _ subslet_untyped_subsletE_inst
    c2_open_app c2_red_id_x.
Lemma c2_red_id_x' : red si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. apply red1_red. exact c2_red_id_x. Qed.
Definition substitution_untyped_redE_inst :=
  @substitution_untyped_redE _ si_Σ si_wfE [] c2_x [] [ci_False] _ _ subslet_untyped_subsletE_inst
    c2_open_app c2_ctx_x c2_red_id_x'.
Definition substitution_redE_inst :=
  @substitution_redE _ si_Σ si_wfE [] c2_x [] [ci_False] _ _ c2_sub localenv_nil
    c2_open_app c2_ctx_x c2_red_id_x'.
Lemma c2_red_beta_False : red si_Σ [] (tApp ci_id ci_False) ci_False.
Proof. apply red1_red. unfold ci_id. apply red_beta. Qed.
Lemma c2_untyped_beta : untyped_subslet [] [tApp ci_id ci_False] c2_x.
Proof. constructor. constructor. Qed.
(** [x] under the substitution [x := (λy:Prop. y) (∀P:Prop. P)], reduced in the
    substitution to [x := ∀P:Prop. P]. *)
Definition red_redE_inst :=
  @red_redE _ si_Σ si_wfE (shiftnP 1 xpred0) [] c2_x [] [tApp ci_id ci_False] [ci_False] (tRel 0)
    eq_refl eq_refl (All2_cons c2_red_beta_False All2_nil) ltac:(constructor; [reflexivity|constructor]) c2_untyped_beta.
Definition untyped_substitution_redE_inst :=
  @untyped_substitution_redE _ si_Σ si_wfE [] c2_x [] [ci_False] _ _ subslet_untyped_subsletE_inst
    c2_ctx_x c2_open_app c2_red_id_x'.

(** [F := λz:Prop. z] substituted in the η pair. *)
Definition c2_id : term := tLambda c1b_na (tSort sProp) (tRel 0).
Lemma c2_id_typed : rf_Σ ;;; [] |-E c2_id : rf_F.
Proof.
  unfold c2_id. apply typeE_Lambda; [exact (rf_P_vass [] localenv_nil)|].
  exact (typeE_Rel _ _ 0 (vass c1b_na (tSort sProp)) (localenv_cons_abs localenv_nil (rf_P_vass [] localenv_nil)) eq_refl).
Qed.
Lemma c2_sub_id : subsletE rf_Σ [] [c2_id] [vass c1b_na rf_F].
Proof. exact (subslet_ass_tipE c2_id_typed). Qed.
Lemma c2_wc_ctx : on_ctx_free_vars (shiftnP #|[] ,,, [vass c1b_na rf_F] ,,, [vass c1b_na wc_G_ty]| xpred0)
  ([] ,,, [vass c1b_na rf_F] ,,, [vass c1b_na wc_G_ty]).
Proof. reflexivity. Qed.
Definition substitution_untyped_cumulE_inst :=
  @substitution_untyped_cumulE _ rf_Σ wc_wfE [] [vass c1b_na rf_F] [vass c1b_na wc_G_ty] [c2_id] wc_T wc_U
    (subslet_untyped_subsletE _ _ _ _ c2_sub_id) eq_refl eq_refl c2_wc_ctx (wsE_join (c2_wc_ws Cumul)).
Definition substitution_cumul0E_inst :=
  @substitution_cumul0E _ rf_Σ wc_wfE rf_Γ c1b_na wc_G_ty wc_T wc_U (tRel 0)
    eq_refl eq_refl eq_refl (wsE_join (c2_wc_ws Cumul)).
(** The let [G := λh:Prop → Prop. ∀P:Prop. P] substituted in the η pair. *)
Definition c2_G : term := tLambda c1b_na rf_F (tProd c1b_na (tSort sProp) (tRel 0)).
Lemma c2_wc_let : JoinE rf_Σ (rf_Γ ,, vdef c1b_na c2_G wc_G_ty) Cumul wc_T wc_U.
Proof.
  exact (wsE_join (into_ws_cumul_pbE_spec (wfΣ := @wfE_ClosedBodies _ rf_Σ wc_wfE)
    (Γ := rf_Γ ,, vdef c1b_na c2_G wc_G_ty) (c2_wc_spec Cumul _) eq_refl eq_refl eq_refl)).
Qed.
Definition substitution_cumul_letE_inst :=
  @substitution_cumul_letE _ rf_Σ wc_wfE rf_Γ c1b_na c2_G wc_G_ty wc_T wc_U eq_refl eq_refl eq_refl c2_wc_let.

(** [usubst_well_substE] on [x := ∀P:Prop. P]. *)
Definition c2_σ : nat -> term := fun n => match n with 0 => ci_False | S k => tRel k end.
Lemma c2_usubst : PCUICInstDef.usubst c2_x c2_σ [].
Proof. intros [|x] d h b hb; [cbn in h; noconf h; discriminate hb|destruct x; discriminate h]. Qed.
Lemma c2_usubst_typed : forall x decl, nth_error c2_x x = Some decl ->
  si_Σ ;;; [] |-E c2_σ x : inst (subst_compose (shiftk (S x)) c2_σ) (decl.(decl_type)).
Proof. intros [|x] d h; [cbn in h; noconf h; exact c2_False0|destruct x; discriminate h]. Qed.
Definition usubst_well_substE_inst := @usubst_well_substE _ si_Σ c2_x c2_σ [] c2_usubst c2_usubst_typed.

Definition subslet_well_substE_inst :=
  @subslet_well_substE _ si_Σ si_wfE [] c2_x [ci_False] [vass si_na (tRel 0)] c2_sub c2_wf_xF.

Definition c2_inst_ctx := (type_instE si_Σ si_wfE c2_Γxy _ _ c2_y_typed).2.1.
Definition All_local_env_instE_inst :=
  @All_local_env_instE _ si_Σ si_wfE [] c2_x [vass si_na (tRel 0)] [ci_False] c2_inst_ctx localenv_nil c2_sub.

Definition substitution_propE_inst :=
  env_propE_typing substitution_propE si_Σ si_wfE c2_Γxy _ _ c2_y_typed [] c2_x [vass si_na (tRel 0)]
    [ci_False] c2_sub eq_refl c2_wf_xF.
Definition substitutionE_inst :=
  @substitutionE _ si_Σ si_wfE [] c2_x [ci_False] [vass si_na (tRel 0)] _ _ c2_sub c2_y_typed.
Definition c2_jx := ci_vass_Prop fi_Γ1 (tRel 0) ci_x_typed.
Definition lift_typing_substitutionE_inst :=
  @lift_typing_substitutionE _ si_Σ si_wfE [] c2_x [ci_False] [] _ c2_sub c2_jx.
Definition lift_typing_substE_inst := @lift_typing_substE _ si_Σ si_wfE [] c2_x [ci_False] _ c2_sub c2_jx.
Definition c2_isT_x := ci_on_typeE_Prop fi_Γ1 (tRel 0) ci_x_typed.
Definition isType_substitutionE_inst :=
  @isType_substitutionE _ si_Σ si_wfE [] c2_x [ci_False] [] _ c2_sub c2_isT_x.
Definition isType_substE_inst := @isType_substE _ si_Σ si_wfE [] c2_x [ci_False] _ c2_sub c2_isT_x.
Definition isTypeRel_substitutionE_inst :=
  @isTypeRel_substitutionE _ si_Σ si_wfE [] c2_x [ci_False] [] _ _ c2_sub c2_jx.
Definition isTypeRel_substE_inst := @isTypeRel_substE _ si_Σ si_wfE [] c2_x [ci_False] _ _ c2_sub c2_jx.
Definition substitution_wf_localE_inst :=
  @substitution_wf_localE _ si_Σ si_wfE [] c2_x [ci_False] [vass si_na (tRel 0)] c2_sub c2_wf_Γxy.
Definition substitution0E_inst :=
  @substitution0E _ si_Σ si_wfE [] si_na ci_False fi_P _ _ (ci_app_typed fi_Γ1 (tRel 0) ci_wf_Γ1 ci_x_typed)
    c2_False0.
Lemma c2_d_typed : si_Σ ;;; [vdef si_na ci_False fi_P] |-E tRel 0 : lift0 1 fi_P.
Proof. exact (typeE_Rel _ _ 0 (vdef si_na ci_False fi_P) c2_wf_d eq_refl). Qed.
Definition substitution_letE_inst := @substitution_letE _ si_Σ si_wfE [] si_na ci_False fi_P _ _ c2_d_typed.

(** The η pair under [F := λz:Prop. z]: [G (λy:Prop. (λz:Prop. z) y)] against
    [G (λz:Prop. z)], related at both [pb]. *)
Definition substitution_wt_cumul_pbE_inst :=
  @substitution_wt_cumul_pbE _ rf_Σ wc_wfE Conv [] [vass c1b_na rf_F] [vass c1b_na wc_G_ty] [c2_id] wc_T wc_U
    c2_sub_id (c2_wc_wt Conv).
Definition substitution_cumulE_inst :=
  @substitution_cumulE _ rf_Σ wc_wfE [] [vass c1b_na rf_F] [vass c1b_na wc_G_ty] [c2_id] wc_T wc_U
    c2_sub_id (c2_wc_wt Cumul).
Definition substitution_convE_inst :=
  @substitution_convE _ rf_Σ wc_wfE [] [vass c1b_na rf_F] [vass c1b_na wc_G_ty] [c2_id] wc_T wc_U
    c2_sub_id (c2_wc_wt Conv).

(** Global environment typing carried to the predicate "the context is well formed". *)
Definition on_wf_global_env_implE_inst :
  on_global_env cumulSpecE0 (fun Σ Γ _ => wf_localE Σ Γ) si_env :=
  @on_wf_global_env_implE _ si_env si_wfE (lift_typing typingE) (fun Σ Γ _ => wf_localE Σ Γ)
    (fun Σ Γ j _ _ _ h => lift_typingE_wf_local h) si_wfE.

(** ** [PCUICContextsEta]

  In [si_Σ]: the context [x : Prop, y : x] ([c2_Γxy]) and the context
  [z := ∀P:Prop. P : Prop, y : z] ([c2_Γlet]), which smashing changes into
  [y : ∀P:Prop. P]. *)

Lemma c2_vass_s_x : lift_typing typingE si_Σ fi_Γ1 (j_vass_s si_na (tRel 0) sProp).
Proof. split; [exact tt|]. exists sProp. split; [exact ci_x_typed|]. split; reflexivity. Qed.
Lemma c2_tlc : type_local_ctx (lift_typing typingE) si_Σ fi_Γ1 [vass si_na (tRel 0)] sProp.
Proof. split; [exact ci_wf_sort_P|exact c2_vass_s_x]. Qed.
Lemma c2_slc : sorts_local_ctx (lift_typing typingE) si_Σ fi_Γ1 [vass si_na (tRel 0)] [sProp].
Proof. split; [constructor|exact c2_vass_s_x]. Qed.
Lemma c2_tlc_P : type_local_ctx (lift_typing typingE) si_Σ [] c2_x (Sort.super sProp).
Proof. split; [exact ci_wf_sort_super_P|exact (ci_vass_s_P [] localenv_nil)]. Qed.
Lemma c2_slc_P : sorts_local_ctx (lift_typing typingE) si_Σ [] c2_x [Sort.super sProp].
Proof. split; [constructor|exact (ci_vass_s_P [] localenv_nil)]. Qed.

Definition c2_Γlet : context := [vass si_na (tRel 0); vdef si_na ci_False fi_P].
Lemma c2_wf_Γlet : wf_localE si_Σ c2_Γlet.
Proof. apply localenv_cons_abs; [exact c2_wf_d|exact (ci_vass_Prop _ (tRel 0) c2_d_typed)]. Qed.
Lemma c2_rel_let : wf_local_relE si_Σ ([] ,,, [vdef si_na ci_False fi_P]) [vass si_na (tRel 0)].
Proof. apply localenv_cons_abs; [constructor|exact (ci_vass_Prop _ (tRel 0) c2_d_typed)]. Qed.

Lemma c2_conv_ctx_d : All2_fold (fun Δ Δ' => conv_decls cumulSpecE0 ci_Σu ([] ,,, Δ) ([] ,,, Δ')) [ci_d] [ci_d'].
Proof. constructor; [constructor|exact ci_conv_decls]. Qed.
(** [λ_:Prop. Type@{l0} _] against [Type@{l1}]: both contexts are assumptions. *)
Definition conv_context_smashE_inst :=
  conv_context_smashE ci_Σu [] [ci_d] [ci_d'] ltac:(repeat constructor) c2_conv_ctx_d.
Definition type_local_ctx_wf_localE_inst := type_local_ctx_wf_localE si_Σ fi_Γ1 _ _ ci_wf_Γ1 c2_tlc.
Definition sorts_local_ctx_wf_localE_inst := sorts_local_ctx_wf_localE si_Σ fi_Γ1 _ _ ci_wf_Γ1 c2_slc.
(* NOT BUILT (polymorphic inductive), this and the two [*_local_ctx_instantiateE_inst]:
   proves satisfiability only; [I] is monomorphic, so its only instance is the empty one,
   which changes nothing. *)
Definition instantiate_minductiveE_inst :=
  instantiate_minductiveE si_Σ si_kn si_mdecl [] fi_Γ1 (tRel 0) fi_P si_wfE si_declared_minductive' eq_refl
    ci_x_typed.
Definition type_local_ctx_instantiateE_inst :=
  type_local_ctx_instantiateE si_Σ si_kn si_mdecl fi_Γ1 [vass si_na (tRel 0)] [] sProp si_wfE
    si_declared_minductive' c2_tlc eq_refl.
Definition sorts_local_ctx_instantiateE_inst :=
  sorts_local_ctx_instantiateE si_Σ si_kn si_mdecl fi_Γ1 [vass si_na (tRel 0)] [] [sProp] si_wfE
    si_declared_minductive' c2_slc eq_refl.
(** [y : x] under [x := ∀P:Prop. P]. *)
Definition subst_type_local_ctxE_inst :=
  subst_type_local_ctxE si_Σ [] c2_x [vass si_na (tRel 0)] [ci_False] sProp si_wfE ci_wf_Γ1 c2_tlc c2_sub.
Definition subst_sorts_local_ctxE_inst :=
  subst_sorts_local_ctxE si_Σ [] c2_x [vass si_na (tRel 0)] [ci_False] [sProp] si_wfE ci_wf_Γ1 c2_slc c2_sub.
Definition weaken_type_local_ctxE_inst :=
  weaken_type_local_ctxE si_Σ fi_Γ1 [] c2_x (Sort.super sProp) si_wfE ci_wf_Γ1 c2_tlc_P.
Definition weaken_sorts_local_ctxE_inst :=
  weaken_sorts_local_ctxE si_Σ fi_Γ1 [] c2_x [Sort.super sProp] si_wfE ci_wf_Γ1 c2_slc_P.
(** Smashing the let [z := ∀P:Prop. P] under [y : z]. *)
Definition wf_local_rel_smash_context_genE_inst :=
  @wf_local_rel_smash_context_genE _ si_Σ si_wfE [vdef si_na ci_False fi_P] [vass si_na (tRel 0)] []
    c2_wf_d c2_rel_let.
Definition wf_local_rel_smash_contextE_inst :=
  @wf_local_rel_smash_contextE _ si_Σ si_wfE c2_Γlet [] c2_wf_Γlet.
Definition wf_local_smash_endE_inst := @wf_local_smash_endE _ si_Σ si_wfE [] c2_Γlet c2_wf_Γlet.
Definition wf_local_rel_emptyE_inst := snd (@wf_local_rel_emptyE _ si_Σ c2_Γlet) c2_wf_Γlet.
Definition wf_local_smash_contextE_inst := @wf_local_smash_contextE _ si_Σ si_wfE c2_Γlet c2_wf_Γlet.
(** [x := x] lifted over [y : x]. *)
Definition subslet_liftE_inst := @subslet_liftE _ si_Σ si_wfE fi_Γ1 [vass si_na (tRel 0)] [tRel 0] c2_x
  c2_wf_Γxy c2_sub_x.
Definition subslet_extended_substE_inst := @subslet_extended_substE _ si_Σ si_wfE [] c2_Γlet c2_wf_Γlet.
Definition typing_expand_letsE_inst :=
  @typing_expand_letsE _ si_Σ si_wfE [] [vdef si_na ci_False fi_P] (tRel 0) _ c2_d_typed.

(** ** [PCUICAritiesEta]

  The canonical typing spines: [c (∀P:Prop. P) : (λ_:Prop. I _) (∀P:Prop. P)] in
  [si_Σ] ([c2_sp], an η-expanded head at its end), and the empty spine from
  [G (λy:Prop. F y)] to [G F] in [rf_Σ] ([c2_sp_wc], an η step). The let-type
  [let z := ∀P:Prop. P : Prop in z] ([c2_letT]) exercises the let-in lemmas. *)

Definition c2_I_A : term := tApp (tInd si_ind []) g_A.
Lemma cp_cstr_app_typed : si_Σ ;;; [] |-E tApp (tConstruct si_ind 0 []) g_A : c2_I_A.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (cp_Ix 0) _ g_A
           (cp_cstr_prod_typed [] localenv_nil) (cp_cstr_typed [] localenv_nil) c2_False0).
Qed.
Lemma c2_I_A_typed : si_Σ ;;; [] |-E c2_I_A : tSort sProp.
Proof.
  unfold c2_I_A.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ g_A
           (cp_arity_typedE [] localenv_nil) (cp_ind_typed [] localenv_nil) c2_False0).
Qed.
Lemma c2_isT_I_A : isTypeE si_Σ [] c2_I_A.
Proof. exact (has_sort_isTypeE _ c2_I_A_typed). Qed.
Lemma c2_ws_I_A : ws_cumul_pbE Cumul si_Σ [] c2_I_A g_T.
Proof.
  apply (into_ws_cumul_pbE_spec (Σ := si_Σ) (wfΣ := si_cb) g_cumul); [reflexivity|reflexivity|reflexivity].
Qed.
Lemma c2_sp : typing_spineE si_Σ [] (tProd si_na si_P (cp_Ix 0)) [g_A] g_T.
Proof.
  eapply type_spine_consE.
  - exact g_cstr_isType.
  - exact g_cstr_isType.
  - exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) _ _ g_cstr_isType).
  - exact c2_False0.
  - apply type_spine_nilE; [exact c2_isT_I_A|exact g_T_isType|exact c2_ws_I_A].
Qed.
Lemma c2_sp_wc : typing_spineE rf_Σ wc_Γ wc_T [] wc_U.
Proof. apply type_spine_nilE; [exact (wc_isType _ wc_T_typed)|exact (wc_isType _ wc_U_typed)|exact (c2_wc_ws Cumul)]. Qed.

Definition c2_letT : term := tLetIn si_na ci_False fi_P (tRel 0).
Lemma c2_letT_typed : si_Σ ;;; [] |-E c2_letT : tSort sProp.
Proof.
  eapply typeE_Cumul.
  - apply typeE_LetIn; [|exact c2_d_typed]. split; [exact c2_False0|].
    exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|]. split; reflexivity.
  - exact (ci_typeE_P [] localenv_nil).
  - apply convSpecE_cumulSpecE, red1_cumulSpecE. apply red_zeta.
Qed.
Lemma c2_isT_letT : isTypeE si_Σ [] c2_letT.
Proof. exact (has_sort_isTypeE _ c2_letT_typed). Qed.
Lemma c2_isT_False : isTypeE si_Σ [] ci_False.
Proof. exact (has_sort_isTypeE _ c2_False0). Qed.

Definition isType_SortE_inst := @isType_SortE _ si_Σ fi_Γ1 sProp ci_wf_sort_P ci_wf_Γ1.
Definition wf_typing_spineE_inst : @wf_typing_spineE _ si_Σ [] (tProd si_na si_P (cp_Ix 0)) [g_A] g_T :=
  (g_cstr_isType, typing_spineE_inst).
Definition typing_spine_isType_codomE_inst := @typing_spine_isType_codomE _ si_Σ si_wfE _ _ _ _ c2_sp.
(* NOT BUILT (polymorphic inductive): proves satisfiability only; [I] is monomorphic, so
   its abstract instance is empty and the substitution is the plain one. *)
Definition subslet_inds_genE_inst := @subslet_inds_genE _ si_env si_wfE si_ind si_mdecl si_idecl si_declared_inductive.

Definition consistent_instance_ext_abstract_instanceE_inst :=
  consistent_instance_ext_abstract_instanceE up_env up_univs up_wfE up_global_ext.
Lemma c2_l0_in_union : LevelSet.In (Level.lvar 0)
  (LevelSet.union (fold_right LevelSet.add LevelSet.empty (unfold 1 Level.lvar)) (global_levels up_env)).
Proof. apply LevelSet.mem_spec. reflexivity. Qed.
Definition subst_instance_level_absE_inst := subst_instance_level_absE (Level.lvar 0) 1 up_env up_wfE c2_l0_in_union.

(** [x : λ_:Prop. Prop] against [x : Prop] (η), extended by [y : Prop]. *)
Definition ws_cumul_ctx_pb_vassE_inst :=
  @ws_cumul_ctx_pb_vassE _ si_Σ [] [] si_na si_na fi_eta fi_P Cumul eq_refl ltac:(constructor) (ci_WS_eta Cumul).
Definition ws_cumul_ctx_pb_appE_inst :=
  fst (@ws_cumul_ctx_pb_appE _ si_Σ si_wfE Cumul [] [] [vass si_na fi_eta] [vass si_na fi_P] eq_refl)
    ws_cumul_ctx_pb_vassE_inst.
Definition isType_tProdE_inst := fst (@isType_tProdE _ si_Σ si_wfE [] si_na fi_P (tRel 0)) c2_isT_False.
(** [c (∀P:Prop. P) : I (∀P:Prop. P)] retyped at [(λ_:Prop. I _) (∀P:Prop. P)]. *)
Definition type_ws_cumul_pbE_inst :=
  @type_ws_cumul_pbE _ si_Σ si_cb Cumul [] _ c2_I_A g_T cp_cstr_app_typed g_T_isType c2_ws_I_A.
Definition isType_tLetIn_redE_inst := @isType_tLetIn_redE _ si_Σ si_wfE [] localenv_nil _ _ _ _ c2_isT_letT.
Definition isType_tLetIn_domE_inst := @isType_tLetIn_domE _ si_Σ si_wfE [] localenv_nil _ _ _ _ c2_isT_letT.
Definition wf_local_assE_inst := @wf_local_assE _ si_Σ [] si_na fi_P localenv_nil (ci_vass_P [] localenv_nil).
Definition wf_local_defE_inst :=
  @wf_local_defE _ si_Σ [] si_na ci_False fi_P localenv_nil (ci_vass_P [] localenv_nil) c2_False0.
Definition isType_applyE_inst := @isType_applyE _ si_Σ si_wfE [] si_na fi_P (tRel 0) ci_False c2_isT_False c2_False0.
Lemma c2_sp_let_nil : typing_spineE si_Σ [] c2_letT [] ci_False.
Proof.
  apply type_spine_nilE; [exact c2_isT_letT|exact c2_isT_False|].
  exact (@ws_cumul_pbE_zetaE _ si_Σ si_wfE Cumul [] si_na ci_False fi_P (tRel 0) c2_isT_letT).
Qed.
Definition typing_spine_letin_invE_inst := @typing_spine_letin_invE _ si_Σ si_wfE [] _ _ _ _ _ _ c2_sp_let_nil.
Lemma c2_sp_False_nil : typing_spineE si_Σ [] ci_False [] ci_False.
Proof.
  apply type_spine_nilE; [exact c2_isT_False|exact c2_isT_False|].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) _ _ c2_isT_False).
Qed.
Definition typing_spine_letinE_inst :=
  @typing_spine_letinE _ si_Σ si_wfE [] si_na ci_False fi_P (tRel 0) [] ci_False c2_isT_letT c2_sp_False_nil.
Lemma c2_sp_wc_refl : typing_spineE rf_Σ wc_Γ wc_T [] wc_T.
Proof.
  apply type_spine_nilE; [exact (wc_isType _ wc_T_typed)|exact (wc_isType _ wc_T_typed)|].
  exact (isType_ws_cumul_pbE_refl (Σ := rf_Σ) (wfΣ := wc_wfE) _ _ (wc_isType _ wc_T_typed)).
Qed.
(** The empty spine at [G (λy:Prop. F y)], widened to [G F] by the η step. *)
Definition typing_spine_weaken_conclE_inst :=
  @typing_spine_weaken_conclE _ rf_Σ wc_wfE wc_Γ wc_T [] wc_T wc_U c2_sp_wc_refl (c2_wc_ws Cumul) (wc_isType _ wc_U_typed).
Lemma c2_sp_tail : typing_spineE si_Σ [] ((cp_Ix 0) {0 := g_A}) [] g_T.
Proof. apply type_spine_nilE; [exact c2_isT_I_A|exact g_T_isType|exact c2_ws_I_A]. Qed.
Definition typing_spine_prodE_inst :=
  @typing_spine_prodE _ si_Σ si_wfE [] si_na g_A si_P (cp_Ix 0) [] g_T c2_sp_tail g_cstr_isType c2_False0.
Definition typing_spine_WAT_conclE_inst := @typing_spine_WAT_conclE _ si_Σ _ _ _ _ c2_sp.
Definition typing_spine_isType_domE_inst := @typing_spine_isType_domE _ si_Σ _ _ _ _ c2_sp.
Definition c2_x_sort : si_Σ ;;; [] ,, vass si_na fi_P |-E tRel 0 : tSort sProp := ci_x_typed.
Definition type_mkProd_or_LetInE_inst :=
  @type_mkProd_or_LetInE _ si_Σ si_wfE [] (vass si_na fi_P) (Sort.super sProp) (tRel 0) sProp
    (ci_vass_s_P [] localenv_nil) c2_x_sort.
Lemma c2_jd : lift_typing typingE si_Σ [] (j_decl_s (vdef si_na ci_False fi_P) (Some (Sort.super sProp))).
Proof. split; [exact c2_False0|]. exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|]. split; reflexivity. Qed.
Definition type_mkProd_or_LetInE_let_inst :=
  @type_mkProd_or_LetInE _ si_Σ si_wfE [] (vdef si_na ci_False fi_P) (Sort.super sProp) (tRel 0) sProp c2_jd c2_d_typed.
Definition type_it_mkProd_or_LetInE_inst :=
  @type_it_mkProd_or_LetInE _ si_Σ si_wfE [] c2_x (Sort.super sProp) (tRel 0) sProp ci_wf_sort_super_P c2_tlc_P ci_x_typed.
Definition type_it_mkProd_or_LetIn_sortsE_inst :=
  @type_it_mkProd_or_LetIn_sortsE _ si_Σ si_wfE [] c2_x [Sort.super sProp] (tRel 0) sProp c2_slc_P ci_x_typed.
Definition isType_it_mkProd_or_LetInE_inst :=
  @isType_it_mkProd_or_LetInE _ si_Σ si_wfE [] c2_x [Sort.super sProp] (tRel 0) c2_slc_P c2_isT_x.
Definition subslet_app_closedE_inst :=
  @subslet_app_closedE _ si_Σ [] [ci_False] [ci_False] c2_x c2_x c2_sub c2_sub eq_refl.
Definition subslet_app_invE_inst :=
  @subslet_app_invE _ si_Σ [] c2_x c2_x [ci_False; ci_False] subslet_app_closedE_inst.
(* NOT BUILT (polymorphic inductive), this and [on_minductive_wf_paramsE_inst]: proves
   satisfiability only; [I] is monomorphic, so its only instance is the empty one. See
   "NOT BUILT: the instances that need a universe-polymorphic inductive" above for the
   witness that is missing and what it costs. *)
Definition subslet_indsE_inst := @subslet_indsE _ si_Σ si_wfE si_ind [] si_mdecl si_idecl si_declared_inductive eq_refl.
Definition weaken_subsletE_inst := @weaken_subsletE _ si_Σ si_wfE [ci_False] c2_x fi_Γ1 ci_wf_Γ1 c2_sub.
Definition isType_substitution_it_mkProd_or_LetInE_inst :=
  @isType_substitution_it_mkProd_or_LetInE _ si_Σ si_wfE [] c2_x (tRel 0) [ci_False] c2_sub c2_isT_False.
Definition isType_substitution_it_mkProd_or_LetInE_let_inst :=
  @isType_substitution_it_mkProd_or_LetInE _ si_Σ si_wfE [] [vdef si_na ci_False fi_P] (tRel 0) [ci_False]
    c2_subd c2_isT_letT.
Definition on_minductive_wf_paramsE_inst :=
  @on_minductive_wf_paramsE _ si_Σ si_wfE si_kn si_mdecl [] si_declared_minductive' eq_refl.
Definition it_mkProd_or_LetIn_wf_localE_inst :=
  @it_mkProd_or_LetIn_wf_localE _ si_Σ si_wfE [] c2_x (tRel 0) _ c2_False0.
Definition it_mkProd_or_LetIn_wf_localE_let_inst :=
  @it_mkProd_or_LetIn_wf_localE _ si_Σ si_wfE [] [vdef si_na ci_False fi_P] (tRel 0) _ c2_letT_typed.
Definition isType_it_mkProd_or_LetIn_wf_localE_inst :=
  @isType_it_mkProd_or_LetIn_wf_localE _ si_Σ si_wfE [] c2_x (tRel 0) c2_isT_False.
Definition isType_weakenE_inst := @isType_weakenE _ si_Σ si_wfE fi_Γ1 ci_False ci_wf_Γ1 c2_isT_False.

(** ** [PCUICTypingEtaNotions]

  [Type@{l0}] in [up_Σp] (a relevant type of [Type@{l0+1}]) and [I (∀P:Prop. P)] in
  [si_Σ] (a type of [Prop]). *)

Definition isTypeRelE_isTypeE_inst := isTypeRelE_isTypeE _ _ _ _ up_isTypeRel_s0.
Definition isTypeE_welltypedE_inst := isTypeE_welltypedE c2_isT_I_A.
Definition isTypeRelE_welltypedE_inst := isTypeRelE_welltypedE up_isTypeRel_s0.
Definition has_sort_isTypeE_inst := has_sort_isTypeE _ c2_I_A_typed.
Definition has_sort_isTypeRelE_inst := has_sort_isTypeRelE (Sort.super up_s0) Relevant eq_refl up_s0_typed.
