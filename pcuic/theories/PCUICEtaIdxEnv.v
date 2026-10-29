(* Distributed under the terms of the MIT license. *)

(** * An indexed, cumulative, universe-polymorphic inductive family whose user arity has a redex

  BET-64 EtaCheckerLane (ETAK), 2026-10-29. The environment [ji_env] declares one inductive family,
  for the instances of [PCUICTypingEtaHyps] that the environment [si_Σ] of
  [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) : Prop := c : I A], no index, a
  constructor without argument, a monomorphic universe context, a user arity equal to the built arity)
  cannot make non-degenerate:

    Polymorphic Cumulative Inductive J@{i} (A : Prop) : forall (X : Type@{i}), (fun Z : Type@{Set+1} => Z) Prop :=
    | jc : forall (X : Type@{i}), J A X.

  - [J] has one index [X : Type@{i}]; its type carries the universe level, so the index contexts of
    [J] at two instances differ;
  - the constructor [jc] takes one argument [X], which is the index of its conclusion;
  - the universe level [i] is covariant ([ind_variance = Some [Covariant]]);
  - after the parameter, the user arity [Π (X : Type@{i}). (λ Z : Type@{Set+1}. Z) Prop] has a
    β-redex, so it is not the built arity [Π (X : Type@{i}). Prop]; [on_ind_body]'s
    [ind_arity_red] asks only that the kernel's reduction take it there ([arity_red]).

  The global universes declare one level [a], with no constraint; the instances use [J@{Set}] and
  [J@{a}]. [ji_wf] proves [wf ji_env], [ji_wfE] [wfE ji_env]; [ji_wf_ext] and [ji_wf_extE] prove the
  monomorphic extension [ji_Σ] well formed, [ji_wf_extp] the extension [ji_Σp] by the universe context
  of [J]. The section "Base derivations" gives the base typing facts the instances of
  [PCUICTypingEtaHyps] lift to the η typing. No axiom is used. *)

From Stdlib Require Import ssreflect ssrbool Lia ZArith.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICArityRed PCUICCumulativitySpec PCUICReduction PCUICCases PCUICContextSubst
     PCUICTypingEta PCUICClosedBodies PCUICClosedTyp PCUICWfUniverses PCUICWellScopedCumulativity
     PCUICCumulativitySpecEtaClosureInstances.
From MetaRocq.PCUIC Require PCUICSubstitution PCUICSpine PCUICArities PCUICInductives PCUICInductiveInversion.

#[local] Existing Instance default_checker_flags.

(** ** The environment *)

Definition ji_kn : kername := (MPfile ["EtaIdx"], "J").
Definition ji_ind : inductive := {| inductive_mind := ji_kn; inductive_ind := 0 |}.

(** [Type@{i}], for the universe level [i] of [J]. *)
Definition ji_s : sort := sType (Universe.make' (Level.lvar 0)).
Definition ji_T : term := tSort ji_s.

Definition ji_naX : aname := mkBindAnn (nNamed "X") Relevant.
Definition ji_naZ : aname := mkBindAnn (nNamed "Z") Relevant.
Definition ji_naJ : aname := mkBindAnn (nNamed "J") rel_of_Type.

Definition ji_params : context := [vass si_na si_P].
Definition ji_indices : context := [vass ji_naX ji_T].

(** [(λ Z : Type@{Set+1}. Z) Prop]: a β-redex; its reduct is [Prop]. *)
Definition ji_redex : term := tApp (tLambda ji_naZ (tSort (Sort.super sProp)) (tRel 0)) (tSort sProp).

(** The user arity [Π (A : Prop) (X : Type@{i}). (λ Z. Z) Prop] and the built arity
    [Π (A : Prop) (X : Type@{i}). Prop]. *)
Definition ji_arity : term := tProd si_na si_P (tProd ji_naX ji_T ji_redex).
Definition ji_built : term := tProd si_na si_P (tProd ji_naX ji_T (tSort sProp)).

(** [jc : Π (A : Prop) (X : Type@{i}). J A X]; [J] is [tRel 2] under the two binders. *)
Definition ji_cdecl : constructor_body :=
  {| cstr_name := "jc"; cstr_args := [vass ji_naX ji_T]; cstr_indices := [tRel 0];
     cstr_type := tProd si_na si_P (tProd ji_naX ji_T (tApp (tApp (tRel 2) (tRel 1)) (tRel 0)));
     cstr_arity := 1 |}.

(** The argument [X : Type@{i}] of [jc] is not a proposition, so [J] eliminates into [Prop] and
    [SProp] only ([elim_sort_prop_ind]). *)
Definition ji_idecl : one_inductive_body :=
  {| ind_name := "J"; ind_indices := ji_indices; ind_sort := sProp; ind_type := ji_arity;
     ind_kelim := IntoPropSProp; ind_ctors := [ji_cdecl]; ind_projs := []; ind_relevance := Relevant |}.

Definition ji_udecl : universes_decl := Polymorphic_ctx ([nNamed "i"], ConstraintSet.empty).

Definition ji_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 1; ind_params := ji_params; ind_bodies := [ji_idecl];
     ind_universes := ji_udecl; ind_variance := Some [Variance.Covariant] |}.

(** One global level [a], with no constraint. *)
Definition ji_a : Level.t := Level.level "a".
Definition ji_univs : ContextSet.t := (LevelSet.singleton ji_a, ConstraintSet.empty).

Definition ji_env : global_env :=
  {| universes := ji_univs; declarations := [(ji_kn, InductiveDecl ji_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

(** The monomorphic extension, where the instances live, and the extension by the universe context
    of [J], where its user arity and constructor type are typed. *)
Definition ji_Σ : global_env_ext := (ji_env, Monomorphic_ctx).
Definition ji_Σp : global_env_ext := (ji_env, ji_udecl).

(** The environment the declaration is checked in. *)
Definition ji_Σ0 : global_env_ext := (mk_global_env ji_univs [] Retroknowledge.empty, ji_udecl).

(** The doubled universe context of the variance check, with [i₁ ≤ i₀] ([variance_universes]). *)
Definition ji_vcstr : UnivConstraint.t := (Level.lvar 1, ConstraintType.Le 0, Level.lvar 0).
Definition ji_udecl2 : universes_decl :=
  Polymorphic_ctx ([nNamed "i"; nNamed "i"],
    ConstraintSet.union (ConstraintSet.union ConstraintSet.empty (lift_constraints 1 ConstraintSet.empty))
      (variance_cstrs [Variance.Covariant] [Level.lvar 1] [Level.lvar 0])).
Definition ji_Σ2 : global_env_ext := (ji_Σ0.1, ji_udecl2).

(** [a ↦ 1]. *)
Definition ji_val : valuation := {| valuation_mono := fun _ => 1%positive; valuation_poly := fun _ => 0 |}.

Lemma ji_for_all (f : Level.t -> bool) (s : LevelSet.t) :
  LevelSet.for_all f s = true -> LevelSet.For_all (fun l => f l = true) s.
Proof.
  intros h. apply LevelSet.for_all_spec; first [exact h | intros x y e; hnf in e; subst; reflexivity].
Qed.

(** ** Typing in any extension

  The environment is an explicit argument of each lemma (no section variable), instantiated below at
  [ji_Σ0], [ji_Σ] and [ji_Σp]. *)

Lemma ji_vass (Σ : global_env_ext) (Γ : context) (na : aname) A s :
  Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) -> lift_typing typing Σ Γ (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma ji_vass_s (Σ : global_env_ext) (Γ : context) (na : aname) A s :
  Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) -> lift_typing typing Σ Γ (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma ji_wf_cons (Σ : global_env_ext) (Γ : context) (na : aname) A s :
  wf_local Σ Γ -> Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) -> wf_local Σ (Γ ,, vass na A).
Proof. intros h hA r. apply localenv_cons_abs; [exact h|exact (ji_vass Σ Γ na A s hA r)]. Qed.

Lemma ji_P_ty (Σ : global_env_ext) (Γ : context) : wf_local Σ Γ -> Σ ;;; Γ |- si_P : tSort (Sort.super sProp).
Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

Lemma ji_P1_ty (Σ : global_env_ext) (Γ : context) :
  wf_local Σ Γ -> Σ ;;; Γ |- tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)).
Proof. intros h. apply type_Sort; [exact h|exact (PCUICWfUniverses.wf_sort_type1 Σ)]. Qed.

Lemma ji_wf_A (Σ : global_env_ext) (Γ : context) : wf_local Σ Γ -> wf_local Σ (Γ ,, vass si_na si_P).
Proof. intros h. exact (ji_wf_cons Σ Γ si_na si_P _ h (ji_P_ty Σ Γ h) eq_refl). Qed.

(** [(λ Z : Type@{Set+1}. Z) Prop : Type@{Set+1}]. *)
Lemma ji_redex_ty (Σ : global_env_ext) (Γ : context) :
  wf_local Σ Γ -> Σ ;;; Γ |- ji_redex : tSort (Sort.super sProp).
Proof.
  intros h. unfold ji_redex.
  have hZ : wf_local Σ (Γ ,, vass ji_naZ (tSort (Sort.super sProp))) :=
    ji_wf_cons Σ Γ ji_naZ _ _ h (ji_P1_ty Σ Γ h) eq_refl.
  refine (type_App _ _ _ ji_naZ (tSort (Sort.super sProp)) (tSort (Sort.super sProp)) _ (tSort sProp) _ _ _).
  - apply type_Prod; [exact (ji_vass_s Σ _ ji_naZ _ _ (ji_P1_ty Σ Γ h) eq_refl)|exact (ji_P1_ty Σ _ hZ)].
  - apply type_Lambda; [exact (ji_vass Σ _ ji_naZ _ _ (ji_P1_ty Σ Γ h) eq_refl)|].
    exact (type_Rel _ _ 0 (vass ji_naZ (tSort (Sort.super sProp))) hZ eq_refl).
  - exact (ji_P_ty Σ Γ h).
Qed.

(** [(λ Z. Z) Prop ≤ Prop], by β. *)
Lemma ji_redex_cumul (Σ : global_env_ext) (Γ : context) : Σ ;;; Γ |- ji_redex <=s tSort sProp.
Proof. exact (cumul_beta Σ Γ Cumul ji_naZ (tSort (Sort.super sProp)) (tRel 0) (tSort sProp)). Qed.

(** ** Typing in an extension that declares the level [i] ([hs : wf_sort Σ ji_s]) *)

Lemma ji_T_ty (Σ : global_env_ext) (hs : wf_sort Σ ji_s) (Γ : context) :
  wf_local Σ Γ -> Σ ;;; Γ |- ji_T : tSort (Sort.super ji_s).
Proof. intros h. apply type_Sort; [exact h|exact hs]. Qed.

Lemma ji_wf_X (Σ : global_env_ext) (hs : wf_sort Σ ji_s) (Γ : context) :
  wf_local Σ Γ -> wf_local Σ (Γ ,, vass ji_naX ji_T).
Proof. intros h. exact (ji_wf_cons Σ Γ ji_naX ji_T _ h (ji_T_ty Σ hs Γ h) eq_refl). Qed.

Lemma ji_arity_ty (Σ : global_env_ext) (hs : wf_sort Σ ji_s) (Γ : context) : wf_local Σ Γ ->
  Σ ;;; Γ |- ji_arity : tSort (Sort.sort_of_product (Sort.super sProp)
                                 (Sort.sort_of_product (Sort.super ji_s) (Sort.super sProp))).
Proof.
  intros h. have h1 := ji_wf_A Σ Γ h. have h2 := ji_wf_X Σ hs _ h1. unfold ji_arity.
  apply type_Prod; [exact (ji_vass_s Σ _ si_na _ _ (ji_P_ty Σ Γ h) eq_refl)|].
  apply type_Prod; [exact (ji_vass_s Σ _ ji_naX _ _ (ji_T_ty Σ hs _ h1) eq_refl)|].
  exact (ji_redex_ty Σ _ h2).
Qed.

Lemma ji_built_ty (Σ : global_env_ext) (hs : wf_sort Σ ji_s) (Γ : context) : wf_local Σ Γ ->
  Σ ;;; Γ |- ji_built : tSort (Sort.sort_of_product (Sort.super sProp)
                                 (Sort.sort_of_product (Sort.super ji_s) (Sort.super sProp))).
Proof.
  intros h. have h1 := ji_wf_A Σ Γ h. have h2 := ji_wf_X Σ hs _ h1. unfold ji_built.
  apply type_Prod; [exact (ji_vass_s Σ _ si_na _ _ (ji_P_ty Σ Γ h) eq_refl)|].
  apply type_Prod; [exact (ji_vass_s Σ _ ji_naX _ _ (ji_T_ty Σ hs _ h1) eq_refl)|].
  exact (ji_P_ty Σ _ h2).
Qed.

Definition ji_Γi : context := [vass ji_naJ ji_arity].

Lemma ji_wf_Γi (Σ : global_env_ext) (hs : wf_sort Σ ji_s) : wf_local Σ ji_Γi.
Proof.
  apply localenv_cons_abs; [constructor|].
  exact (ji_vass Σ _ ji_naJ _ _ (ji_arity_ty Σ hs [] localenv_nil) eq_refl).
Qed.

(** [Π (A : Prop) (X : Type@{i}). J A X : Prop]: [J A X] has type [(λ Z. Z) Prop], which reduces to
    [Prop]. *)
Lemma ji_ctype_ty (Σ : global_env_ext) (hs : wf_sort Σ ji_s) :
  Σ ;;; ji_Γi |- cstr_type ji_cdecl
    : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.sort_of_product (Sort.super ji_s) sProp)).
Proof.
  have h1 := ji_wf_A Σ ji_Γi (ji_wf_Γi Σ hs). have h2 := ji_wf_X Σ hs _ h1. cbn [cstr_type ji_cdecl].
  apply type_Prod; [exact (ji_vass_s Σ _ si_na _ _ (ji_P_ty Σ _ (ji_wf_Γi Σ hs)) eq_refl)|].
  apply type_Prod; [exact (ji_vass_s Σ _ ji_naX _ _ (ji_T_ty Σ hs _ h1) eq_refl)|].
  have hJ : Σ ;;; ((ji_Γi ,, vass si_na si_P) ,, vass ji_naX ji_T) |- tRel 2 : ji_arity :=
    type_Rel _ _ 2 (vass ji_naJ ji_arity) h2 eq_refl.
  have hJA : Σ ;;; ((ji_Γi ,, vass si_na si_P) ,, vass ji_naX ji_T) |- tApp (tRel 2) (tRel 1)
               : tProd ji_naX ji_T ji_redex :=
    type_App _ _ (tRel 2) si_na si_P (tProd ji_naX ji_T ji_redex) _ (tRel 1)
      (ji_arity_ty Σ hs _ h2) hJ (type_Rel _ _ 1 (vass si_na si_P) h2 eq_refl).
  have hJAX : Σ ;;; ((ji_Γi ,, vass si_na si_P) ,, vass ji_naX ji_T) |- tApp (tApp (tRel 2) (tRel 1)) (tRel 0)
                : ji_redex :=
    type_App _ _ (tApp (tRel 2) (tRel 1)) ji_naX ji_T ji_redex _ (tRel 0)
      (type_Prod _ _ ji_naX ji_T ji_redex _ _ (ji_vass_s Σ _ ji_naX _ _ (ji_T_ty Σ hs _ h2) eq_refl)
         (ji_redex_ty Σ _ (ji_wf_X Σ hs _ h2)))
      hJA (type_Rel _ _ 0 (vass ji_naX ji_T) h2 eq_refl).
  exact (type_Cumul _ _ _ ji_redex (tSort sProp) (Sort.super sProp) hJAX (ji_P_ty Σ _ h2)
           (ji_redex_cumul Σ _)).
Qed.

(** ** The declaration is well formed *)

Lemma ji_levels_Σ0 : LevelSet.In (Level.lvar 0) (global_ext_levels ji_Σ0).
Proof. apply LevelSet.mem_spec. vm_compute. reflexivity. Qed.

Lemma ji_levels_Σp : LevelSet.In (Level.lvar 0) (global_ext_levels ji_Σp).
Proof. apply LevelSet.mem_spec. vm_compute. reflexivity. Qed.

Lemma ji_hs_of (Σ : global_env_ext) : LevelSet.In (Level.lvar 0) (global_ext_levels Σ) -> wf_sort Σ ji_s.
Proof. intros h l hin%LevelExprSet.singleton_spec. subst l. exact h. Qed.

Definition ji_hs0 : wf_sort ji_Σ0 ji_s := ji_hs_of ji_Σ0 ji_levels_Σ0.
Definition ji_hsp : wf_sort ji_Σp ji_s := ji_hs_of ji_Σp ji_levels_Σp.

(** [Type@{i₁} ≤ Type@{i₀}] under the variance constraint [i₁ ≤ i₀]. *)
Lemma ji_cumul_T (Γ : context) :
  cumulSpec0 ji_Σ2 Γ Cumul (tSort (sType (Universe.make' (Level.lvar 1))))
    (tSort (sType (Universe.make' (Level.lvar 0)))).
Proof.
  apply cumul_Sort.
  change (leq0_universe_n 0 (global_ext_constraints ji_Σ2) (Universe.make' (Level.lvar 1))
            (Universe.make' (Level.lvar 0))).
  intros v hv.
  have hin : ConstraintSet.In ji_vcstr (global_ext_constraints ji_Σ2).
  { apply ConstraintSet.mem_spec. vm_compute. reflexivity. }
  have hsat := hv _ hin. unfold ji_vcstr in hsat. inversion hsat; subst.
  rewrite !Universe.val_make'. assumption.
Qed.

Lemma ji_on_constructor :
  on_constructor cumulSpec0 (lift_typing typing) ji_Σ0 ji_mdecl 0 ji_idecl ji_indices ji_cdecl
    [Sort.super ji_s].
Proof.
  have h1 := ji_wf_A ji_Σ0 ji_Γi (ji_wf_Γi ji_Σ0 ji_hs0).
  have h2 := ji_wf_X ji_Σ0 ji_hs0 _ h1.
  unshelve econstructor.
  - (* cstr_args_length *) reflexivity.
  - (* cstr_eq *) reflexivity.
  - (* on_ctype *)
    exact (ji_vass ji_Σ0 _ (mkBindAnn nAnon Relevant) _ _ (ji_ctype_ty ji_Σ0 ji_hs0) eq_refl).
  - (* on_cargs *)
    split; [exact tt|]. exact (ji_vass_s ji_Σ0 _ ji_naX _ _ (ji_T_ty ji_Σ0 ji_hs0 _ h1) eq_refl).
  - (* on_cindices: the index [X] of the conclusion has type [Type@{i}] *)
    cbn. econstructor; [|cbn; constructor].
    split; [exact (type_Rel _ _ 0 (vass ji_naX ji_T) h2 eq_refl)|].
    exists (Sort.super ji_s). split; [exact (ji_T_ty ji_Σ0 ji_hs0 _ h2)|split; exact I].
  - (* on_ctype_positive *)
    cbn. eapply pos_ass; [apply pos_arg_closed; reflexivity|].
    eapply pos_ass; [apply pos_arg_closed; reflexivity|].
    exact (pos_concl _ _ _ [vass ji_naX ji_T; vass si_na si_P] [tRel 1; tRel 0]
             (All_cons (x := tRel 1) (eq_refl : is_true (closedn 2 (tRel 1)))
                (All_cons (x := tRel 0) (eq_refl : is_true (closedn 2 (tRel 0))) All_nil))).
  - (* on_ctype_variance: the argument [X : Type@{i}] at [i₁] is below its copy at [i₀]; the index
       [X] is the same variable at both *)
    intros v e. cbn in e. injection e as <-. cbn. split.
    + constructor; [constructor|]. constructor; [reflexivity|]. exact (ji_cumul_T _).
    + constructor; [apply cumul_Refl|constructor].
  - (* on_lets_in_type *) destruct lets_in_constructor_types; [exact I|reflexivity].
Qed.

Lemma ji_on_ind_body : on_ind_body cumulSpec0 (lift_typing typing) ji_Σ0 ji_kn ji_mdecl 0 ji_idecl.
Proof.
  unshelve econstructor.
  - (* ind_cunivs *) exact [[Sort.super ji_s]].
  - (* ind_arity_red: after the parameter, [Π X. (λ Z. Z) Prop] reduces to [Π X. Prop] *)
    exists (tProd ji_naX ji_T ji_redex). split; [reflexivity|].
    change (arity_red ji_Σ0.1 ji_params (tProd ji_naX ji_T ji_redex) ([] ++ [vass ji_naX ji_T]) sProp).
    eapply arity_red_prod; [apply whd_stop; reflexivity|].
    apply arity_red_sort. unfold ji_redex. apply whd_app. apply whd_beta. cbn. apply whd_stop. reflexivity.
  - (* onArity *)
    exact (ji_vass ji_Σ0 _ (mkBindAnn nAnon rel_of_Type) _ _ (ji_arity_ty ji_Σ0 ji_hs0 [] localenv_nil) eq_refl).
  - (* onArityRed *)
    exact (ji_vass ji_Σ0 _ (mkBindAnn nAnon rel_of_Type) _ _ (ji_built_ty ji_Σ0 ji_hs0 [] localenv_nil) eq_refl).
  - (* onConstructors *) constructor; [exact ji_on_constructor|constructor].
  - (* onProjections *) exact I.
  - (* ind_sorts *) reflexivity.
  - (* ind_relevance_compat *) reflexivity.
  - (* onIndices: the index [X : Type@{i}] at [i₁] is below its copy at [i₀] *)
    cbn. constructor; [constructor|]. constructor; [reflexivity|]. exact (ji_cumul_T _).
Qed.

Lemma ji_on_inductive : on_inductive cumulSpec0 (lift_typing typing) ji_Σ0 ji_kn ji_mdecl.
Proof.
  constructor.
  - constructor; [exact ji_on_ind_body|constructor].
  - exact (ji_wf_A ji_Σ0 [] localenv_nil).
  - reflexivity.
  - (* on_variance: the two copies [i₁], [i₀] of the level are consistent instances of [J@{i}] in
       the doubled context *)
    cbn. do 3 eexists. split; [reflexivity| | |reflexivity].
    all: split; [vm_compute; reflexivity|split; [reflexivity|]].
    all: intros v _ c hc; exfalso; eapply ConstraintSet.empty_spec; exact hc.
Qed.

Lemma ji_on_udecl : on_udecl ji_univs ji_udecl.
Proof.
  have hfresh : LevelSet.for_all (fun l => negb (LevelSet.mem l (global_levels ji_univs)))
                  (levels_of_udecl ji_udecl) = true.
  { vm_compute. reflexivity. }
  split; [|split; [|split]].
  - intros l hl hin.
    have h := ji_for_all _ _ hfresh l hl. cbv beta in h.
    have hin' : LevelSet.mem l (global_levels ji_univs) = true := proj2 (LevelSet.mem_spec _ _) hin.
    rewrite hin' in h. cbn in h. discriminate h.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists ji_val. intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma ji_on_udecl_mono : on_udecl ji_univs Monomorphic_ctx.
Proof.
  split; [|split; [|split]].
  - intros x Hx. exfalso. eapply LevelSet.empty_spec. exact Hx.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists ji_val. intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma ji_wf : wf ji_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + have h : LevelSet.for_all (fun l => negb (Level.is_var l)) (global_levels ji_univs) = true.
      { vm_compute. reflexivity. }
      intros l hl. exact (ji_for_all _ _ h l hl).
    + exists ji_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - (* trunk's wf: the retroknowledge conjunct, then the declarations *)
    split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact ji_on_udecl.
    + exact ji_on_inductive.
    + (* on_prim_decl: no boolean type is registered *)
      cbn. intros i h; discriminate h.
Qed.

Definition ji_wfE : wfE ji_env := wf_incl_E ji_wf.

Lemma ji_wf_ext : wf_ext ji_Σ.
Proof. split; [exact ji_wf|exact ji_on_udecl_mono]. Qed.

Lemma ji_wf_extE : wf_extE ji_Σ.
Proof. exact (wf_ext_incl_E ji_wf_ext). Qed.

Lemma ji_wf_extp : wf_ext ji_Σp.
Proof. split; [exact ji_wf|exact ji_on_udecl]. Qed.

Lemma ji_declared_minductive : declared_minductive ji_Σ ji_kn ji_mdecl.
Proof. left; reflexivity. Qed.

Lemma ji_declared_inductive : declared_inductive ji_Σ ji_ind ji_mdecl ji_idecl.
Proof. split; [left; reflexivity|reflexivity]. Qed.

Lemma ji_declared_constructor : declared_constructor ji_Σ (ji_ind, 0) ji_mdecl ji_idecl ji_cdecl.
Proof. split; [exact ji_declared_inductive|reflexivity]. Qed.

(** ** Base derivations, for the instances of [PCUICTypingEtaHyps]

  The instances use [J@{Set}] and [J@{a}]: the instances [ji_u0 = [Set]] and [ji_u1 = [a]], at which
  the index type [Type@{i}] becomes [Type@{Set}] ([ji_TSet], i.e. [tSort Sort.type0]) and
  [Type@{a}]. The context [ji_Γ = (A : Prop) (X : Type@{Set})] is the telescope of [J@{Set}]: [J A X]
  ([ji_JAX]) is a proposition in it. *)

Definition ji_u0 : Instance.t := [Level.lzero].
Definition ji_u1 : Instance.t := [ji_a].
Definition ji_TSet : term := tSort Sort.type0.
Definition ji_Γ : context := [vass ji_naX ji_TSet; vass si_na si_P].
Definition ji_pargs : list term := [tRel 1; tRel 0].
Definition ji_JAX : term := mkApps (tInd ji_ind ji_u0) ji_pargs.
(** [(λ Y : Prop. Y) A], β-convertible to [A]. *)
Definition ji_idA : term := tApp (tLambda si_na si_P (tRel 0)) (tRel 1).

Lemma ji_T_u0 : subst_instance ji_u0 ji_T = ji_TSet.
Proof. reflexivity. Qed.

Lemma ji_cons0 : consistent_instance_ext ji_Σ (ind_universes ji_mdecl) ji_u0.
Proof.
  split; [vm_compute; reflexivity|split; [reflexivity|]].
  intros v _ c hc. exfalso. eapply ConstraintSet.empty_spec. exact hc.
Qed.

Lemma ji_cons1 : consistent_instance_ext ji_Σ (ind_universes ji_mdecl) ji_u1.
Proof.
  split; [vm_compute; reflexivity|split; [reflexivity|]].
  intros v _ c hc. exfalso. eapply ConstraintSet.empty_spec. exact hc.
Qed.

(** [J@{Set}] and [J@{a}] fully applied (two arguments) are compared at the variance of [J]:
    [Set ≤ a] holds at every valuation. *)
Lemma ji_cmp : PCUICEquality.cmp_ind_universes ji_Σ ji_ind 2 ji_u0 ji_u1.
Proof.
  change (cmp_opt_variance (compare_universe (global_ext_constraints ji_Σ)) Cumul
            (Variance [Variance.Covariant]) ji_u0 ji_u1).
  right. constructor; [|constructor].
  change (leq0_universe_n 0 (global_ext_constraints ji_Σ) (Universe.make' Level.lzero) (Universe.make' ji_a)).
  intros v _. rewrite !Universe.val_make'. cbn. lia.
Qed.

Lemma ji_TSet_ty (Γ : context) : wf_local ji_Σ Γ -> ji_Σ ;;; Γ |- ji_TSet : tSort (Sort.super Sort.type0).
Proof. intros h. apply type_Sort; [exact h|exact (PCUICWfUniverses.wf_sort_type0 ji_Σ)]. Qed.

Lemma ji_wf_ΓX (Γ : context) : wf_local ji_Σ Γ -> wf_local ji_Σ (Γ ,, vass ji_naX ji_TSet).
Proof. intros h. exact (ji_wf_cons ji_Σ Γ ji_naX ji_TSet _ h (ji_TSet_ty Γ h) eq_refl). Qed.

Lemma ji_wf_Γ : wf_local ji_Σ ji_Γ.
Proof. exact (ji_wf_ΓX _ (ji_wf_A ji_Σ [] localenv_nil)). Qed.

Lemma ji_wf_ΓΓ : wf_local ji_Σ (ji_Γ ,,, ji_Γ).
Proof. exact (ji_wf_ΓX _ (ji_wf_A ji_Σ _ ji_wf_Γ)). Qed.

Lemma ji_wf_ΓA : wf_local ji_Σ (ji_Γ ,,, [vass si_na si_P]).
Proof. exact (ji_wf_A ji_Σ _ ji_wf_Γ). Qed.

Lemma ji_A_ty : ji_Σ ;;; ji_Γ |- tRel 1 : si_P.
Proof. exact (type_Rel _ _ 1 (vass si_na si_P) ji_wf_Γ eq_refl). Qed.

Lemma ji_X_ty : ji_Σ ;;; ji_Γ |- tRel 0 : ji_TSet.
Proof. exact (type_Rel _ _ 0 (vass ji_naX ji_TSet) ji_wf_Γ eq_refl). Qed.

Lemma ji_idA_ty : ji_Σ ;;; ji_Γ |- ji_idA : si_P.
Proof.
  have h1 := ji_wf_A ji_Σ _ ji_wf_Γ.
  unfold ji_idA. refine (type_App _ _ _ si_na si_P si_P _ (tRel 1) _ _ ji_A_ty).
  - apply type_Prod; [exact (ji_vass_s ji_Σ _ si_na _ _ (ji_P_ty ji_Σ _ ji_wf_Γ) eq_refl)|exact (ji_P_ty ji_Σ _ h1)].
  - apply type_Lambda; [exact (ji_vass ji_Σ _ si_na _ _ (ji_P_ty ji_Σ _ ji_wf_Γ) eq_refl)|].
    exact (type_Rel _ _ 0 (vass si_na si_P) h1 eq_refl).
Qed.

(** [ji_pargs = [A; X]] instantiates the telescope [(A : Prop) (X : Type@{Set})] of [J@{Set}]. *)
Lemma ji_spine_JAX :
  PCUICSpine.spine_subst ji_Σ ji_Γ ji_pargs [tRel 0; tRel 1] (ind_params ji_mdecl ,,, ind_indices ji_idecl)@[ji_u0].
Proof.
  split.
  - exact ji_wf_Γ.
  - exact ji_wf_ΓΓ.
  - exact (context_subst_ass _ _ _ ji_naX ji_TSet (tRel 0)
             (context_subst_ass [] [] [] si_na si_P (tRel 1) context_subst_nil)).
  - exact (PCUICSubstitution.cons_let_ass _ _ _ _ ji_naX (tRel 0) ji_TSet
             (PCUICSubstitution.cons_let_ass _ _ _ _ si_na (tRel 1) si_P (PCUICSubstitution.emptyslet _ _) ji_A_ty)
             ji_X_ty).
Qed.

(** [J A X] is a proposition. *)
Lemma ji_JAX_ty : ji_Σ ;;; ji_Γ |- ji_JAX : tSort sProp.
Proof.
  exact (PCUICInductives.isType_mkApps_Ind (Σ := ji_Σ) (wfΣ := ji_wf) ji_declared_inductive (Γ := ji_Γ)
           ji_cons0 ji_spine_JAX).
Qed.

(** Its spine over the user arity [(ind_type J)@[Set]], which has the redex. *)
Lemma ji_tspine_JAX : PCUICArities.typing_spine ji_Σ ji_Γ (ind_type ji_idecl)@[ji_u0] ji_pargs (tSort sProp).
Proof.
  exact (fst (PCUICInductives.invert_type_mkApps_ind ji_Σ ji_Γ ji_ind ji_u0 ji_pargs (tSort sProp) ji_mdecl
                ji_idecl ji_wf ji_declared_inductive ji_JAX_ty)).
Qed.

(** At [J@{Set}]: the instantiated user arity steps to the instantiated built arity, in any context. *)
Lemma ji_red1_arity_u0 (Γ : context) :
  red1 ji_Σ.1 Γ (ind_type ji_idecl)@[ji_u0]
    (it_mkProd_or_LetIn (ind_params ji_mdecl ,,, ind_indices ji_idecl) (tSort (ind_sort ji_idecl)))@[ji_u0].
Proof.
  change (red1 ji_Σ.1 Γ (tProd si_na si_P (tProd ji_naX ji_TSet ji_redex))
            (tProd si_na si_P (tProd ji_naX ji_TSet (tSort sProp)))).
  apply prod_red_r. apply prod_red_r.
  exact (red_beta _ _ ji_naZ (tSort (Sort.super sProp)) (tRel 0) (tSort sProp)).
Qed.

(** The parameter instances [A] and [(λ Y : Prop. Y) A] of [J@{Set}] and [J@{a}]. *)
Lemma ji_spine_A u : PCUICSpine.spine_subst ji_Σ ji_Γ [tRel 1] [tRel 1] (ind_params ji_mdecl)@[u].
Proof.
  split.
  - exact ji_wf_Γ.
  - exact ji_wf_ΓA.
  - exact (context_subst_ass [] [] [] si_na si_P (tRel 1) context_subst_nil).
  - exact (PCUICSubstitution.cons_let_ass _ _ _ _ si_na (tRel 1) si_P (PCUICSubstitution.emptyslet _ _) ji_A_ty).
Qed.

Lemma ji_spine_idA u : PCUICSpine.spine_subst ji_Σ ji_Γ [ji_idA] [ji_idA] (ind_params ji_mdecl)@[u].
Proof.
  split.
  - exact ji_wf_Γ.
  - exact ji_wf_ΓA.
  - exact (context_subst_ass [] [] [] si_na si_P ji_idA context_subst_nil).
  - exact (PCUICSubstitution.cons_let_ass _ _ _ _ si_na ji_idA si_P (PCUICSubstitution.emptyslet _ _) ji_idA_ty).
Qed.

(** [(λ Y : Prop. Y) A ⇝ A]: the two parameter lists are convertible, by one β step. *)
Lemma ji_red_idA : ji_Σ ;;; ji_Γ ⊢ ji_idA ⇝ tRel 1.
Proof.
  split; [reflexivity|reflexivity|].
  apply red1_red. exact (red_beta _ _ si_na si_P (tRel 0) (tRel 1)).
Qed.

Lemma ji_pars_conv : All2 (PCUICWellScopedCumulativity.ws_cumul_pb Conv ji_Σ ji_Γ) [tRel 1] [ji_idA].
Proof.
  constructor; [|constructor].
  exact (PCUICWellScopedCumulativity.red_ws_cumul_pb_inv (Σ := ji_Σ) (wfΣ := ji_wf) ji_red_idA).
Qed.

(** *** In [ji_Σp]: the facts about the declaration itself *)

Lemma ji_isT_arity : isType ji_Σp [] (ind_type ji_idecl).
Proof. exact (has_sort_isType _ (ji_arity_ty ji_Σp ji_hsp [] localenv_nil)). Qed.

Lemma ji_isT_built :
  isType ji_Σp [] (it_mkProd_or_LetIn (ind_params ji_mdecl)
                     (it_mkProd_or_LetIn (ind_indices ji_idecl) (tSort (ind_sort ji_idecl)))).
Proof. exact (has_sort_isType _ (ji_built_ty ji_Σp ji_hsp [] localenv_nil)). Qed.

(** The user arity steps to the built arity: one β step under the two binders. *)
Lemma ji_red1_arity : red1 ji_Σp.1 [] ji_arity ji_built.
Proof.
  unfold ji_arity, ji_built. apply prod_red_r. apply prod_red_r.
  exact (red_beta _ _ ji_naZ (tSort (Sort.super sProp)) (tRel 0) (tSort sProp)).
Qed.

Lemma ji_red_arity :
  PCUICReduction.red ji_Σp.1 [] (ind_type ji_idecl)
    (it_mkProd_or_LetIn (ind_params ji_mdecl) (it_mkProd_or_LetIn (ind_indices ji_idecl) (tSort (ind_sort ji_idecl)))).
Proof. exact (red1_red _ _ _ _ ji_red1_arity). Qed.

(** The index [X] of the conclusion of [jc] instantiates the index telescope [(X : Type@{i})]. *)
Lemma ji_ci_cindices :
  ctx_inst (typing ji_Σp) (arities_context (ind_bodies ji_mdecl) ,,, ind_params ji_mdecl ,,, cstr_args ji_cdecl)
    (cstr_indices ji_cdecl) (List.rev (lift_context #|cstr_args ji_cdecl| 0 (ind_indices ji_idecl))).
Proof.
  have h1 := ji_wf_A ji_Σp ji_Γi (ji_wf_Γi ji_Σp ji_hsp).
  have h2 := ji_wf_X ji_Σp ji_hsp _ h1.
  cbn. econstructor; [|cbn; constructor].
  exact (type_Rel _ _ 0 (vass ji_naX ji_T) h2 eq_refl).
Qed.

Lemma ji_isT_ctype : isType ji_Σp (arities_context (ind_bodies ji_mdecl)) (cstr_type ji_cdecl).
Proof. exact (has_sort_isType _ (ji_ctype_ty ji_Σp ji_hsp)). Qed.

(** *** A case on [J A X]: predicate [λ (X' : Type@{Set}) (j : J A X'). X'], branch of [jc] *)

Definition ji_ci : case_info := {| ci_ind := ji_ind; ci_npar := 1; ci_relevance := Relevant |}.
Definition ji_p : predicate term :=
  {| pparams := [tRel 1]; puinst := ji_u0; pcontext := ind_predicate_context ji_ind ji_mdecl ji_idecl;
     preturn := tRel 1 |}.
Definition ji_iargs : list term := [tRel 0].
Definition ji_br : branch term := {| bcontext := [vass ji_naX ji_T]; bbody := tRel 0 |}.

Lemma ji_wfpred : wf_predicate ji_mdecl ji_idecl ji_p.
Proof. split; [reflexivity|repeat constructor]. Qed.

Lemma ji_eqctx :
  All2 PCUICEquality.eq_decl_upto_names (pcontext ji_p) (ind_predicate_context ji_ci ji_mdecl ji_idecl).
Proof. cbn. repeat constructor. Qed.

Lemma ji_wfbr : wf_branch ji_cdecl ji_br.
Proof. repeat constructor. Qed.

Lemma ji_isT_case : isType ji_Σ ji_Γ (mkApps (tInd ji_ci (puinst ji_p)) (pparams ji_p ++ ji_iargs)).
Proof. exact (has_sort_isType _ ji_JAX_ty). Qed.

Lemma ji_wf_predctx : wf_local ji_Σ (ji_Γ ,,, case_predicate_context ji_ci ji_mdecl ji_idecl ji_p).
Proof.
  have h := PCUICInductiveInversion.wf_case_predicate_context (Σ := ji_Σ) (wfΣ := ji_wf) (Γ := ji_Γ)
    (ci := ji_ci) (p := ji_p) (args := ji_iargs) ji_declared_inductive ji_isT_case ji_wfpred.
  cbv zeta in h. exact h.
Qed.

(** The return type [X'] (the predicate's own index, [tRel 1]) has sort [Type@{Set}]. *)
Lemma ji_ret_ty :
  ji_Σ ;;; ji_Γ ,,, case_predicate_context ji_ci ji_mdecl ji_idecl ji_p |- preturn ji_p : tSort Sort.type0.
Proof. have h := type_Rel _ _ 1 _ ji_wf_predctx eq_refl. exact h. Qed.
