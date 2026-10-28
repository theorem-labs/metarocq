(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, S4: proved instances of the under-applied lemmas (FRAC practice)

  Each lemma of S4 (PCUICCumulativitySpecEtaClosure.v) is applied here to a concrete
  instance with every premise proved, so the premises are shown to be jointly
  satisfiable:

  - [cumulSpecE_ind_underapplied_gen_inst], [cumulSpecE_ind_underapplied_inst];
  - [cumulSpecE_construct_underapplied_gen_inst], [cumulSpecE_construct_underapplied_inst].

  The environment [si_env] declares one inductive with one parameter and one
  constructor, [Inductive I (A : Prop) : Prop := c : I A], and [si_wf] proves it
  well-formed ([wf]). The instances use [Γ := []], [args = args' = []] and the empty
  universe instance on both sides; the arity is 1 for both heads, so both are
  under-applied. C3-side: no confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICArityRed PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICCumulativitySpecEtaClosure.

#[local] Existing Instance default_checker_flags.

(** ** The environment *)

Definition si_kn : kername := (MPfile ["SInst"], "I").
Definition si_ind : inductive := {| inductive_mind := si_kn; inductive_ind := 0 |}.
Definition si_P : term := tSort sProp.
Definition si_na : aname := mkBindAnn nAnon Relevant.
Definition si_params : context := [vass si_na si_P].
Definition si_arity : term := tProd si_na si_P (tSort sProp).

Definition si_cdecl : constructor_body :=
  {| cstr_name := "c"; cstr_args := []; cstr_indices := [];
     cstr_type := tProd si_na si_P (tApp (tRel 1) (tRel 0)); cstr_arity := 0 |}.

Definition si_idecl : one_inductive_body :=
  {| ind_name := "I"; ind_indices := []; ind_sort := sProp; ind_type := si_arity;
     ind_kelim := IntoAny; ind_ctors := [si_cdecl]; ind_projs := []; ind_relevance := Relevant |}.

Definition si_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 1; ind_params := si_params; ind_bodies := [si_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition si_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(si_kn, InductiveDecl si_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition si_Σ : global_env_ext := (si_env, Monomorphic_ctx).

(** The environment the declaration is checked in. *)
Definition si_Σ0 : global_env_ext := (mk_global_env ContextSet.empty [] Retroknowledge.empty, Monomorphic_ctx).

(** ** Typing in [si_Σ0] *)

Lemma si_vass (Γ : context) (na : aname) A s :
  si_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typing si_Σ0 Γ (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma si_vass_s (Γ : context) (na : aname) A s :
  si_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typing si_Σ0 Γ (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma si_P_typed (Γ : context) : wf_local si_Σ0 Γ -> si_Σ0 ;;; Γ |- si_P : tSort (Sort.super sProp).
Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

Lemma si_wf_nil : wf_local si_Σ0 [].
Proof. constructor. Qed.

Lemma si_wf_P (Γ : context) : wf_local si_Σ0 Γ -> wf_local si_Σ0 (Γ ,, vass si_na si_P).
Proof.
  intros h. apply localenv_cons_abs; [exact h|].
  exact (si_vass _ si_na _ _ (si_P_typed Γ h) eq_refl).
Qed.

(** [Π A : Prop. Prop] is a type, in any well-formed context. *)
Lemma si_arity_typed (Γ : context) : wf_local si_Σ0 Γ ->
  si_Σ0 ;;; Γ |- si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply type_Prod.
  - exact (si_vass_s _ si_na _ _ (si_P_typed Γ h) eq_refl).
  - apply type_Sort; [exact (si_wf_P Γ h)|cbn; trivial].
Qed.

Definition si_Γi : context := arities_context [si_idecl].

Lemma si_wf_Γi : wf_local si_Σ0 si_Γi.
Proof.
  apply localenv_cons_abs; [constructor|].
  exact (si_vass _ (mkBindAnn (nNamed "I") rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
Qed.

(** The constructor type [Π A : Prop. I A], in the arities context. *)
Lemma si_ctype_typed :
  si_Σ0 ;;; si_Γi |- cstr_type si_cdecl : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  have w2 := si_wf_P si_Γi si_wf_Γi.
  apply type_Prod.
  - exact (si_vass_s _ si_na _ _ (si_P_typed si_Γi si_wf_Γi) eq_refl).
  - refine (type_App _ _ (tRel 1) si_na si_P (tSort sProp)
              (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0) _ _ _).
    + exact (si_arity_typed _ w2).
    + exact (type_Rel _ _ 1 (vass (mkBindAnn (nNamed "I") rel_of_Type) si_arity) w2 eq_refl).
    + exact (type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl).
Qed.

(** ** The declaration is well-formed *)

Lemma si_on_constructor :
  on_constructor cumulSpec0 (lift_typing typing) si_Σ0 si_mdecl 0 si_idecl [] si_cdecl [].
Proof.
  unshelve econstructor.
  - reflexivity.
  - reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon Relevant) _ _ si_ctype_typed eq_refl).
  - exact tt.
  - constructor.
  - cbn. eapply pos_ass.
    + apply pos_arg_closed. reflexivity.
    + exact (pos_concl _ _ _ [vass si_na si_P] [tRel 0] (All_cons (x := tRel 0) (eq_refl : is_true (closedn 1 (tRel 0))) All_nil)).
  - intros v e. discriminate e.
  - destruct lets_in_constructor_types; [exact I|reflexivity].
Qed.

Lemma si_on_ind_body :
  on_ind_body cumulSpec0 (lift_typing typing) si_Σ0 si_kn si_mdecl 0 si_idecl.
Proof.
  unshelve econstructor.
  - exact [[]].
  - exists (tSort sProp). split; [reflexivity|].
    apply arity_red_sort. apply whd_stop. reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
  - constructor; [exact si_on_constructor|constructor].
  - exact I.
  - reflexivity.
  - reflexivity.
  - exact I.
Qed.

Lemma si_on_inductive : on_inductive cumulSpec0 (lift_typing typing) si_Σ0 si_kn si_mdecl.
Proof.
  constructor.
  - constructor; [exact si_on_ind_body|constructor].
  - exact (si_wf_P [] si_wf_nil).
  - reflexivity.
  - reflexivity.
Qed.

Definition si_val : valuation := {| valuation_mono := fun _ => 1%positive; valuation_poly := fun _ => 0 |}.

Lemma si_on_udecl : on_udecl ContextSet.empty Monomorphic_ctx.
Proof.
  split; [|split; [|split]].
  - intros x Hx. exfalso. eapply LevelSet.empty_spec. exact Hx.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists si_val. intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma si_wf : wf si_env.
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
    + exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - (* trunk's wf: the retroknowledge conjunct, then the declarations *)
    split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact si_on_udecl.
    + exact si_on_inductive.
    + (* on_prim_decl: no boolean type is registered *)
      cbn. intros i h; discriminate h.
Qed.

(** ** The universe premises *)

Lemma si_cumul_Ind_univ pb n : cumul_Ind_univ si_Σ pb si_ind n [] [].
Proof. apply cmp_global_instance_refl; tc. Qed.

Lemma si_cumul_Construct_univ pb n : cumul_Construct_univ si_Σ pb si_ind 0 n [] [].
Proof. apply cmp_global_instance_refl; tc. Qed.

Lemma si_declared_inductive : declared_inductive si_Σ si_ind si_mdecl si_idecl.
Proof. split; [left; reflexivity|reflexivity]. Qed.

Lemma si_declared_constructor : declared_constructor si_Σ (si_ind, 0) si_mdecl si_idecl si_cdecl.
Proof. split; [exact si_declared_inductive|reflexivity]. Qed.

(** ** The four instances *)

Lemma cumulSpecE_ind_underapplied_gen_inst :
  si_Σ ;;; [] ⊢ mkApps (tInd si_ind []) [] ≤sE[Conv] mkApps (tInd si_ind []) [].
Proof.
  exact (cumulSpecE_ind_underapplied_gen si_Σ si_ind [] [] 1 si_wf (si_cumul_Ind_univ Conv 1)
           1 [] [] [] eq_refl eq_refl eq_refl eq_refl eq_refl All2_nil).
Qed.

Lemma cumulSpecE_ind_underapplied_inst :
  si_Σ ;;; [] ⊢ mkApps (tInd si_ind []) [] ≤sE[Cumul] mkApps (tInd si_ind []) [].
Proof.
  exact (cumulSpecE_ind_underapplied si_Σ [] Cumul si_ind si_mdecl si_idecl [] [] [] []
           si_wf si_declared_inductive eq_refl eq_refl eq_refl eq_refl
           (le_n 1) (si_cumul_Ind_univ Conv 1) All2_nil).
Qed.

Lemma cumulSpecE_construct_underapplied_gen_inst :
  si_Σ ;;; [] ⊢ mkApps (tConstruct si_ind 0 []) [] ≤sE[Conv] mkApps (tConstruct si_ind 0 []) [].
Proof.
  exact (cumulSpecE_construct_underapplied_gen si_Σ si_ind 0 [] [] 1 si_wf
           (si_cumul_Construct_univ Conv 1) 1 [] [] [] eq_refl eq_refl eq_refl eq_refl eq_refl All2_nil).
Qed.

Lemma cumulSpecE_construct_underapplied_inst :
  si_Σ ;;; [] ⊢ mkApps (tConstruct si_ind 0 []) [] ≤sE[Cumul] mkApps (tConstruct si_ind 0 []) [].
Proof.
  exact (cumulSpecE_construct_underapplied si_Σ [] Cumul si_ind 0 si_mdecl si_idecl si_cdecl [] [] [] []
           si_wf si_declared_constructor eq_refl eq_refl eq_refl eq_refl
           (le_n 1) (si_cumul_Construct_univ Conv 1) All2_nil).
Qed.
