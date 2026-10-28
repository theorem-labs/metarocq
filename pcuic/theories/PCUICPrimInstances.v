(* Distributed under the terms of the MIT license. *)
(** * Concrete well-formed environments that register primitive operations

    Each environment below registers a primitive operation and has a direct
    proof that it is well formed under the three-part [wf] (universes ×
    [Retroknowledge.wf_retro] × declarations): no checker run, no normalization
    assumption.  [wf] and [on_prim_decl] are stated in the functor
    [EnvironmentTyping.GlobalMaps], which cannot hold a concrete instance, so the
    PCUIC instances live here.  They show that the PCUIC [wf] premise, with its
    [wf_retro] and [on_prim_decl_d] parts, is satisfiable by an environment in
    which an operation is registered:

    - [Σ_po]: the integer type [int : Set] and [land : int -> int -> int],
      registered as [Int63land].  Result shape [SInt].
    - [Σ_po_bool]: [int], a one-packet [bool : Set] with constructors [true]
      then [false], and [eqb : int -> int -> bool], registered as [Int63eq], with
      [bool] as [retro_bool].  Result shape [SBool]: the [on_prim_bool_decl]
      clause and the boolean [on_prim_op_result] clause.
    - [Σ_po_str]: the string type [str : Set] (registered as [retro_string]),
      [int], [len : str -> int] registered as [Stringlength] and
      [get : str -> int -> int] registered as [Stringget].  Argument tag
      [primString], result shape [SInt].

    They cover PCUIC only, not Template, and only the premises named here and
    in [PCUICPrimInstanceRules] (which instantiates the reduction, weak-head and
    typing premises on these environments). *)

From MetaRocq.Utils Require Import utils.
From Stdlib Require Import ssreflect.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICCumulativitySpec
  PCUICWfUniverses PCUICArityRed.

Import ListNotations.

Local Existing Instance default_checker_flags.

Definition po_dp : dirpath := ["PCUICPrimInstances"; "PCUIC"; "MetaRocq"].
Definition po_int_kn : kername := (MPfile po_dp, "int").
Definition po_land_kn : kername := (MPfile po_dp, "land").

Definition po_int_body : constant_body :=
  {| cst_type := tSort Sort.type0; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_land_ty : term :=
  tImpl (tConst po_int_kn []) (tImpl (tConst po_int_kn []) (tConst po_int_kn [])).

Definition po_land_body : constant_body :=
  {| cst_type := po_land_ty; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_retro : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := Some po_int_kn;
     Retroknowledge.retro_float64 := None;
     Retroknowledge.retro_string := None;
     Retroknowledge.retro_array := None;
     Retroknowledge.retro_ops := [(po_land_kn, Int63land)];
     Retroknowledge.retro_bool := None |}.

Definition po_univs : ContextSet.t := (LevelSet.singleton Level.lzero, ConstraintSet.empty).

Definition Σ_po_int : global_env :=
  {| universes := po_univs; declarations := [(po_int_kn, ConstantDecl po_int_body)];
     retroknowledge := po_retro |}.

Definition Σ_po0 : global_env :=
  {| universes := po_univs;
     declarations := [(po_land_kn, ConstantDecl po_land_body); (po_int_kn, ConstantDecl po_int_body)];
     retroknowledge := po_retro |}.

Definition Σ_po : global_env_ext := (Σ_po0, Monomorphic_ctx).

(** [Σ_po] registers an operation. *)
Lemma Σ_po_registers : prim_op_of Σ_po0 po_land_kn = Some Int63land.
Proof. reflexivity. Qed.

Lemma po_univs_ok : on_global_univs po_univs.
Proof.
  repeat split.
  - intros x Hx; cbn in *. inversion Hx.
  - intros x Hx; cbn in *. destruct x; eauto. now inversion Hx.
  - red. unshelve eexists.
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros ? ?. cbn in *. inversion H.
Qed.

Lemma po_udecl_ok : on_udecl po_univs Monomorphic_ctx.
Proof.
  repeat split; cbn.
  - intros i; rewrite LevelSetFact.empty_iff //.
  - intros i; rewrite ConstraintSetFact.empty_iff //.
  - red. rewrite /univs_ext_constraints /=. unshelve eexists.
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros c hc.
      apply ConstraintSetFact.union_iff in hc as [hc|hc]; inversion hc.
  - apply consistent_extension_on_empty.
Qed.

Lemma po_retro_wf : Retroknowledge.wf_retro po_retro.
Proof.
  constructor; cbn.
  - constructor; [intros []|constructor].
  - intros c [<-|[]] h; cbn in h.
    repeat destruct h as [h|h]; try discriminate; try contradiction.
  - unfold Retroknowledge.types_distinct, Retroknowledge.disjoint_opt; cbn;
      repeat split; intros c H1 H2; discriminate.
  - intros i [=].
Qed.

Lemma po_int_type (Σ : global_env_ext) : Σ ;;; [] |- tSort Sort.type0 : tSort (Sort.super Sort.type0).
Proof. apply type_Sort; [constructor|apply wf_sort_type0]. Qed.

(** [int] has type [Set] in any environment that declares it. *)
Lemma po_int_typed (Σ : global_env_ext) Γ :
  wf_local Σ Γ -> declared_constant Σ po_int_kn po_int_body ->
  Σ ;;; Γ |- tConst po_int_kn [] : tSort Sort.type0.
Proof.
  intros wfΓ hd.
  change (tSort Sort.type0) with (po_int_body.(cst_type)@[[]]).
  eapply type_Const; tea. cbn. reflexivity.
Qed.

Lemma po_land_type_typed :
  (Σ_po_int, Monomorphic_ctx) ;;; [] |- po_land_ty
    : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have hd : declared_constant Σ_po_int po_int_kn po_int_body by now left.
  have hdom : forall Γ, wf_local (Σ_po_int, Monomorphic_ctx) Γ ->
      lift_typing typing (Σ_po_int, Monomorphic_ctx) Γ
        (j_vass_s (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0).
  { intros Γ wfΓ. split; [exact tt|]. exists Sort.type0. repeat split.
    now apply po_int_typed. }
  have w1 : wf_local (Σ_po_int, Monomorphic_ctx) [vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn [])].
  { constructor; [constructor|]. eapply lift_sorting_forget_univ, hdom. constructor. }
  unfold po_land_ty, tImpl.
  apply type_Prod; [apply hdom; constructor|].
  apply type_Prod; [now apply hdom|].
  apply po_int_typed.
  - constructor; [exact w1|]. eapply lift_sorting_forget_univ, hdom, w1.
  - now left.
Qed.

Lemma Σ_po_wf_ext : wf_ext Σ_po.
Proof.
  split; [|exact po_udecl_ok].
  split; [exact po_univs_ok|]. split; [exact po_retro_wf|].
  cbn. constructor.
  - constructor; [constructor|].
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_land_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_land_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

Lemma Σ_po_wf : ∥ wf_ext Σ_po ∥.
Proof. exact (sq Σ_po_wf_ext). Qed.

(** ** The boolean instance *)

Definition po_bool_kn : kername := (MPfile po_dp, "bool").
Definition po_eqb_kn : kername := (MPfile po_dp, "eqb").
Definition po_bool_ind : inductive := {| inductive_mind := po_bool_kn; inductive_ind := 0 |}.

(** A constructor of [bool]: no argument, no index, type [tRel 0] (the block's
    only inductive, in the arities context). *)
Definition po_bool_ctor (na : ident) : constructor_body :=
  {| cstr_name := na; cstr_args := []; cstr_indices := []; cstr_type := tRel 0;
     cstr_arity := 0 |}.

Definition po_bool_body : one_inductive_body :=
  {| ind_name := "bool"; ind_indices := []; ind_sort := Sort.type0;
     ind_type := tSort Sort.type0; ind_kelim := IntoAny;
     ind_ctors := [po_bool_ctor "true"; po_bool_ctor "false"];
     ind_projs := []; ind_relevance := Relevant |}.

Definition po_bool_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 0; ind_params := [];
     ind_bodies := [po_bool_body]; ind_universes := Monomorphic_ctx;
     ind_variance := None |}.

Definition po_eqb_ty : term :=
  tImpl (tConst po_int_kn []) (tImpl (tConst po_int_kn []) (tInd po_bool_ind [])).

Definition po_eqb_body : constant_body :=
  {| cst_type := po_eqb_ty; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_bool_retro : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := Some po_int_kn;
     Retroknowledge.retro_float64 := None;
     Retroknowledge.retro_string := None;
     Retroknowledge.retro_array := None;
     Retroknowledge.retro_ops := [(po_eqb_kn, Int63eq)];
     Retroknowledge.retro_bool := Some po_bool_ind |}.

(** The prefix [eqb] is checked against: [int] and [bool]. *)
Definition Σ_po_bool_pre : global_env :=
  {| universes := po_univs;
     declarations := [(po_int_kn, ConstantDecl po_int_body);
                      (po_bool_kn, InductiveDecl po_bool_mdecl)];
     retroknowledge := po_bool_retro |}.

Definition Σ_po_bool0 : global_env :=
  {| universes := po_univs;
     declarations := [(po_eqb_kn, ConstantDecl po_eqb_body);
                      (po_int_kn, ConstantDecl po_int_body);
                      (po_bool_kn, InductiveDecl po_bool_mdecl)];
     retroknowledge := po_bool_retro |}.

Definition Σ_po_bool : global_env_ext := (Σ_po_bool0, Monomorphic_ctx).

(** [Σ_po_bool] registers an operation with a boolean result. *)
Lemma Σ_po_bool_registers : prim_op_of Σ_po_bool0 po_eqb_kn = Some Int63eq.
Proof. reflexivity. Qed.

Lemma po_bool_retro_wf : Retroknowledge.wf_retro po_bool_retro.
Proof.
  constructor; cbn.
  - constructor; [intros []|constructor].
  - intros c [<-|[]] h; cbn in h.
    repeat destruct h as [h|h]; try discriminate; try contradiction.
  - unfold Retroknowledge.types_distinct, Retroknowledge.disjoint_opt; cbn;
      repeat split; intros c H1 H2; discriminate.
  - intros i [= <-]. reflexivity.
Qed.

(** [Set] is a relevant type in any well-formed context. *)
Lemma po_set_isType (Σ : global_env_ext) Γ :
  wf_local Σ Γ -> lift_typing typing Σ Γ (TypRel (tSort Sort.type0) Relevant).
Proof.
  intros wfΓ. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split.
  apply type_Sort; [exact wfΓ|apply wf_sort_type0].
Qed.

(** The arities context of the block: [bool : Set]. *)
Lemma po_bool_arities_wf (Σ : global_env_ext) :
  wf_local Σ (arities_context po_bool_mdecl.(ind_bodies)).
Proof.
  cbn. constructor; [constructor|]. apply po_set_isType. constructor.
Qed.

(** Each constructor's type [tRel 0] is a relevant type in the arities context. *)
Lemma po_bool_ctor_isType (Σ : global_env_ext) :
  lift_typing typing Σ (arities_context po_bool_mdecl.(ind_bodies)) (TypRel (tRel 0) Relevant).
Proof.
  split; [exact tt|]. exists Sort.type0. split; [|repeat split].
  have h := type_Rel Σ (arities_context po_bool_mdecl.(ind_bodies)) 0 _
    (po_bool_arities_wf Σ) eq_refl.
  exact h.
Qed.

Lemma po_bool_ctor_ok (Σ : global_env_ext) na :
  on_constructor cumulSpec0 (lift_typing typing) Σ po_bool_mdecl 0 po_bool_body
    po_bool_body.(ind_indices) (po_bool_ctor na) [].
Proof.
  constructor; cbn.
  - reflexivity.
  - reflexivity.
  - apply po_bool_ctor_isType.
  - exact tt.
  - constructor.
  - change (tRel 0) with (mkApps (tRel 0) []). constructor. constructor.
  - intros v [=].
  - exact I.
Qed.

Lemma po_bool_inductive_ok (Σ : global_env_ext) :
  on_inductive cumulSpec0 (lift_typing typing) Σ po_bool_kn po_bool_mdecl.
Proof.
  constructor; cbn.
  - constructor; [|constructor].
    econstructor 1 with (ind_cunivs := [[]; []]); cbn.
    + exists (tSort Sort.type0). split; [reflexivity|].
      apply arity_red_sort, whd_stop. reflexivity.
    + apply po_set_isType. constructor.
    + apply po_set_isType. constructor.
    + constructor; [apply po_bool_ctor_ok|].
      constructor; [apply po_bool_ctor_ok|constructor].
    + exact I.
    + split; [repeat constructor|exact I].
    + reflexivity.
    + exact I.
  - constructor.
  - reflexivity.
  - reflexivity.
Qed.

Lemma po_eqb_type_typed :
  (Σ_po_bool_pre, Monomorphic_ctx) ;;; [] |- po_eqb_ty
    : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have hd : declared_constant Σ_po_bool_pre po_int_kn po_int_body by now left.
  have hdom : forall Γ, wf_local (Σ_po_bool_pre, Monomorphic_ctx) Γ ->
      lift_typing typing (Σ_po_bool_pre, Monomorphic_ctx) Γ
        (j_vass_s (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0).
  { intros Γ wfΓ. split; [exact tt|]. exists Sort.type0. repeat split.
    now apply po_int_typed. }
  have w1 : wf_local (Σ_po_bool_pre, Monomorphic_ctx)
              [vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn [])].
  { constructor; [constructor|]. eapply lift_sorting_forget_univ, hdom. constructor. }
  unfold po_eqb_ty, tImpl.
  apply type_Prod; [apply hdom; constructor|].
  apply type_Prod; [now apply hdom|].
  change (tSort Sort.type0) with (po_bool_body.(ind_type)@[[]]).
  eapply type_Ind.
  - constructor; [exact w1|]. eapply lift_sorting_forget_univ, hdom, w1.
  - split; [now right; left|reflexivity].
  - cbn. reflexivity.
Qed.

Lemma Σ_po_bool_wf_ext : wf_ext Σ_po_bool.
Proof.
  split; [|exact po_udecl_ok].
  split; [exact po_univs_ok|]. split; [exact po_bool_retro_wf|].
  cbn. constructor; [constructor; [constructor; [constructor|]|]|].
  - (* bool *)
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + apply po_bool_inductive_ok.
    + cbn. intros i _ _. repeat split.
  - (* int *)
    econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - (* eqb *)
    econstructor.
    + constructor; [intros [=]|constructor; [intros [=]|constructor]].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_eqb_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_eqb_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_bool_ind, po_bool_mdecl, po_bool_body. split; [reflexivity|].
        split; [now right; left|reflexivity].
Qed.

Lemma Σ_po_bool_wf : ∥ wf_ext Σ_po_bool ∥.
Proof. exact (sq Σ_po_bool_wf_ext). Qed.

(** ** The string instance *)

Definition po_str_kn : kername := (MPfile po_dp, "str").
Definition po_str_len_kn : kername := (MPfile po_dp, "len").
Definition po_str_get_kn : kername := (MPfile po_dp, "get").

Definition po_str_body : constant_body :=
  {| cst_type := tSort Sort.type0; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_str_len_ty : term := tImpl (tConst po_str_kn []) (tConst po_int_kn []).

Definition po_str_len_body : constant_body :=
  {| cst_type := po_str_len_ty; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_str_get_ty : term :=
  tImpl (tConst po_str_kn []) (tImpl (tConst po_int_kn []) (tConst po_int_kn [])).

Definition po_str_get_body : constant_body :=
  {| cst_type := po_str_get_ty; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_str_retro : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := Some po_int_kn;
     Retroknowledge.retro_float64 := None;
     Retroknowledge.retro_string := Some po_str_kn;
     Retroknowledge.retro_array := None;
     Retroknowledge.retro_ops := [(po_str_len_kn, Stringlength); (po_str_get_kn, Stringget)];
     Retroknowledge.retro_bool := None |}.

(** The prefix [len] is checked against: [int] and [str]. *)
Definition Σ_po_str_pre_len : global_env :=
  {| universes := po_univs;
     declarations := [(po_int_kn, ConstantDecl po_int_body);
                      (po_str_kn, ConstantDecl po_str_body)];
     retroknowledge := po_str_retro |}.

(** The prefix [get] is checked against: [len], [int] and [str]. *)
Definition Σ_po_str_pre_get : global_env :=
  {| universes := po_univs;
     declarations := [(po_str_len_kn, ConstantDecl po_str_len_body);
                      (po_int_kn, ConstantDecl po_int_body);
                      (po_str_kn, ConstantDecl po_str_body)];
     retroknowledge := po_str_retro |}.

Definition Σ_po_str0 : global_env :=
  {| universes := po_univs;
     declarations := [(po_str_get_kn, ConstantDecl po_str_get_body);
                      (po_str_len_kn, ConstantDecl po_str_len_body);
                      (po_int_kn, ConstantDecl po_int_body);
                      (po_str_kn, ConstantDecl po_str_body)];
     retroknowledge := po_str_retro |}.

Definition Σ_po_str : global_env_ext := (Σ_po_str0, Monomorphic_ctx).

(** [Σ_po_str] registers [len] as [Stringlength] (premise [prim_op_of _ kn = Some op]). *)
Lemma Σ_po_str_registers_len : prim_op_of Σ_po_str0 po_str_len_kn = Some Stringlength.
Proof. reflexivity. Qed.

(** [Σ_po_str] registers [get] as [Stringget] (premise [prim_op_of _ kn = Some op]). *)
Lemma Σ_po_str_registers_get : prim_op_of Σ_po_str0 po_str_get_kn = Some Stringget.
Proof. reflexivity. Qed.

(** The retroknowledge conjunct [Retroknowledge.wf_retro] of [wf]: the two
    operations are distinct, neither is a type constant, and [int] and [str]
    are distinct kernames. *)
Lemma Σ_po_str_retro_wf : Retroknowledge.wf_retro po_str_retro.
Proof.
  constructor; cbn.
  - constructor; [intros [[=]|[]]|constructor; [intros []|constructor]].
  - intros c [<-|[<-|[]]] h; cbn in h.
    all: repeat destruct h as [h|h]; try discriminate; try contradiction.
  - unfold Retroknowledge.types_distinct, Retroknowledge.disjoint_opt; cbn;
      repeat split; intros c H1 H2; first [discriminate|rewrite -H1 in H2; discriminate H2].
  - intros i [=].
Qed.

(** [str] has type [Set] in any environment that declares it. *)
Lemma po_str_typed (Σ : global_env_ext) Γ :
  wf_local Σ Γ -> declared_constant Σ po_str_kn po_str_body ->
  Σ ;;; Γ |- tConst po_str_kn [] : tSort Sort.type0.
Proof.
  intros wfΓ hd.
  change (tSort Sort.type0) with (po_str_body.(cst_type)@[[]]).
  eapply type_Const; tea. cbn. reflexivity.
Qed.

Lemma po_str_dom_str (Σ : global_env_ext) Γ :
  wf_local Σ Γ -> declared_constant Σ po_str_kn po_str_body ->
  lift_typing typing Σ Γ (j_vass_s (mkBindAnn nAnon rel_of_Type) (tConst po_str_kn []) Sort.type0).
Proof.
  intros wfΓ hd. split; [exact tt|]. exists Sort.type0. repeat split.
  now apply po_str_typed.
Qed.

Lemma po_str_dom_int (Σ : global_env_ext) Γ :
  wf_local Σ Γ -> declared_constant Σ po_int_kn po_int_body ->
  lift_typing typing Σ Γ (j_vass_s (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0).
Proof.
  intros wfΓ hd. split; [exact tt|]. exists Sort.type0. repeat split.
  now apply po_int_typed.
Qed.

Lemma po_str_len_type_typed :
  (Σ_po_str_pre_len, Monomorphic_ctx) ;;; [] |- po_str_len_ty
    : tSort (Sort.sort_of_product Sort.type0 Sort.type0).
Proof.
  have hs : declared_constant Σ_po_str_pre_len po_str_kn po_str_body by now right; left.
  have hi : declared_constant Σ_po_str_pre_len po_int_kn po_int_body by now left.
  unfold po_str_len_ty, tImpl.
  apply type_Prod; [now apply po_str_dom_str; [constructor|]|].
  apply po_int_typed; [|exact hi].
  constructor; [constructor|]. eapply lift_sorting_forget_univ, po_str_dom_str; [constructor|exact hs].
Qed.

Lemma po_str_get_type_typed :
  (Σ_po_str_pre_get, Monomorphic_ctx) ;;; [] |- po_str_get_ty
    : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have hs : declared_constant Σ_po_str_pre_get po_str_kn po_str_body by now right; right; left.
  have hi : declared_constant Σ_po_str_pre_get po_int_kn po_int_body by now right; left.
  have w1 : wf_local (Σ_po_str_pre_get, Monomorphic_ctx)
              [vass (mkBindAnn nAnon rel_of_Type) (tConst po_str_kn [])].
  { constructor; [constructor|]. eapply lift_sorting_forget_univ, po_str_dom_str; [constructor|exact hs]. }
  unfold po_str_get_ty, tImpl.
  apply type_Prod; [now apply po_str_dom_str; [constructor|]|].
  apply type_Prod; [now apply po_str_dom_int|].
  apply po_int_typed; [|exact hi].
  constructor; [exact w1|]. eapply lift_sorting_forget_univ, po_str_dom_int; [exact w1|exact hi].
Qed.

(** One [prim_op_tag_declared] goal at a prefix that declares [int] and [str]. *)
Local Ltac po_str_tag :=
  first
    [ exists po_str_kn, po_str_body;
      split; [reflexivity|repeat (first [now left|right])|split; reflexivity]
    | exists po_int_kn, po_int_body;
      split; [reflexivity|repeat (first [now left|right])|split; reflexivity] ].

(** [wf_ext] (universes, [wf_retro], and each declaration's [on_global_decl]
    and [on_prim_decl_d] against its prefix) for the string instance. *)
Lemma Σ_po_str_wf_ext : wf_ext Σ_po_str.
Proof.
  split; [|exact po_udecl_ok].
  split; [exact po_univs_ok|]. split; [exact Σ_po_str_retro_wf|].
  cbn. constructor; [constructor; [constructor; [constructor; [constructor|]|]|]|].
  - (* str *)
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - (* int *)
    econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - (* len *)
    econstructor.
    + constructor; [intros [=]|constructor; [intros [=]|constructor]].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 Sort.type0).
      repeat split. exact po_str_len_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_str_len_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor. all: po_str_tag.
      * po_str_tag.
  - (* get *)
    econstructor.
    + constructor; [intros [=]|constructor; [intros [=]|constructor; [intros [=]|constructor]]].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_str_get_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_str_get_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor. all: po_str_tag.
      * po_str_tag.
Qed.

Lemma Σ_po_str_wf : ∥ wf_ext Σ_po_str ∥.
Proof. exact (sq Σ_po_str_wf_ext). Qed.
