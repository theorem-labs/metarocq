(** * Template instances of the environment condition

    Concrete Template environments that REGISTER a primitive operation, each with
    a proof that it is well formed under Template's three-part [Typing.wf]
    (universes × [Retroknowledge.wf_retro] × declarations, every declaration
    with its [on_prim_decl] condition).  They transcribe the PCUIC instances of
    [prim_ops_instance.v] into Template's syntax and typing.  They show that the
    premise is satisfiable with a registered operation, for each result shape;
    they say nothing about premises other than [wf], or about the string tag.

    [Σ_po] declares [int : Set] and [land : int -> int -> int], and registers
    [land] as [Int63land] (result shape [SInt]) and [int] as the integer type.

    [Σ_po_bool] declares [int : Set], a one-packet inductive [bool : Set] with
    constructors [true] then [false], and [eqb : int -> int -> bool]; it
    registers [eqb] as [Int63eq] (result shape [SBool]), [int] as the integer
    type and [bool] as [retro_bool].

    The proofs are direct: constructors and computation, no checker run, no
    normalization assumption.

    Beside the primitive libraries' axioms, [Print Assumptions] lists Template's
    [guard_checking : GuardChecker] ([Typing.v]).  It comes from the statement,
    not the proofs: Template's [typing], and so [wf], refers to that axiom, as
    [Print Assumptions Σ_po_wf_statement] below shows for the statement alone. *)

From MetaRocq.Utils Require Import utils.
From Stdlib Require Import ssreflect.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.Template Require Import Ast Typing.

Import ListNotations.

Local Existing Instance default_checker_flags.

Definition po_dp : dirpath := ["prim_ops_instance_template"; "TestSuite"; "MetaRocq"].
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

(** [Set] is a well-formed sort in any environment. *)
Lemma po_wf_sort_type0 (Σ : global_env_ext) : wf_sort Σ Sort.type0.
Proof.
  cbn. intros l hin%LevelExprSet.singleton_spec. subst l. cbn.
  apply global_ext_levels_InSet.
Qed.

Lemma po_int_type (Σ : global_env_ext) : Σ ;;; [] |- tSort Sort.type0 : tSort (Sort.super Sort.type0).
Proof. apply type_Sort; [constructor|apply po_wf_sort_type0]. Qed.

(** [int] has type [Set] in any environment that declares it. *)
Lemma po_int_typed (Σ : global_env_ext) Γ :
  wf_local Σ Γ -> declared_constant Σ.1 po_int_kn po_int_body ->
  Σ ;;; Γ |- tConst po_int_kn [] : tSort Sort.type0.
Proof.
  intros wfΓ hd.
  change (tSort Sort.type0) with (subst_instance [] po_int_body.(cst_type)).
  eapply type_Const; tea. cbn. reflexivity.
Qed.

(** [int] as the domain of a product, in any context of an environment that
    declares it. *)
Lemma po_int_dom (Σ : global_env_ext) Γ :
  declared_constant Σ.1 po_int_kn po_int_body -> wf_local Σ Γ ->
  lift_typing typing Σ Γ (j_vass_s (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0).
Proof.
  intros hd wfΓ. split; [exact tt|]. exists Sort.type0. repeat split.
  now apply po_int_typed.
Qed.

(** [int -> int -> T] is a type when [T], lifted under the two binders, is in
    [Set] in every well-formed context. *)
Lemma po_impl2_typed (Σ : global_env_ext) T :
  declared_constant Σ.1 po_int_kn po_int_body ->
  (forall Γ, wf_local Σ Γ -> Σ ;;; Γ |- lift 1 1 (lift0 1 T) : tSort Sort.type0) ->
  Σ ;;; [] |- tImpl (tConst po_int_kn []) (tImpl (tConst po_int_kn []) T)
    : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  intros hd hT.
  have w1 : wf_local Σ [vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn [])].
  { constructor; [constructor|]. eapply lift_sorting_forget_univ, po_int_dom; tea. constructor. }
  unfold tImpl.
  apply type_Prod; [apply po_int_dom; [exact hd|constructor]|].
  apply type_Prod; [now apply po_int_dom|].
  apply hT. constructor; [exact w1|]. eapply lift_sorting_forget_univ, po_int_dom; tea.
Qed.

Lemma po_land_type_typed :
  (Σ_po_int, Monomorphic_ctx) ;;; [] |- po_land_ty
    : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have hd : declared_constant Σ_po_int po_int_kn po_int_body by now left.
  apply po_impl2_typed; [exact hd|]. intros Γ wfΓ. cbn. now apply po_int_typed.
Qed.

Lemma Σ_po_wf : ∥ wf_ext Σ_po ∥.
Proof.
  constructor. split; [|exact po_udecl_ok].
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
      * exists po_land_ty. split; [reflexivity|]. apply conv_refl'.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

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
  apply type_Sort; [exact wfΓ|apply po_wf_sort_type0].
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
  on_constructor cumul_gen (lift_typing typing) Σ po_bool_mdecl 0 po_bool_body
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
  on_inductive cumul_gen (lift_typing typing) Σ po_bool_kn po_bool_mdecl.
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
  apply po_impl2_typed; [exact hd|]. intros Γ wfΓ. cbn.
  change (tSort Sort.type0) with (subst_instance [] po_bool_body.(ind_type)).
  eapply type_Ind with (mdecl := po_bool_mdecl) (idecl := po_bool_body);
    [exact wfΓ| |cbn; reflexivity].
  split; [now right; left|reflexivity].
Qed.

Lemma Σ_po_bool_wf : ∥ wf_ext Σ_po_bool ∥.
Proof.
  constructor. split; [|exact po_udecl_ok].
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
      * exists po_eqb_ty. split; [reflexivity|]. apply conv_refl'.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_bool_ind, po_bool_mdecl, po_bool_body. split; [reflexivity|].
        split; [now right; left|reflexivity].
Qed.

(** The instances rest on nothing beyond the primitive libraries and the axiom
    their statement already names: no axiom of their own, no admitted lemma. *)
Print Assumptions Σ_po_wf.
Print Assumptions Σ_po_bool_wf.

(** The statement alone already depends on [guard_checking]. *)
Definition Σ_po_wf_statement : Type := wf_ext Σ_po.
Print Assumptions Σ_po_wf_statement.
