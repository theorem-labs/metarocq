(* Distributed under the terms of the MIT license. *)
(** * A satisfying instance for [cumulE_prim_op]

  [cumulE_prim_op] ([PCUICCumulativitySpecEta]) is the copy, in the η
  specification [cumulSpecE0], of base [cumul_prim_op] ([PCUICCumulativitySpec]).
  This file proves a satisfying instance: a concrete primitive conversion that the
  η specification relates, in a well-formed environment that registers the
  operation, so the rule is not vacuous.

  The environment [Σ_po] and its well-formedness proof [Σ_po_wf] are copied from
  [test-suite/prim_ops_instance.v] (the test suite is not a library, so it cannot
  be imported), with [po_dp] renamed. It declares [int : Set] and
  [land : int -> int -> int] and registers [land] as [Int63land]. The instance is
  [land 1 3 ≤sE[Conv] 1]. *)

From MetaRocq.Utils Require Import utils.
From Stdlib Require Import ssreflect PrimInt63.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICCumulativitySpec
  PCUICWfUniverses PCUICArityRed PCUICPrimitiveRed PCUICCumulativitySpecEta.

Import ListNotations.

Local Existing Instance default_checker_flags.

Definition po_dp : dirpath := ["PCUICEtaPrimOpInstance"; "PCUIC"; "MetaRocq"].
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
      * exists po_land_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

(** ** The instance *)

Lemma Σ_po_declared_land : declared_constant Σ_po po_land_kn po_land_body.
Proof. now left. Qed.

Lemma po_land_1_3 :
  prim_op_denote Int63land [LInt 1%uint63; LInt 3%uint63] = Some (RInt 1%uint63).
Proof. vm_compute. reflexivity. Qed.

(** [land 1 3 ≤sE[Conv] 1] in [Σ_po], by [cumulE_prim_op], every premise proved. *)
Lemma cumulE_prim_op_inst :
  Σ_po ;;; [] ⊢ mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 3%uint63])
    ≤sE[Conv] tPrim (prim_int 1%uint63).
Proof.
  exact (cumulE_prim_op Σ_po [] Conv po_land_kn po_land_body [] Int63land
           [LInt 1%uint63; LInt 3%uint63] (RInt 1%uint63) (tPrim (prim_int 1%uint63))
           Σ_po_registers Σ_po_declared_land eq_refl po_land_1_3 eq_refl).
Qed.

(** The same instance at [Cumul]. *)
Lemma cumulE_prim_op_inst_cumul :
  Σ_po ;;; [] ⊢ mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 3%uint63])
    ≤sE[Cumul] tPrim (prim_int 1%uint63).
Proof.
  exact (cumulE_prim_op Σ_po [] Cumul po_land_kn po_land_body [] Int63land
           [LInt 1%uint63; LInt 3%uint63] (RInt 1%uint63) (tPrim (prim_int 1%uint63))
           Σ_po_registers Σ_po_declared_land eq_refl po_land_1_3 eq_refl).
Qed.
