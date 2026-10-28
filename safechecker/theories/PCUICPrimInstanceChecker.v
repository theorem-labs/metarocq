(* Distributed under the terms of the MIT license. *)
(** * Proved instances of the safe checker's primitive-operation lemmas

    The lemmas of [PCUICSafeChecker] and [PCUICSafeReduce] that handle
    primitive operations take an abstract environment [X_ext], a global
    environment [Σ] related to it by [abstract_env_ext_rel X_ext Σ], and
    side conditions that the checker computes.  Each lemma below applies one of
    them at a concrete abstract environment built from the proved well-formed
    environments of [PCUICPrimInstances], with every premise discharged.

    The abstract environment is the canonical (reference) implementation,
    [canonical_abstract_env_impl], with the real guard check
    [real_guard_impl].  For it [abstract_env_ext_rel X Σ] is
    [Σ = reference_impl_env_ext X], so the relation holds by [eq_refl].

    - [X_po]: [Σ_po] ([int] and [land], registered as [Int63land]).
    - [X_po_int]: [(Σ_po_int, Monomorphic_ctx)], the prefix against which
      [land] is checked.
    - [X_po_bool]: [Σ_po_bool] ([int], [bool] and [eqb], registered as
      [Int63eq], with [bool] as [retro_bool]).
    - [X_po_bool_pre]: [(Σ_po_bool_pre, Monomorphic_ctx)], the prefix against
      which [eqb] is checked.

    [check_prim_op_constant] and [check_prim_op_decl] also take a
    [normalization_in] argument, which is not instantiated here; only their
    [wty] and [ond] arguments are, for [land] at [X_po_int]. *)

From MetaRocq.Utils Require Import utils.
From Stdlib Require Import ssreflect.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICCumulativitySpec
  PCUICPrimitiveRed PCUICWellScopedCumulativity PCUICPrimInstances.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICSafeReduce PCUICSafeChecker
  PCUICWfEnvImpl.

Import ListNotations.

Local Existing Instance default_checker_flags.
Local Existing Instance real_guard_impl.

(** ** The prefixes are well formed *)

(** [wf_ext] of the prefix [land] is checked against: the tail of the
    declarations of [Σ_po], with the same universes and retroknowledge. *)
Lemma Σ_po_int_wf_ext : wf_ext (Σ_po_int, Monomorphic_ctx).
Proof.
  destruct Σ_po_wf_ext as [[hu [hr hd]] hud].
  cbn in hd. inversion hd; subst.
  refine ((hu, (hr, _)), hud). assumption.
Qed.

(** [wf_ext] of the prefix [eqb] is checked against: the tail of the
    declarations of [Σ_po_bool]. *)
Lemma Σ_po_bool_pre_wf_ext : wf_ext (Σ_po_bool_pre, Monomorphic_ctx).
Proof.
  destruct Σ_po_bool_wf_ext as [[hu [hr hd]] hud].
  cbn in hd. inversion hd; subst.
  refine ((hu, (hr, _)), hud). assumption.
Qed.

(** ** The concrete abstract environments *)

Definition X_po : reference_impl_ext := build_reference_impl_ext Σ_po Σ_po_wf.

Definition X_po_int : reference_impl_ext :=
  build_reference_impl_ext (Σ_po_int, Monomorphic_ctx) (sq Σ_po_int_wf_ext).

Definition X_po_bool : reference_impl_ext := build_reference_impl_ext Σ_po_bool Σ_po_bool_wf.

Definition X_po_bool_pre : reference_impl_ext :=
  build_reference_impl_ext (Σ_po_bool_pre, Monomorphic_ctx) (sq Σ_po_bool_pre_wf_ext).

Local Abbreviation X_impl := canonical_abstract_env_impl (only parsing).

(** ** Instances of the side-condition lemmas *)

(** [abstract_prim_op_of_spec] at [X_po], [Σ_po]: premise
    [abstract_env_ext_rel X_po Σ_po]. *)
Lemma inst_abstract_prim_op_of_spec kn :
  abstract_prim_op_of X_po kn = prim_op_of Σ_po.1 kn.
Proof. exact (@abstract_prim_op_of_spec _ X_impl X_po Σ_po eq_refl kn). Qed.

(** [abstract_prim_tag_type_spec] at [X_po], [Σ_po]: premise
    [abstract_env_ext_rel X_po Σ_po]. *)
Lemma inst_abstract_prim_tag_type_spec t :
  abstract_prim_tag_type X_impl X_po t = PCUICPrimOpType.prim_tag_type Σ_po.1.(retroknowledge) t.
Proof. exact (abstract_prim_tag_type_spec X_impl X_po Σ_po eq_refl t). Qed.

(** [abstract_prim_op_type_spec] at [X_po], [Σ_po]: premise
    [abstract_env_ext_rel X_po Σ_po]. *)
Lemma inst_abstract_prim_op_type_spec op :
  abstract_prim_op_type X_impl X_po op = PCUICPrimOpType.prim_op_type Σ_po.1.(retroknowledge) op.
Proof. exact (abstract_prim_op_type_spec X_impl X_po Σ_po eq_refl op). Qed.

(** [prim_op_tag_declared_of_lookup] at [X_po_int] for the tag [primInt]:
    premises [abstract_env_ext_rel], [abstract_primitive_constant X_po_int primInt
    = Some po_int_kn], [abstract_env_lookup X_po_int po_int_kn = Some (ConstantDecl
    po_int_body)] and [primitive_invariants primInt po_int_body]. *)
Lemma inst_prim_op_tag_declared_of_lookup :
  prim_op_tag_declared (Σ_po_int, Monomorphic_ctx) primInt.
Proof.
  apply (prim_op_tag_declared_of_lookup X_impl X_po_int (Σ_po_int, Monomorphic_ctx) eq_refl
           primInt po_int_kn po_int_body).
  - reflexivity.
  - reflexivity.
  - split; reflexivity.
Qed.

(** [on_prim_op_result_bool_of_lookup] at [X_po_bool_pre] for [bool]: premises
    [abstract_env_ext_rel], [abstract_primitive_bool X_po_bool_pre = Some po_bool_ind],
    [abstract_env_lookup X_po_bool_pre po_bool_kn = Some (InductiveDecl po_bool_mdecl)]
    and [nth_error (ind_bodies po_bool_mdecl) 0 = Some po_bool_body]. *)
Lemma inst_on_prim_op_result_bool_of_lookup :
  on_prim_op_result (Σ_po_bool_pre, Monomorphic_ctx) SBool.
Proof.
  apply (on_prim_op_result_bool_of_lookup X_impl X_po_bool_pre (Σ_po_bool_pre, Monomorphic_ctx)
           eq_refl po_bool_ind po_bool_mdecl po_bool_body).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The argument tags of [Int63land] are declared at [X_po_int]'s environment. *)
Lemma po_land_args_declared :
  ∥ All (prim_op_tag_declared (Σ_po_int, Monomorphic_ctx)) (po_args (info Int63land)) ∥.
Proof.
  sq. cbn. repeat constructor; exact inst_prim_op_tag_declared_of_lookup.
Qed.

(** [prim_op_type_welltyped] at [X_po_int] for [Int63land] and [T := po_land_ty]:
    premises [abstract_env_ext_rel], [abstract_prim_op_type X_po_int Int63land =
    Some po_land_ty], the argument tags declared and the [SInt] result declared. *)
Lemma inst_prim_op_type_welltyped :
  welltyped (Σ_po_int, Monomorphic_ctx) [] po_land_ty.
Proof.
  apply (prim_op_type_welltyped X_impl X_po_int (Σ_po_int, Monomorphic_ctx) eq_refl
           Int63land po_land_ty).
  - reflexivity.
  - exact po_land_args_declared.
  - sq. exact inst_prim_op_tag_declared_of_lookup.
Qed.

(** [on_prim_op_constant_of_checks] at [X_po_int] for [Int63land], [cb :=
    po_land_body] and [T := po_land_ty]: premises [abstract_env_ext_rel],
    [cst_body = None], [cst_universes = Monomorphic_ctx], [abstract_prim_op_type
    X_po_int Int63land = Some po_land_ty], the tags and result declared and
    [po_land_ty ≤[Conv] po_land_ty]. *)
Lemma inst_on_prim_op_constant_of_checks :
  ∥ on_prim_op_constant cumulSpec0 (Σ_po_int, Monomorphic_ctx) Int63land po_land_body ∥.
Proof.
  apply (on_prim_op_constant_of_checks X_impl X_po_int (Σ_po_int, Monomorphic_ctx) eq_refl
           Int63land po_land_body po_land_ty).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact po_land_args_declared.
  - sq. exact inst_prim_op_tag_declared_of_lookup.
  - sq. apply ws_cumul_pb_refl; reflexivity.
Qed.

(** [on_prim_decl_const_none] at [X_po_int] for [int] (not registered as an
    operation): premises [abstract_env_ext_rel] and [abstract_prim_op_of
    X_po_int po_int_kn = None]. *)
Lemma inst_on_prim_decl_const_none :
  on_prim_decl cumulSpec0 (Σ_po_int, Monomorphic_ctx) po_int_kn (ConstantDecl po_int_body).
Proof.
  apply (on_prim_decl_const_none X_impl X_po_int (Σ_po_int, Monomorphic_ctx) eq_refl
           po_int_kn po_int_body).
  reflexivity.
Qed.

(** [on_prim_decl_const_some] at [X_po_int] for [land] and [Int63land]:
    premises [abstract_env_ext_rel], [abstract_prim_op_of X_po_int po_land_kn =
    Some Int63land] and [on_prim_op_constant] (from
    [inst_on_prim_op_constant_of_checks]). *)
Lemma inst_on_prim_decl_const_some :
  ∥ on_prim_decl cumulSpec0 (Σ_po_int, Monomorphic_ctx) po_land_kn (ConstantDecl po_land_body) ∥.
Proof.
  apply (on_prim_decl_const_some X_impl X_po_int (Σ_po_int, Monomorphic_ctx) eq_refl
           po_land_kn po_land_body Int63land).
  - reflexivity.
  - exact inst_on_prim_op_constant_of_checks.
Qed.

(** [on_prim_decl_ind] at [X_po_bool] for [bool]: premises
    [abstract_env_ext_rel] and, for the registered boolean inductive [i] with
    [inductive_mind i = po_bool_kn], [on_prim_bool_decl po_bool_mdecl] (from the
    checker's test [check_prim_bool_decl], which computes to [true]). *)
Lemma inst_on_prim_decl_ind :
  on_prim_decl cumulSpec0 Σ_po_bool po_bool_kn (InductiveDecl po_bool_mdecl).
Proof.
  apply (on_prim_decl_ind X_impl X_po_bool Σ_po_bool eq_refl po_bool_kn po_bool_mdecl).
  intros i _ _. apply check_prim_bool_decl_spec. reflexivity.
Qed.

(** [abstract_readback_correct] at [X_po_bool], [Σ_po_bool]: premise
    [abstract_env_ext_rel X_po_bool Σ_po_bool]. *)
Lemma inst_abstract_readback_correct s r :
  abstract_readback X_impl X_po_bool s r = readback Σ_po_bool s r.
Proof. exact (abstract_readback_correct X_impl X_po_bool Σ_po_bool eq_refl s r). Qed.

(** ** The [wty] and [ond] arguments of [check_prim_op_constant] and
    [check_prim_op_decl], for [land] at its prefix [X_po_int] *)

(** The [wty] argument of [check_prim_op_constant] at [X_ext := X_po_int] and
    [cb := po_land_body]. *)
Lemma inst_check_prim_op_constant_wty :
  forall Σ, abstract_env_ext_rel X_po_int Σ -> ∥ isType Σ [] po_land_body.(cst_type) ∥.
Proof.
  intros Σ hΣ. change (Σ = (Σ_po_int, Monomorphic_ctx)) in hΣ. subst Σ.
  sq. exact (has_sort_isType _ po_land_type_typed).
Qed.

(** The [ond] argument of [check_prim_op_decl] at [X_ext := X_po_int],
    [kn := po_land_kn] and [d := ConstantDecl po_land_body]: the
    [on_global_decl_d] field of [land]'s entry in [Σ_po_wf_ext]. *)
Lemma inst_check_prim_op_decl_ond :
  forall Σ, abstract_env_ext_rel X_po_int Σ ->
    ∥ on_global_decl cumulSpec0 (lift_typing typing) Σ po_land_kn (ConstantDecl po_land_body) ∥.
Proof.
  intros Σ hΣ. change (Σ = (Σ_po_int, Monomorphic_ctx)) in hΣ. subst Σ.
  destruct Σ_po_wf_ext as [[_ [_ hd]] _].
  cbn in hd. inversion hd as [|? ? ? _ hdata]; subst.
  destruct hdata as [hfresh hudecl hon_udecl hond hprim].
  sq. exact hond.
Qed.
