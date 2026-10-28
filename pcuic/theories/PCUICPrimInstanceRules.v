(* Distributed under the terms of the MIT license. *)
(** * The premises of the primitive-operation rule, on concrete environments

    On the well-formed environments of [PCUICPrimInstances], this file proves
    concrete instances of the premises that the reduction, weak-head and typing
    theory of primitive operations states:

    - the side condition [prim_op_of Σ c = None] of a bodiless constant, and an
      instance of the section [BelowAxiom] of [PCUICPrimCanonical] built on it;
    - a firing of [red_prim_op], the typing of its redex, and the typing of its
      reduct obtained from [sr_prim_op];
    - a stuck operation application, [whne_primapp_stuck];
    - the typing of that stuck application, and instances of [prim_op_head_type]
      and [prim_app_typing_inv] on it.

    Each instance is proved directly: no checker run, no normalization
    assumption. *)

From Stdlib Require Import ssreflect.
From Corelib Require Import PrimInt63 Uint63Axioms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICReduction
  PCUICNormal PCUICSR PCUICPrimCanonical PCUICPrimitiveRed PCUICWellScopedCumulativity
  PCUICPrimInstances.

Import ListNotations.

Local Existing Instance default_checker_flags.

(** ** Declarations of [Σ_po] *)

(** [land] is declared: the [declared_constant] premise of [red_prim_op],
    [sr_prim_op] and [prim_op_head_type]. *)
Lemma po_land_declared : declared_constant Σ_po0 po_land_kn po_land_body.
Proof. now left. Qed.

(** The integer type of [Σ_po] is declared, has no body, and is not an
    operation: the three premises on [kn] of the section [BelowAxiom]
    ([PCUICPrimCanonical]), also those of [ws_cumul_pb_Axiom_r_inv] and
    [invert_red_axiom]. *)
Lemma po_int_declared : declared_constant Σ_po0 po_int_kn po_int_body.
Proof. now right; left. Qed.

Lemma po_int_bodiless : cst_body po_int_body = None.
Proof. reflexivity. Qed.

Lemma po_int_not_op : prim_op_of Σ_po0 po_int_kn = None.
Proof. reflexivity. Qed.

(** The [wf Σ] premise of the PCUIC lemmas below, from [Σ_po_wf_ext]. *)
Lemma Σ_po_wf_env : wf Σ_po.
Proof. exact Σ_po_wf_ext.1. Qed.

(** [sort_not_below_axiom] of the section [BelowAxiom], instantiated on [Σ_po]
    and its integer type. *)
Lemma Σ_po_sort_not_below_int Γ s u :
  Σ_po ;;; Γ ⊢ tSort s ≤ tConst po_int_kn u -> False.
Proof.
  exact (sort_not_below_axiom (wfΣ := Σ_po_wf_env)
           po_int_declared po_int_bodiless po_int_not_op).
Qed.

(** ** Typing in [Σ_po] *)

(** An integer literal has the integer type ([type_Prim]). *)
Lemma po_lit_int_typed Γ i :
  wf_local Σ_po Γ -> Σ_po ;;; Γ |- term_of_lit (LInt i) : tConst po_int_kn [].
Proof.
  intros wfΓ.
  eapply (type_Prim _ _ (prim_int i) po_int_kn po_int_body).
  - exact wfΓ.
  - reflexivity.
  - exact po_int_declared.
  - now repeat split.
  - constructor.
Qed.

(** [land] applied to two integers is an integer ([type_App], [type_Const]). *)
Lemma po_land_app_typed Γ a b :
  wf_local Σ_po Γ ->
  Σ_po ;;; Γ |- a : tConst po_int_kn [] ->
  Σ_po ;;; Γ |- b : tConst po_int_kn [] ->
  Σ_po ;;; Γ |- mkApps (tConst po_land_kn []) [a; b] : tConst po_int_kn [].
Proof.
  intros wfΓ ha hb.
  set (tI := tConst po_int_kn []).
  set (na := mkBindAnn nAnon rel_of_Type).
  have hdom : forall Δ, wf_local Σ_po Δ -> lift_typing typing Σ_po Δ (j_vass_s na tI Sort.type0).
  { intros Δ wfΔ. split; [exact tt|]. exists Sort.type0. repeat split.
    exact (po_int_typed _ _ wfΔ po_int_declared). }
  have w1 : wf_local Σ_po (Γ ,, vass na tI).
  { constructor; [exact wfΓ|]. eapply lift_sorting_forget_univ, hdom, wfΓ. }
  have w2 : wf_local Σ_po ((Γ ,, vass na tI) ,, vass na tI).
  { constructor; [exact w1|]. eapply lift_sorting_forget_univ, hdom, w1. }
  have hP' : Σ_po ;;; Γ |- tProd na tI tI : tSort (Sort.sort_of_product Sort.type0 Sort.type0).
  { apply type_Prod; [now apply hdom|]. exact (po_int_typed _ _ w1 po_int_declared). }
  have hP : Σ_po ;;; Γ |- tProd na tI (tProd na tI tI)
      : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
  { apply type_Prod; [now apply hdom|].
    apply type_Prod; [now apply hdom|]. exact (po_int_typed _ _ w2 po_int_declared). }
  have hl : Σ_po ;;; Γ |- tConst po_land_kn [] : tProd na tI (tProd na tI tI).
  { refine (type_Const _ _ _ [] po_land_body wfΓ po_land_declared _). cbn. reflexivity. }
  have h1 : Σ_po ;;; Γ |- tApp (tConst po_land_kn []) a : tProd na tI tI
    := type_App _ _ _ na tI (tProd na tI tI) _ a hP hl ha.
  exact (type_App _ _ _ na tI tI _ b hP' h1 hb).
Qed.

(** ** A firing of [red_prim_op] and its subject reduction *)

(** [red_prim_op] fires on [land 1 2] in [Σ_po]: all five premises hold. *)
Lemma Σ_po_fires :
  red1 Σ_po0 [] (mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 2%uint63]))
    (tPrim (prim_int (PrimInt63.land 1%uint63 2%uint63))).
Proof.
  eapply (red_prim_op _ _ po_land_kn po_land_body [] Int63land).
  - exact Σ_po_registers.
  - exact po_land_declared.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The redex of [Σ_po_fires] is well typed: the typing premise of [sr_prim_op]. *)
Lemma Σ_po_redex_typed :
  Σ_po ;;; [] |- mkApps (tConst po_land_kn []) (map term_of_lit [LInt 1%uint63; LInt 2%uint63])
    : tConst po_int_kn [].
Proof.
  have w0 : wf_local Σ_po [] by constructor.
  exact (po_land_app_typed [] _ _ w0 (po_lit_int_typed [] _ w0) (po_lit_int_typed [] _ w0)).
Qed.

(** The reduct of [Σ_po_fires] has the redex's type, by [sr_prim_op]. *)
Lemma Σ_po_fires_sr :
  Σ_po ;;; [] |- tPrim (prim_int (PrimInt63.land 1%uint63 2%uint63)) : tConst po_int_kn [].
Proof.
  eapply (sr_prim_op (wfΣ := Σ_po_wf_env) (ls := [LInt 1%uint63; LInt 2%uint63])).
  - exact Σ_po_redex_typed.
  - exact Σ_po_registers.
  - exact po_land_declared.
  - reflexivity.
  - reflexivity.
Qed.

(** ** The same on [Σ_po_bool]: a boolean result *)

(** [eqb] and [int] are declared in [Σ_po_bool], and so is the block [bool]:
    the [declared_constant] premises of [red_prim_op] and [sr_prim_op], and the
    [declared_constant] and [declared_inductive] premises of [type_Prim] and
    [type_Ind]. *)
Lemma po_eqb_declared : declared_constant Σ_po_bool0 po_eqb_kn po_eqb_body.
Proof. now left. Qed.

Lemma po_bool_int_declared : declared_constant Σ_po_bool0 po_int_kn po_int_body.
Proof. now right; left. Qed.

Lemma po_bool_declared : declared_inductive Σ_po_bool0 po_bool_ind po_bool_mdecl po_bool_body.
Proof. split; [now right; right; left|reflexivity]. Qed.

(** The [wf Σ] premise of [sr_prim_op], from [Σ_po_bool_wf_ext]. *)
Lemma Σ_po_bool_wf_env : wf Σ_po_bool.
Proof. exact Σ_po_bool_wf_ext.1. Qed.

(** An integer literal has the integer type in [Σ_po_bool] ([type_Prim]). *)
Lemma po_bool_lit_int_typed Γ i :
  wf_local Σ_po_bool Γ -> Σ_po_bool ;;; Γ |- term_of_lit (LInt i) : tConst po_int_kn [].
Proof.
  intros wfΓ.
  eapply (type_Prim _ _ (prim_int i) po_int_kn po_int_body).
  - exact wfΓ.
  - reflexivity.
  - exact po_bool_int_declared.
  - now repeat split.
  - constructor.
Qed.

(** [eqb] applied to two integers is a boolean ([type_App], [type_Const]). *)
Lemma po_eqb_app_typed Γ a b :
  wf_local Σ_po_bool Γ ->
  Σ_po_bool ;;; Γ |- a : tConst po_int_kn [] ->
  Σ_po_bool ;;; Γ |- b : tConst po_int_kn [] ->
  Σ_po_bool ;;; Γ |- mkApps (tConst po_eqb_kn []) [a; b] : tInd po_bool_ind [].
Proof.
  intros wfΓ ha hb.
  set (tI := tConst po_int_kn []).
  set (tB := tInd po_bool_ind []).
  set (na := mkBindAnn nAnon rel_of_Type).
  have hB : forall Δ, wf_local Σ_po_bool Δ -> Σ_po_bool ;;; Δ |- tB : tSort Sort.type0.
  { intros Δ wfΔ. change (tSort Sort.type0) with (po_bool_body.(ind_type)@[[]]).
    eapply type_Ind; [exact wfΔ|exact po_bool_declared|cbn; reflexivity]. }
  have hdom : forall Δ, wf_local Σ_po_bool Δ ->
      lift_typing typing Σ_po_bool Δ (j_vass_s na tI Sort.type0).
  { intros Δ wfΔ. split; [exact tt|]. exists Sort.type0. repeat split.
    exact (po_int_typed _ _ wfΔ po_bool_int_declared). }
  have w1 : wf_local Σ_po_bool (Γ ,, vass na tI).
  { constructor; [exact wfΓ|]. eapply lift_sorting_forget_univ, hdom, wfΓ. }
  have w2 : wf_local Σ_po_bool ((Γ ,, vass na tI) ,, vass na tI).
  { constructor; [exact w1|]. eapply lift_sorting_forget_univ, hdom, w1. }
  have hP' : Σ_po_bool ;;; Γ |- tProd na tI tB : tSort (Sort.sort_of_product Sort.type0 Sort.type0).
  { apply type_Prod; [now apply hdom|]. exact (hB _ w1). }
  have hP : Σ_po_bool ;;; Γ |- tProd na tI (tProd na tI tB)
      : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
  { apply type_Prod; [now apply hdom|].
    apply type_Prod; [now apply hdom|]. exact (hB _ w2). }
  have hl : Σ_po_bool ;;; Γ |- tConst po_eqb_kn [] : tProd na tI (tProd na tI tB).
  { refine (type_Const _ _ _ [] po_eqb_body wfΓ po_eqb_declared _). cbn. reflexivity. }
  have h1 : Σ_po_bool ;;; Γ |- tApp (tConst po_eqb_kn []) a : tProd na tI tB
    := type_App _ _ _ na tI (tProd na tI tB) _ a hP hl ha.
  exact (type_App _ _ _ na tI tB _ b hP' h1 hb).
Qed.

(** [red_prim_op] fires on [eqb 1 1] in [Σ_po_bool]; the [SBool] readback is
    constructor 0 ([true]) of the registered [bool]. *)
Lemma Σ_po_bool_fires :
  red1 Σ_po_bool0 [] (mkApps (tConst po_eqb_kn []) (map term_of_lit [LInt 1%uint63; LInt 1%uint63]))
    (tConstruct po_bool_ind 0 []).
Proof.
  eapply (red_prim_op _ _ po_eqb_kn po_eqb_body [] Int63eq).
  - exact Σ_po_bool_registers.
  - exact po_eqb_declared.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The redex of [Σ_po_bool_fires] is well typed: the typing premise of
    [sr_prim_op]. *)
Lemma Σ_po_bool_redex_typed :
  Σ_po_bool ;;; [] |- mkApps (tConst po_eqb_kn []) (map term_of_lit [LInt 1%uint63; LInt 1%uint63])
    : tInd po_bool_ind [].
Proof.
  have w0 : wf_local Σ_po_bool [] by constructor.
  exact (po_eqb_app_typed [] _ _ w0 (po_bool_lit_int_typed [] _ w0) (po_bool_lit_int_typed [] _ w0)).
Qed.

(** The reduct of [Σ_po_bool_fires] has the redex's type, by [sr_prim_op]. *)
Lemma Σ_po_bool_fires_sr :
  Σ_po_bool ;;; [] |- tConstruct po_bool_ind 0 [] : tInd po_bool_ind [].
Proof.
  eapply (sr_prim_op (wfΣ := Σ_po_bool_wf_env) (ls := [LInt 1%uint63; LInt 1%uint63])).
  - exact Σ_po_bool_redex_typed.
  - exact Σ_po_bool_registers.
  - exact po_eqb_declared.
  - reflexivity.
  - reflexivity.
Qed.

(** ** A stuck operation application *)

(** Two integer variables; [tRel 0] is [x]. *)
Definition Γ_po : context :=
  [vass (mkBindAnn (nNamed "x") Relevant) (tConst po_int_kn []);
   vass (mkBindAnn (nNamed "y") Relevant) (tConst po_int_kn [])].

(** [Γ_po] is well formed: the [wf_local] premise of [prim_op_head_type]. *)
Lemma Γ_po_wf : wf_local Σ_po Γ_po.
Proof.
  have hv : forall (Δ : context) (x : name), wf_local Σ_po Δ ->
      lift_typing typing Σ_po Δ (j_vass (mkBindAnn x Relevant) (tConst po_int_kn [])).
  { intros Δ x wfΔ. split; [exact tt|]. exists Sort.type0. repeat split.
    exact (po_int_typed _ _ wfΔ po_int_declared). }
  have w1 : wf_local Σ_po [vass (mkBindAnn (nNamed "y") Relevant) (tConst po_int_kn [])].
  { constructor; [constructor|]. apply hv. constructor. }
  constructor; [exact w1|]. now apply hv.
Qed.

(** [land x y] is neutral, by [whne_primapp_stuck] with no literal before the
    blocking argument [x]. *)
Lemma Σ_po_stuck :
  whne RedFlags.default Σ_po0 Γ_po (mkApps (tConst po_land_kn []) [tRel 0; tRel 1]).
Proof.
  eapply (whne_primapp_stuck _ _ _ po_land_kn [] po_land_body Int63land [] (tRel 0) [tRel 1]).
  - reflexivity.
  - reflexivity.
  - exact Σ_po_registers.
  - reflexivity.
  - apply whne_rel. reflexivity.
Qed.

(** The stuck application [land x y] is well typed. *)
Lemma Σ_po_stuck_typed :
  Σ_po ;;; Γ_po |- mkApps (tConst po_land_kn []) [tRel 0; tRel 1] : tConst po_int_kn [].
Proof.
  apply po_land_app_typed; [exact Γ_po_wf| |].
  - exact (type_Rel _ _ 0 _ Γ_po_wf eq_refl).
  - exact (type_Rel _ _ 1 _ Γ_po_wf eq_refl).
Qed.

(** [prim_op_head_type] on the head [land] of [Σ_po], at its own declared type:
    the cumulativity premise holds by reflexivity. *)
Lemma Σ_po_land_head_type :
  ∑ res Tp,
    [× PCUICPrimOpType.prim_shape_type (retroknowledge Σ_po0) (po_shape (info Int63land)) = Some res,
       PCUICPrimOpType.prim_arg_types (retroknowledge Σ_po0) (po_args (info Int63land)) res = Some Tp,
       Σ_po ;;; Γ_po ⊢ Tp ≤ po_land_ty,
       on_prim_op_result Σ_po (po_shape (info Int63land)) &
       All (prim_op_tag_declared Σ_po) (po_args (info Int63land))].
Proof.
  eapply (prim_op_head_type (wfΣ := Σ_po_wf_env) (Γ := Γ_po) (c := po_land_kn) (u := [])
            (decl := po_land_body) (op := Int63land) (A := po_land_ty)).
  - exact Γ_po_wf.
  - exact po_land_declared.
  - cbn. reflexivity.
  - exact Σ_po_registers.
  - apply ws_cumul_pb_refl; reflexivity.
Qed.

(** [prim_app_typing_inv] applied to [Σ_po_stuck_typed]. *)
Lemma Σ_po_stuck_typing_inv :
  (forall i a tag, nth_error [tRel 0; tRel 1] i = Some a ->
     nth_error (po_args (info Int63land)) i = Some tag ->
     ∑ kn, (primitive_constant Σ_po tag = Some kn) × (Σ_po ;;; Γ_po |- a : tConst kn [])) ×
  (#|[tRel 0; tRel 1]| < arity Int63land ->
     ∑ na A B, Σ_po ;;; Γ_po ⊢ tProd na A B ≤ tConst po_int_kn []).
Proof.
  exact (prim_app_typing_inv (wfΣ := Σ_po_wf_env) Σ_po_registers Σ_po_stuck_typed (le_n 2)).
Qed.
