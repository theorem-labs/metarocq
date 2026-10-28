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
      and [prim_app_typing_inv] on it;
    - the premises of [typing_spine_prim_type] (a literal's type admits no
      argument), and the lemma applied to them;
    - a well-typed [tCase] whose discriminee is a stuck operation application:
      the typing premise of [reduced_case_discriminee_whne]
      (safechecker/theories/PCUICSafeConversion.v).

    Each instance is proved directly: no checker run, no normalization
    assumption. *)

From Stdlib Require Import ssreflect.
From Corelib Require Import PrimInt63 Uint63Axioms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICReduction
  PCUICNormal PCUICSR PCUICPrimCanonical PCUICPrimitiveRed PCUICWellScopedCumulativity
  PCUICWfUniverses PCUICPosition PCUICArities PCUICProgress PCUICPrimInstances.
From Equations Require Import Equations.

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

(** ** The premises of [typing_spine_prim_type] *)

(** The tag of an integer literal names [int]: the [primitive_constant] premise
    of [typing_spine_prim_type]. *)
Lemma po_prim_int_constant i :
  primitive_constant Σ_po (prim_val_tag (@prim_int term i)) = Some po_int_kn.
Proof. reflexivity. Qed.

(** [int] meets the invariants of its tag: the [primitive_invariants] premise of
    [typing_spine_prim_type]. *)
Lemma po_prim_int_invariants i :
  primitive_invariants (prim_val_tag (@prim_int term i)) po_int_body.
Proof. now repeat split. Qed.

(** The type of an integer literal is [int]; the empty spine from it to [int]:
    the [typing_spine] premise of [typing_spine_prim_type]. *)
Lemma Σ_po_prim_int_spine i :
  PCUICArities.typing_spine Σ_po [] (prim_type (prim_int i) po_int_kn) [] (tConst po_int_kn []).
Proof.
  have w0 : wf_local Σ_po [] by constructor.
  have hI : isType Σ_po [] (tConst po_int_kn []) :=
    has_sort_isType _ (po_int_typed _ _ w0 po_int_declared).
  rewrite /prim_int; simp prim_type.
  apply PCUICArities.type_spine_nil; [exact hI|exact hI|].
  apply ws_cumul_pb_refl; reflexivity.
Qed.

(** [typing_spine_prim_type] applied to the three premises above, with
    [declared_constant] given by [po_int_declared]. *)
Lemma Σ_po_typing_spine_prim_type (i : PrimInt63.int) : @nil term = [].
Proof.
  exact (typing_spine_prim_type (wfΣ := Σ_po_wf_env) [] (prim_int i) po_int_kn po_int_body [] _
    (po_prim_int_constant i) po_int_declared (po_prim_int_invariants i) (Σ_po_prim_int_spine i)).
Qed.

(** ** A well-typed case on a stuck operation application *)

(** One integer variable [x]. *)
Definition Γ_po_case : context :=
  [vass (mkBindAnn (nNamed "x") Relevant) (tConst po_int_kn [])].

Definition po_case_info : case_info :=
  {| ci_ind := po_bool_ind; ci_npar := 0; ci_relevance := Relevant |}.

(** The constant motive [fun _ : bool => int], over the predicate context that
    the block fixes. *)
Definition po_case_pred : predicate term :=
  {| pparams := []; puinst := [];
     pcontext := ind_predicate_context po_bool_ind po_bool_mdecl po_bool_body;
     preturn := tConst po_int_kn [] |}.

(** One branch per constructor of [bool], each an integer literal. *)
Definition po_case_brs : list (branch term) :=
  [{| bcontext := []; bbody := tPrim (prim_int 0%uint63) |};
   {| bcontext := []; bbody := tPrim (prim_int 1%uint63) |}].

(** The discriminee [eqb x 1]. *)
Definition po_case_discr : term :=
  mkApps (tConst po_eqb_kn []) [tRel 0; tPrim (prim_int 1%uint63)].

Definition po_case_term : term := tCase po_case_info po_case_pred po_case_discr po_case_brs.

Lemma Γ_po_case_wf : wf_local Σ_po_bool Γ_po_case.
Proof.
  have w0 : wf_local Σ_po_bool [] by constructor.
  constructor; [exact w0|]. split; [exact tt|]. exists Sort.type0. repeat split.
  exact (po_int_typed _ _ w0 po_bool_int_declared).
Qed.

(** The discriminee is stuck: [eqb] is saturated and blocked on the variable
    [x] ([whne_primapp_stuck]). *)
Lemma Σ_po_bool_case_discr_stuck :
  whne RedFlags.default Σ_po_bool0 Γ_po_case po_case_discr.
Proof.
  unfold po_case_discr.
  eapply (whne_primapp_stuck _ _ _ po_eqb_kn [] po_eqb_body Int63eq [] (tRel 0)
            [tPrim (prim_int 1%uint63)]).
  - reflexivity.
  - reflexivity.
  - exact Σ_po_bool_registers.
  - reflexivity.
  - apply whne_rel. reflexivity.
Qed.

(** The discriminee has the type [bool]. *)
Lemma Σ_po_bool_case_discr_typed :
  Σ_po_bool ;;; Γ_po_case |- po_case_discr : tInd po_bool_ind [].
Proof.
  unfold po_case_discr.
  apply po_eqb_app_typed; [exact Γ_po_case_wf| |].
  - exact (type_Rel _ _ 0 _ Γ_po_case_wf eq_refl).
  - exact (po_bool_lit_int_typed _ 1%uint63 Γ_po_case_wf).
Qed.

(** The case on the stuck discriminee is well typed ([type_Case]): the premise
    [welltyped Σ Γ (zipc (tCase ci p c brs) π)] of
    [reduced_case_discriminee_whne], with the empty stack. *)
Lemma Σ_po_bool_case_welltyped :
  welltyped Σ_po_bool Γ_po_case (zipc po_case_term []).
Proof.
  set (tI := tConst po_int_kn []).
  set (tB := tInd po_bool_ind []).
  set (nb := mkBindAnn (nNamed "bool") Relevant).
  have wfΓ := Γ_po_case_wf.
  have hB : forall Δ, wf_local Σ_po_bool Δ -> Σ_po_bool ;;; Δ |- tB : tSort Sort.type0.
  { intros Δ wfΔ. change (tSort Sort.type0) with (po_bool_body.(ind_type)@[[]]).
    eapply type_Ind; [exact wfΔ|exact po_bool_declared|cbn; reflexivity]. }
  have hI : forall Δ, wf_local Σ_po_bool Δ -> Σ_po_bool ;;; Δ |- tI : tSort Sort.type0.
  { intros Δ wfΔ. exact (po_int_typed _ _ wfΔ po_bool_int_declared). }
  have hvB : forall Δ, wf_local Σ_po_bool Δ ->
      lift_typing typing Σ_po_bool Δ (j_vass_s nb tB Sort.type0).
  { intros Δ wfΔ. split; [exact tt|]. exists Sort.type0. repeat split. exact (hB _ wfΔ). }
  have wfP : wf_local Σ_po_bool (Γ_po_case ,, vass nb tB).
  { constructor; [exact wfΓ|]. eapply lift_sorting_forget_univ, hvB, wfΓ. }
  (* The constructors of [bool] have type [bool]. *)
  have hctor : forall i na, nth_error po_bool_body.(ind_ctors) i = Some (po_bool_ctor na) ->
      Σ_po_bool ;;; Γ_po_case |- tConstruct po_bool_ind i [] : tB.
  { intros i na hi.
    refine (type_Construct _ _ po_bool_ind i [] po_bool_mdecl po_bool_body (po_bool_ctor na)
              wfΓ _ _).
    - split; [exact po_bool_declared|exact hi].
    - cbn. reflexivity. }
  (* The motive and the branch types [(fun _ : bool => int) c]. *)
  have hlam : Σ_po_bool ;;; Γ_po_case |- tLambda nb tB tI : tProd nb tB (tSort Sort.type0).
  { apply type_Lambda; [eapply lift_sorting_forget_univ, hvB, wfΓ|exact (hI _ wfP)]. }
  have hprod : Σ_po_bool ;;; Γ_po_case |- tProd nb tB (tSort Sort.type0)
      : tSort (Sort.sort_of_product Sort.type0 (Sort.super Sort.type0)).
  { apply type_Prod; [exact (hvB _ wfΓ)|].
    apply type_Sort; [exact wfP|apply wf_sort_type0]. }
  have hbrty : forall i na, nth_error po_bool_body.(ind_ctors) i = Some (po_bool_ctor na) ->
      Σ_po_bool ;;; Γ_po_case |- tApp (tLambda nb tB tI) (tConstruct po_bool_ind i [])
        : tSort Sort.type0.
  { intros i na hi.
    exact (type_App _ _ _ nb tB (tSort Sort.type0) _ _ hprod hlam (hctor i na hi)). }
  (* A literal branch body has the branch type, by beta. *)
  have hbody : forall i na n, nth_error po_bool_body.(ind_ctors) i = Some (po_bool_ctor na) ->
      Σ_po_bool ;;; Γ_po_case |- tPrim (prim_int n)
        : tApp (tLambda nb tB tI) (tConstruct po_bool_ind i []).
  { intros i na n hi.
    eapply type_Cumul; [exact (po_bool_lit_int_typed _ n wfΓ)|exact (hbrty i na hi)|].
    exact (cumul_Sym _ _ _ _ _ (cumul_beta _ _ _ nb tB tI (tConstruct po_bool_ind i []))). }
  eapply iswelltyped. cbn [zipc]. unfold po_case_term.
  eapply (type_Case _ _ po_case_info po_case_pred po_case_discr po_case_brs [] Sort.type0
            po_bool_mdecl po_bool_body).
  - exact po_bool_declared.
  - exact (hI _ wfP).
  - exact Σ_po_bool_case_discr_typed.
  - constructor.
    + reflexivity.
    + cbn. split; [reflexivity|repeat constructor].
    + cbn. reflexivity.
    + exact wfP.
    + cbn. repeat constructor.
    + reflexivity.
    + reflexivity.
    + cbn. constructor.
    + reflexivity.
  - constructor.
    + unfold wf_branches, wf_branch, wf_branch_gen. cbn. repeat constructor.
    + constructor; [|constructor; [|constructor]].
      * split; [cbn; constructor|]. split; [exact wfΓ|].
        split; [exact (hbody 0 "true" 0%uint63 eq_refl)|exact (hbrty 0 "true" eq_refl)].
      * split; [cbn; constructor|]. split; [exact wfΓ|].
        split; [exact (hbody 1 "false" 1%uint63 eq_refl)|exact (hbrty 1 "false" eq_refl)].
Qed.
