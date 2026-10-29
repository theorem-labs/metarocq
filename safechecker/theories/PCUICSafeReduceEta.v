(* Distributed under the terms of the MIT license. *)
(** * The reduction machine over an abstract typing (BET-315 eta lane, plan I7 B3 (a))

  The E copy of [PCUICSafeReduce.v] (trunk [0729d50e], equal to [frac/eta] [0cb773a4],
  with prim-ops' [Prim_app] machine). It keeps base [PCUICPosition]'s stack (plan I7
  rev 14 B3: the η stack appears only in [PCUICPositionEta] and the files that import
  it). Every name of the base file is kept.

  The machine is stated over an abstract well-typedness predicate
  [wt : global_env_ext -> context -> term -> Prop] and an abstract environment
  predicate [wfP : global_env_ext -> Type]. The typed facts its code and its proofs use
  are the fields of two classes:
  - [ReduceEnvFacts wt wfP]: closed constant bodies ([ClosedBodies], the premise of the
    untyped reduction metatheory), the scoping of [wt]-typed terms, and the readback
    of a registered primitive operation;
  - [ReduceTypedFacts wt wfP]: subject reduction along [red] ([WtRed],
    [PCUICWfReductionEta]), the inversion of [wt] through a stack, and the inversion
    and classification facts at the typed sites of the machine and of [whnf].
  Termination uses, besides subject reduction, only [NormalizationInWt wt Σ]
  ([PCUICWfReductionEta]); the order [R] is untyped
  ([lanes/eta/k3-reduce-stack-termination.md]).

  Both classes have a proved instance at base [welltyped] and [wf_ext] below
  ([reduce_env_facts_base], [reduce_typed_facts_base]). The E instantiation is
  [PCUICSafeReduceEtaBridge]: [ReduceEnvFacts welltypedE wf_extE] is proved there, and
  [ReduceTypedFacts welltypedE wf_extE] is its one named hypothesis. *)
From Stdlib Require Import RelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICGeneration PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICPosition PCUICNormal
     PCUICInversion PCUICSR PCUICSN
     PCUICUtils PCUICReduction PCUICValidity PCUICSafeLemmata
     PCUICConfluence PCUICConversion
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICClassification PCUICArityRed PCUICPrimitiveRed PCUICPrimCanonical
     PCUICClosedBodies PCUICClosedTyp PCUICTypingEta.

(* The base machine, for the base instance only; not imported. *)
From MetaRocq.SafeChecker Require PCUICSafeReduce.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfReductionEta PCUICWfEnvEta.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations Transparent.
Set Equations With UIP.

(** * Reduction machine for PCUIC without fuel

  We implement the reduction machine of Rocq without relying on fuel.
  Instead we assume strong normalization of the system (for well-typed terms)
  and proceed by well-founded induction.

  Once extracted, this should roughly correspond to the OCaml implementation.

 *)

(* From Program *)
Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : metarocq_scope.

Set Default Goal Selector "!".

Local Set Keyed Unification.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** Filling the [Prim_app] frame: the evaluated arguments, then the argument,
    then the rest of the spine. *)
Lemma mkApps_tApp_app u args v l :
  mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l).
Proof. rewrite mkApps_app. reflexivity. Qed.

(** The position of an argument under the [Prim_app] frame is strictly to the
    right of the head's: [n] application nodes then the argument, against [m > n]
    application nodes down to the head. *)
Lemma positionR_repeat_app_r n m :
  n < m -> positionR (repeat app_l n ++ [app_r]) (repeat app_l m).
Proof.
  induction n in m |- *; intros h; destruct m as [|m]; try lia; cbn.
  - constructor.
  - constructor. apply IHn. lia.
Qed.

(** ** Primitive operations: the readback of a registered operation never fails

    §4.2(b)1, gate 4 ([on_prim_op_result]): in an environment checked by
    [on_global_env] (for ANY conversion and typing, so for [wf] and for [wfE]) the
    readback of a registered operation's result never fails.  This is why the
    machine's readback-[None] branch is unreachable, and why [whd_rel], the machine's
    graph, has no constructor for it (change log 15(a)).  Base [wf_prim_op_readback]
    is the instance at [wf]. *)
Lemma prim_op_readback_on_global_env {cf} {Pcmp P} {Σ : global_env}
  (wfΣ : on_global_env Pcmp P Σ) {c cb op ls r} :
  lookup_env Σ c = Some (ConstantDecl cb) ->
  prim_op_of Σ c = Some op ->
  prim_op_denote op ls = Some r ->
  ∑ v, readback Σ (po_shape (info op)) r = Some v.
Proof.
  intros hl hop hden.
  pose proof (prim_op_denote_shape _ _ _ hden) as hsh.
  destruct (po_shape (info op)) eqn:hshape, r as [i|b]; cbn in hsh |- *; try contradiction.
  - eexists; reflexivity.
  - destruct (lookup_on_global_env_prim wfΣ hl) as (Σ' & [_ _ hretro hpd]).
    cbn in hpd.
    specialize (hpd op (eq_trans (f_equal (fun r => Retroknowledge.prim_op_of r c) hretro) hop)).
    destruct hpd as [_ _ _ _ hres].
    rewrite hshape in hres. cbn in hres.
    destruct hres as (i0 & mdecl & idecl & hb' & _).
    unfold primitive_bool in hb'. rewrite hretro in hb'.
    rewrite hb'. eexists; reflexivity.
Qed.

(** ** The interface: the typed facts the machine uses *)

(** Facts PROVED at base ([reduce_env_facts_base] below) AND at E
    ([PCUICSafeReduceEtaBridge.reduce_env_facts_E]). A [Prop], so extraction erases it. *)
Class ReduceEnvFacts {cf : checker_flags}
  (wt : global_env_ext -> context -> term -> Prop) (wfP : global_env_ext -> Type) : Prop := {
  ref_cb : forall Σ, wfP Σ -> ∥ ClosedBodies Σ ∥;
  ref_closed_context : forall Σ Γ t, wfP Σ -> wt Σ Γ t -> is_closed_context Γ;
  ref_open_term : forall Σ Γ t, wfP Σ -> wt Σ Γ t -> is_open_term Γ t;
  ref_prim_readback : forall Σ c cb op ls r, wfP Σ ->
    lookup_env Σ c = Some (ConstantDecl cb) -> prim_op_of Σ c = Some op ->
    prim_op_denote op ls = Some r -> exists v, readback Σ (po_shape (info op)) r = Some v
}.

(** Facts PROVED at base ([reduce_typed_facts_base] below); at E they are the named
    hypothesis [reduce_factsE] of [PCUICSafeReduceEtaBridge]. The plan row each one
    waits on at [welltypedE] is in the comment after it. A [Prop], so extraction
    erases the hypothesis. *)
Class ReduceTypedFacts {cf : checker_flags}
  (wt : global_env_ext -> context -> term -> Prop) (wfP : global_env_ext -> Type) : Prop := {
  (* subject reduction along [red] (T1) *)
  rtf_wt_red :: WtRed wt wfP;
  (* inversion of the typing through every frame of a stack (T6) *)
  rtf_context : forall Σ Γ (t : term × stack), wfP Σ ->
    wt Σ Γ (zip t) -> wt Σ (Γ ,,, stack_context (snd t)) (fst t);
  (* inversion of a variable (T6) *)
  rtf_rel : forall Σ Γ n, wfP Σ -> wt Σ Γ (tRel n) -> nth_error Γ n <> None;
  (* inversion of a constant (T6) *)
  rtf_const : forall Σ Γ c u, wfP Σ -> wt Σ Γ (tConst c u) ->
    exists decl, declared_constant Σ c decl;
  (* a case on a constructor (T6; base [invert_Case_Construct]) *)
  rtf_case_construct : forall Σ Γ ci p ind' i u brs args, wfP Σ ->
    wt Σ Γ (tCase ci p (mkApps (tConstruct ind' i u) args) brs) ->
    ci.(ci_ind) = ind' /\
    exists br, nth_error brs i = Some br /\
      (#|args| = ci.(ci_npar) + context_assumptions br.(bcontext))%nat;
  (* a projection of a constructor (T6; base [invert_Proj_Construct]) *)
  rtf_proj_construct : forall Σ Γ p i' c u l, wfP Σ ->
    wt Σ Γ (tProj p (mkApps (tConstruct i' c u) l)) ->
    p.(proj_ind) = i' /\ c = 0 /\ (p.(proj_npars) + p.(proj_arg) < #|l|)%nat;
  (* inversion of a cofixpoint (T6) *)
  rtf_cofix : forall Σ Γ mfix idx, wfP Σ -> wt Σ Γ (tCoFix mfix idx) ->
    nth_error mfix idx <> None;
  (* a sort, a product, a primitive value is not applied (T6, classification).
     These four fields conclude [False], so their premise is unsatisfiable by design and
     no concrete instance with a proved premise exists (lane lead's decision,
     2026-10-29). Satisfying instance: [reduce_typed_facts_base] at base [welltyped].
     Not a known-false form: each is a TYPED negative classification (its premise is
     [wt] of the applied term), not a head shape inferred from untyped E-convertibility,
     so it is not the closed-only [conv_witnessE] form that ArityLane's η-expanded-domain
     witness refutes. Over [typingE] the applied head would need a product type up to
     [cumulSpecE]; the E cumulativity does not relate sorts or products to each other
     ([ws_cumul_pbE_Sort_Prod_inv], [ws_cumul_pbE_Prod_Sort_inv], [ws_cumul_pbE_Sort_l_inv],
     [ws_cumul_pbE_Prod_l_inv], [PCUICEtaA6.v:176-316]), and η only adds or removes λs, so
     it relates neither a sort nor a primitive type to a product. *)
  rtf_app_sort : forall Σ Γ s a, wfP Σ -> wt Σ Γ (tApp (tSort s) a) -> False;
  rtf_app_prod : forall Σ Γ na A B a, wfP Σ -> wt Σ Γ (tApp (tProd na A B) a) -> False;
  rtf_app_prim : forall Σ Γ p a, wfP Σ -> wt Σ Γ (tApp (tPrim p) a) -> False;
  (* a registered operation is not applied beyond its arity (T6, prim-ops). Concludes
     [False]; instance and not-known-false argument as for the three fields above: a
     typed negative classification (the saturated application has the operation's
     result type, an inductive or the int type constant, never a product); the E
     cumulativity relates neither to a product ([PCUICEtaA6.v:176-316]). *)
  rtf_prim_overapplied : forall Σ Γ c u op args, wfP Σ ->
    prim_op_of Σ c = Some op -> (arity op < #|args|)%nat ->
    wt Σ Γ (mkApps (tConst c u) args) -> False;
  (* the recursive argument of a fixpoint, the discriminee of a case and of a
     projection, in weak-head normal form and not a constructor, are neutral (T6,
     classification; base [whnf_fix_arg_whne], [whnf_case_arg_whne],
     [whnf_proj_arg_whne]) *)
  rtf_fix_arg_whne : forall flags Σ Γ mfix idx body t before args aftr, wfP Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    wt Σ Γ (mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr)) ->
    ∥ whne flags Σ Γ (mkApps t args) ∥;
  rtf_case_arg_whne : forall flags Σ Γ hd args ci p brs, wfP Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    wt Σ Γ (tCase ci p (mkApps hd args) brs) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥;
  rtf_proj_arg_whne : forall flags Σ Γ hd args p, wfP Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    wt Σ Γ (tProj p (mkApps hd args)) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥;
  (* untyped: a reduct of a weak-head normal form keeps its head (base
     [PCUICNormal.whnf_red_inv] under [wf Σ]; at E it waits for the W-c port of
     PCUICNormal's whnf_red chain to [ClosedBodies]) *)
  rtf_whnf_red_inv : forall Σ Γ t t', wfP Σ ->
    whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> ∥ whnf_red Σ Γ t t' ∥
}.

(** *** The base instances

    [reduce_env_facts_base] and [reduce_typed_facts_base] prove both classes at base
    [welltyped] and [wf_ext], every field from the base lemmas (base
    [PCUICSafeReduce], [PCUICSafeLemmata], [PCUICInductiveInversion], [PCUICNormal]).
    (1) They show that the hypotheses are consistent and that the sections below are
    about something real: the base reduction machine is this file's machine at
    [welltyped]. (2) They do NOT discharge the instantiation at [welltypedE] and
    [wf_extE]: subject reduction over [typingE] (plan row T1), the inversion and
    classification facts over [typingE] (rows T0/T6) and the [ClosedBodies] port of
    [whnf_red_inv] (row W-c) remain hypotheses ([PCUICSafeReduceEtaBridge.reduce_factsE])
    until those rows land. *)
(* Lemmas, not global instances: inside the abstract sections the only instance is the
   section's own, so instance search always picks it. *)
Lemma reduce_env_facts_base {cf : checker_flags} : ReduceEnvFacts welltyped wf_ext.
Proof.
  constructor.
  - intros Σ [wfΣ _]. sq. exact (@wf_ClosedBodies _ Σ wfΣ).
  - intros Σ Γ t [wfΣ _] h. exact (PCUICSafeReduce.welltyped_is_closed_context (wfΣ := wfΣ) h).
  - intros Σ Γ t [wfΣ _] h. exact (PCUICSafeReduce.welltyped_is_open_term (wfΣ := wfΣ) h).
  - intros Σ c cb op ls r [wfΣ _] hl hop hden.
    destruct (prim_op_readback_on_global_env wfΣ hl hop hden) as [v hv]. now exists v.
Qed.

Lemma reduce_typed_facts_base {cf : checker_flags} : ReduceTypedFacts welltyped wf_ext.
Proof.
  constructor.
  - exact wt_red_base.
  - intros Σ Γ t [wfΣ _] h. exact (welltyped_context Σ wfΣ Γ t h).
  - intros Σ Γ n [wfΣ _] [A h] e.
    apply inversion_Rel in h as (decl & _ & e' & _); auto.
    rewrite e' in e. discriminate.
  - intros Σ Γ c u [wfΣ _] [A h].
    apply inversion_Const in h as (decl & _ & d & _); auto.
    now exists decl.
  - intros Σ Γ ci p ind' i u brs args [wfΣ _] [A h].
    exact (PCUICInductiveInversion.invert_Case_Construct Σ (sq wfΣ) h).
  - intros Σ Γ p i' c u l [wfΣ _] [A h].
    exact (PCUICInductiveInversion.invert_Proj_Construct Σ (sq wfΣ) h).
  - intros Σ Γ mfix idx [wfΣ _] [A h] e.
    apply inversion_CoFix in h as (decl & _ & e' & _); auto.
    rewrite e' in e. discriminate.
  - intros Σ Γ s a [wfΣ _] [T h].
    apply inversion_App in h as (na' & A' & B' & hf & hu & hcum); auto.
    apply inversion_Sort in hf as (?&?&?); auto.
    eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv; eauto.
  - intros Σ Γ na A B a [wfΣ _] [T h].
    apply inversion_App in h as (na' & A' & B' & hf & hu & hcum); auto.
    apply inversion_Prod in hf as (?&?&?&?&?); auto.
    eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv; eauto.
  - intros Σ Γ p a [wfΣ _] [T h].
    apply inversion_App in h as (na' & A' & B' & hf & hu & hcum); auto.
    apply inversion_Prim in hf as (prim_ty & cdecl & [? hpc hdecl hinv ? w]); auto.
    pose proof wfΣ as (_ & wfr & _).
    eapply (PCUICConversion.invert_cumul_prim_type_prod (wfΣ := wfΣ) hdecl hinv); [|exact w].
    exact (prim_op_of_primitive_constant Σ _ _ wfr hpc).
  - intros Σ Γ c u op args [wfΣ _] hop hlt h.
    exact (PCUICSafeReduce.prim_app_overapplied_ill_typed (wfΣ := wfΣ) hop hlt h).
  - intros flags Σ Γ mfix idx body t before args aftr [wfΣ _] hu hshape hwh [T h].
    constructor. eapply PCUICSafeReduce.whnf_fix_arg_whne; eassumption.
  - intros flags Σ Γ hd args ci p brs [wfΣ _] hshape hwh [T h].
    constructor. eapply PCUICSafeReduce.whnf_case_arg_whne; eassumption.
  - intros flags Σ Γ hd args p [wfΣ _] hshape hwh [T h].
    constructor. eapply PCUICSafeReduce.whnf_proj_arg_whne; eassumption.
  - intros Σ Γ t t' [wfΣ _] hwh r.
    sq. exact (whnf_red_inv Γ t t' wfΣ hwh r).
Qed.

(** *** The GENUINE part of the interface at [welltypedE]

    [ReduceTypedFactsE] holds the nine fields of [ReduceTypedFacts] that are still
    hypotheses at [wt := welltypedE], [wfP := wf_extE]: each field [rtf_<f>E] is the field
    [rtf_<f>] above with [wt] replaced by [welltypedE] and [wfP] by [wf_extE], nothing
    else changed (the plan row each one waits on is in the comment above it). The other six
    fields ([rtf_rel], [rtf_const], [rtf_cofix], [rtf_app_sort], [rtf_app_prod],
    [rtf_app_prim]) are proved at that instantiation ([PCUICEtaTypedFactsProved]).
    [PCUICSafeReduceEtaBridge.reduce_typed_facts_E] builds [ReduceTypedFacts welltypedE
    wf_extE] from an instance of this class and those six lemmas; the kernel checking that
    construction is the check that each field here is the field above at [welltypedE].
    It is the E sections' named hypothesis ([PCUICSafeReduceEtaBridge.reduce_factsE]).
    A [Prop], so extraction erases it. Satisfying instance: [reduce_typed_facts_base]
    proves the same nine statements at base [welltyped]/[wf_ext]; it shows them consistent
    and does NOT discharge them at [welltypedE] (rows T1, T6, W-c); concrete E instances of
    three of them are in [PCUICSafeReduceEtaBridge] ([rtf_wt_red_inst], [rtf_context_inst],
    [rtf_whnf_red_inv_inst]). *)
Class ReduceTypedFactsE {cf : checker_flags} : Prop := {
  (* subject reduction along [red] (T1) *)
  rtf_wt_redE : WtRed welltypedE wf_extE;
  (* inversion of the typing through every frame of a stack (T6) *)
  rtf_contextE : forall Σ Γ (t : term × stack), wf_extE Σ ->
    welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t);
  (* a case on a constructor (T6; base [invert_Case_Construct]) *)
  rtf_case_constructE : forall Σ Γ ci p ind' i u brs args, wf_extE Σ ->
    welltypedE Σ Γ (tCase ci p (mkApps (tConstruct ind' i u) args) brs) ->
    ci.(ci_ind) = ind' /\
    exists br, nth_error brs i = Some br /\
      (#|args| = ci.(ci_npar) + context_assumptions br.(bcontext))%nat;
  (* a projection of a constructor (T6; base [invert_Proj_Construct]) *)
  rtf_proj_constructE : forall Σ Γ p i' c u l, wf_extE Σ ->
    welltypedE Σ Γ (tProj p (mkApps (tConstruct i' c u) l)) ->
    p.(proj_ind) = i' /\ c = 0 /\ (p.(proj_npars) + p.(proj_arg) < #|l|)%nat;
  (* a registered operation is not applied beyond its arity (T6, prim-ops); argument as for
     [rtf_prim_overapplied] above *)
  rtf_prim_overappliedE : forall Σ Γ c u op args, wf_extE Σ ->
    prim_op_of Σ c = Some op -> (arity op < #|args|)%nat ->
    welltypedE Σ Γ (mkApps (tConst c u) args) -> False;
  (* the recursive argument of a fixpoint, the discriminee of a case and of a
     projection, in weak-head normal form and not a constructor, are neutral (T6,
     classification; base [whnf_fix_arg_whne], [whnf_case_arg_whne],
     [whnf_proj_arg_whne]) *)
  rtf_fix_arg_whneE : forall flags Σ Γ mfix idx body t before args aftr, wf_extE Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    welltypedE Σ Γ (mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr)) ->
    ∥ whne flags Σ Γ (mkApps t args) ∥;
  rtf_case_arg_whneE : forall flags Σ Γ hd args ci p brs, wf_extE Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    welltypedE Σ Γ (tCase ci p (mkApps hd args) brs) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥;
  rtf_proj_arg_whneE : forall flags Σ Γ hd args p, wf_extE Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    welltypedE Σ Γ (tProj p (mkApps hd args)) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥;
  (* untyped: a reduct of a weak-head normal form keeps its head (row W-c) *)
  rtf_whnf_red_invE : forall Σ Γ t t', wf_extE Σ ->
    whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> ∥ whnf_red Σ Γ t t' ∥
}.

(** ** Consequences of the interface, under the names the machine's proofs use *)

Section WtLemmas.
  Context {cf : checker_flags}.
  Context {wt : global_env_ext -> context -> term -> Prop} {wfP : global_env_ext -> Type}.
  Context {EF : ReduceEnvFacts wt wfP} {TF : ReduceTypedFacts wt wfP}.

  Lemma red_wt Σ {Γ u v} : wfP Σ -> wt Σ Γ u -> red (fst Σ) Γ u v -> wt Σ Γ v.
  Proof using TF. intros hΣ h r. exact (wt_red Σ Γ u v hΣ h r). Qed.

  Lemma cored_wt Σ {Γ u v} : wfP Σ -> wt Σ Γ u -> cored Σ Γ v u -> wt Σ Γ v.
  Proof using TF.
    intros hΣ h r. apply cored_red in r as [r]. exact (red_wt Σ hΣ h r).
  Qed.

  Lemma wt_context Σ (hΣ : wfP Σ) Γ (t : term × stack) :
    wt Σ Γ (zip t) -> wt Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof using TF. exact (rtf_context Σ Γ t hΣ). Qed.

  Lemma wt_zipc_zipp Σ (hΣ : wfP Σ) Γ t π :
    wt Σ Γ (zipc t π) -> wt Σ (Γ ,,, stack_context π) (zipp t π).
  Proof using TF.
    intros h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    change (wt Σ Γ (zip (mkApps t l, ρ))) in h.
    apply wt_context in h; [|exact hΣ]. cbn in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.

  Lemma wt_is_closed_context {Σ} {hΣ : wfP Σ} {Γ t} : wt Σ Γ t -> is_closed_context Γ.
  Proof using EF. intros h. exact (ref_closed_context Σ Γ t hΣ h). Qed.

  Lemma wt_is_open_term {Σ} {hΣ : wfP Σ} {Γ t} : wt Σ Γ t -> is_open_term Γ t.
  Proof using EF. intros h. exact (ref_open_term Σ Γ t hΣ h). Qed.

  (** [closed_red_confluence] under [ClosedBodies] *)
  Lemma closed_red_confluence_cb {Σ : global_env_ext} {cb : ClosedBodies Σ} {Γ} {t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v ->
    ∑ v', Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v'.
  Proof using Type.
    intros [clΓ clT r] [clΓ' clT' r'].
    destruct (red_confluence_cb (Γ := exist Γ clΓ) (t := exist t clT) r r') as [v' [redl redr]].
    cbn in *. exists v'. split; constructor; tea.
    - exact (red_is_open_term_cb t u r clΓ clT).
    - exact (red_is_open_term_cb t v r' clΓ clT).
  Qed.

  (** [invert_red_sort] needs no premise on the environment *)
  Lemma invert_red_sort_gen {Σ : global_env_ext} Γ u v :
    Σ ;;; Γ ⊢ (tSort u) ⇝ v -> v = tSort u.
  Proof using Type.
    intros [_ _ H]. remember (tSort u) as x eqn:ex.
    induction H as [x y r|x|x y z H1 IH1 H2 IH2] in ex |- *.
    - subst x. depind r; solve_discr.
    - now subst x.
    - specialize (IH1 ex). subst y. now apply IH2.
  Qed.
End WtLemmas.

#[global] Hint Resolve wt_is_closed_context wt_is_open_term : fvs.


(* We assume normalization of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Measure.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).
  Context (Σ : global_env_ext).

  Definition R_aux Γ :=
    dlexprod (cored Σ Γ) (@posR).

  Definition R Γ u v :=
    R_aux Γ (zip u ; stack_pos (fst u) (snd u))
            (zip v ; stack_pos (fst v) (snd v)).


  Derive Signature for Acc.
  Lemma R_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2),
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; p1) (t2 ; p2).
  Proof using Type.
    intros Γ t1 t2 p1 p2 e h.
    subst. right. assumption.
  Qed.

  Definition Req Γ t t' :=
    t = t' \/ R Γ t t'.

  Lemma Rtrans :
    forall Γ u v w,
      R Γ u v ->
      R Γ v w ->
      R Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2.
    eapply dlexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - eapply posR_trans.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Γ}, Transitive (Req Γ).
  Proof using Type.
    intros Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Γ u v},
      R Γ u v ->
      Req Γ u v.
  Proof using Type.
    intros Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Γ, Reflexive (Req Γ).
  Proof using Type.
    intros Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Γ u v w},
      R Γ u v ->
      Req Γ v w ->
      R Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Measure.

(** The two cases of [R], without the dependent pair: a strict reduction of the
    zipped term, or the same term and a deeper position. *)
Lemma dlexprod_posR_cases {A} {B : A -> Type} (leA : A -> A -> Prop)
  (f : forall x, B x -> position) (p q : sigT B) :
  dlexprod leA (fun x (a b : B x) => positionR (f x a) (f x b)) p q ->
  leA (projT1 p) (projT1 q) \/
  (projT1 p = projT1 q /\ positionR (f _ (projT2 p)) (f _ (projT2 q))).
Proof.
  intros h. destruct h as [x x' y y' h|x y y' h].
  - left. exact h.
  - right. split; [reflexivity|exact h].
Qed.

Lemma R_cases Σ Γ u v : R Σ Γ u v ->
  cored Σ Γ (zip u) (zip v) \/
  (zip u = zip v /\ positionR (stack_position (snd u)) (stack_position (snd v))).
Proof.
  unfold R, R_aux. intros h.
  exact (dlexprod_posR_cases (cored Σ Γ) (fun t (p : pos t) => proj1_sig p) _ _ h).
Qed.

(** A zipped term equal to a variable has the empty stack. *)
Lemma zipc_tRel_inv u ρ n : zipc u ρ = tRel n -> ρ = [] /\ u = tRel n.
Proof.
  induction ρ as [|se ρ ih] in u |- *; cbn; intros e.
  - split; [reflexivity|exact e].
  - destruct (ih _ e) as [-> e']. destruct se; cbn in e'; discriminate.
Qed.

(** A variable bound by an assumption has no [red1] step. *)
Lemma cored_Rel_assum (Σ : global_env) Γ n decl v :
  nth_error Γ n = Some decl -> decl_body decl = None -> cored Σ Γ v (tRel n) -> False.
Proof.
  intros hn hb hc. remember (tRel n) as u eqn:eu.
  induction hc as [u v r|u v w hc ih r] in eu |- *.
  - subst u. depelim r; try solve_discr.
    match goal with H : option_map _ _ = _ |- _ =>
      rewrite hn in H; cbn in H; rewrite hb in H; discriminate H end.
  - exact (ih eu).
Qed.

(* Added by Julien Forest on 13/11/20 in Rocq stdlib, adapted to subset case by M. Sozeau *)
Section Acc_sidecond_generator.
  Context {A : Type} {R : A -> A -> Prop} {P : A -> Prop}.
  Variable Pimpl : forall x y, P x -> R y x -> P y.
  (* *Lazily* add 2^n - 1 Acc_intro on top of wf.
     Needed for fast reductions using Function and Program Fixpoint
     and probably using Fix and Fix_F_2
   *)
  Fixpoint Acc_intro_generator n (acc : forall t, P t -> Acc R t) : forall t, P t -> Acc R t :=
    match n with
        | O => acc
        | S n => fun x Px =>
                   Acc_intro x (fun y Hy => Acc_intro_generator n (Acc_intro_generator n acc) y (Pimpl _ _ Px Hy))
    end.
End Acc_sidecond_generator.
(** We leave it opaque for now, as some simplification tactics
  might otherwise unfold the large Acc proof. Don't forget to make it transparent
  when computing. *)
Opaque Acc_intro_generator.

Section Reduce.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context {wt : global_env_ext -> context -> term -> Prop} {wfP : global_env_ext -> Type}.

  Context {EF : ReduceEnvFacts wt wfP} {TF : ReduceTypedFacts wt wfP}.

  Context (flags : RedFlags.t).

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {hX : AbstractEnvWf X_type X wfP}.

  Context {normalization_in : forall Σ, wfP Σ -> Σ ∼_ext X -> NormalizationInWt wt Σ}.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wfP Σ ∥ := @abstract_env_wfP cf X_type X wfP hX Σ wfΣ.

  Existing Instance Req_refl.

Lemma acc_dlexprod_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
  (forall x, well_founded (leB x)) ->
  forall x,
    Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
    forall y,
      Acc (leB x) y ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
Proof using Type.
intros hw. induction 1 as [x hx ih1].
intros y. induction 1 as [y hy ih2].
constructor.
intros [x' y'] h.
destruct HQ as [[p q]].
specialize (h p q).
simple inversion h.
- intro hA. inversion H0. inversion H1. subst.
  eapply ih1.
  + intros. now eapply (HP _ _ _ _ q).
  + apply hw.
- intro hB. rewrite <- H0.
  pose proof (projT2_eq H1) as p2.
  set (projT1_eq H1) as p1 in *; cbn in p1.
  destruct p1; cbn in p2; destruct p2.
  eapply ih2. assumption.
Qed.

Lemma dlexprod_Acc_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
Proof using Type.
  intros hB x y hA.
  eapply acc_dlexprod_gen ; try assumption.
  apply hB.
Qed.

Definition R_singleton Abs A
  (R : Abs -> A -> A -> Prop) (Q : Abs -> Prop) x (q : Q x)
  (HQ : forall x x' , Q x -> Q x' -> x = x') (a a' : A) :
  R x a a' <-> (forall x, Q x -> R x a a').
Proof using Type.
  split.
  - intros H x' q'.  specialize (HQ x x' q q'). subst; eauto.
  - eauto.
Defined.

Fixpoint Acc_equiv A (R R' : A -> A -> Prop)
  (Heq : forall a a', R a a' <-> R' a a') a
  (HAcc : Acc R a) : Acc R' a.
Proof using Type.
  econstructor. intros. apply Heq in H.
  destruct HAcc. eapply Acc_equiv; eauto.
Defined.

Corollary R_Acc_aux :
    forall Γ t p,
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ t) ->
    (Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R_aux Σ Γ t t') (t ; p)).
  Proof using normalization_in hX.
    intros Γ t p h.
    eapply dlexprod_Acc_gen.
    - apply abstract_env_ext_exists.
    - intros. eapply abstract_env_cored; try apply H1; eauto.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
      destruct (hΣ _ wfΣ).
      eapply Acc_equiv; try
      eapply normalization_in; eauto.
      eapply R_singleton with (Q := abstract_env_ext_rel X)
          (R := fun Σ a a' => cored Σ Γ a a'); eauto.
      intros; eapply abstract_env_ext_irr; eauto.
  Defined.

  Corollary R_Acc :
    forall Γ t,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ (zip t)) ->
      Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ t t') t.
  Proof using normalization_in hX.
    intros Γ t h.
    pose proof (R_Acc_aux _ _ (stack_pos (fst t) (snd t)) h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H0; eauto.
  Qed.



  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition Pr (t' : term * stack) π :=
    snd (decompose_stack π) = snd (decompose_stack (snd t')).

  Notation givePr := (_) (only parsing).

  Definition Pr' (t' : term * stack) :=
    isApp (fst t') = false /\
    (RedFlags.beta flags -> isLambda (fst t') -> isStackApp (snd t') = false).

  Notation givePr' := (conj _ (fun β hl => _)) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist res prf_Σ) := reduce t π smaller in
     exist res (fun Σ wfΣ => let '((conj prf (conj h (conj h1 h2)))) := prf_Σ Σ wfΣ in conj (Req_trans _ _ _ _ _ (R_to_Req _ (smaller Σ wfΣ))) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist (t,π) (fun Σ wfΣ => conj _ (conj givePr givePr'))) (only parsing).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Lemma Req_red Σ :
    forall Γ x y,
      Req Σ Γ y x ->
      ∥ red Σ Γ (zip x) (zip y) ∥.
  Proof using Type.
    intros Γ [t π] [t' π'] h; simpl.
    dependent destruction h.
    - repeat zip fold. rewrite H.
      constructor. reflexivity.
    - dependent destruction H.
      + eapply cored_red. assumption.
      + simpl in H0. inversion H0.
        constructor. reflexivity.
  Qed.


  (* Show Obligation Tactic. *)
  Ltac obTac :=
    (* program_simpl ; *)
    Program.Tactics.program_simplify ;
    Equations.CoreTactics.equations_simpl ;
    try Program.Tactics.program_solve_wf ;
    try reflexivity.

  Obligation Tactic := obTac.

  Equations discr_construct (t : term) : Prop :=
    discr_construct (tConstruct ind n ui) := False ;
    discr_construct _ := True.

  Inductive construct_view : term -> Type :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Equations construct_viewc t : construct_view t :=
    construct_viewc (tConstruct ind n ui) := view_construct ind n ui ;
    construct_viewc t := view_other t I.

  (** [readback] on the abstract environment: the booleans are read through
      [abstract_primitive_bool].  It computes the same term as [readback] on
      every environment the abstract one stands for. *)
  Definition abstract_readback (s : prim_shape) (r : prim_result) : option term :=
    match s, r with
    | SInt, RInt i => Some (tPrim (prim_int i))
    | SBool, RBool b =>
        match abstract_primitive_bool X with
        | Some ind => Some (tConstruct ind (if b then 0 else 1) [])
        | None => None
        end
    | SInt, RBool _ | SBool, RInt _ => None
    end.

  Lemma abstract_readback_correct Σ (wfΣ : abstract_env_ext_rel X Σ) s r :
    abstract_readback s r = readback Σ s r.
  Proof using Type.
    destruct s, r; cbn; try reflexivity.
    rewrite (abstract_primitive_bool_correct X Σ wfΣ). reflexivity.
  Qed.

  (* Tailored view for _reduce_stack *)
  Equations red_discr (t : term) (π : stack) : Prop :=
    red_discr (tRel _) _ := False ;
    red_discr (tLetIn _ _ _ _) _ := False ;
    red_discr (tConst _ _) _ := False ;
    red_discr (tApp _ _) _ := False ;
    red_discr (tLambda _ _ _) (App_l _ :: _) := False ;
    red_discr (tFix _ _) _ := False ;
    red_discr (tCase _ _ _ _) _ := False ;
    red_discr (tProj _ _) _ := False ;
    red_discr _ _ := True.

  Inductive red_view : term -> stack -> Type :=
  | red_view_Rel c π : red_view (tRel c) π
  | red_view_LetIn A b B c π : red_view (tLetIn A b B c) π
  | red_view_Const c u π : red_view (tConst c u) π
  | red_view_App f a π : red_view (tApp f a) π
  | red_view_Lambda na A t a args : red_view (tLambda na A t) (App_l a :: args)
  | red_view_Fix mfix idx π : red_view (tFix mfix idx) π
  | red_view_Case ci p c brs π : red_view (tCase ci p c brs) π
  | red_view_Proj p c π : red_view (tProj p c) π
  | red_view_other t π : red_discr t π -> red_view t π.

  Equations red_viewc t π : red_view t π :=
    red_viewc (tRel c) π := red_view_Rel c π ;
    red_viewc (tLetIn A b B c) π := red_view_LetIn A b B c π ;
    red_viewc (tConst c u) π := red_view_Const c u π ;
    red_viewc (tApp f a) π := red_view_App f a π ;
    red_viewc (tLambda na A t) (App_l a :: args) := red_view_Lambda na A t a args ;
    red_viewc (tFix mfix idx) π := red_view_Fix mfix idx π ;
    red_viewc (tCase ci p c brs) π := red_view_Case ci p c brs π ;
    red_viewc (tProj p c) π := red_view_Proj p c π ;
    red_viewc t π := red_view_other t π I.

  Equations discr_construct_cofix (t : term) : Prop :=
    discr_construct_cofix (tConstruct ind n ui) := False ;
    discr_construct_cofix (tCoFix mfix idx) := False ;
    discr_construct_cofix _ := True.

  Inductive construct_cofix_view : term -> Type :=
  | ccview_construct : forall ind n ui, construct_cofix_view (tConstruct ind n ui)
  | ccview_cofix : forall mfix idx, construct_cofix_view (tCoFix mfix idx)
  | ccview_other : forall t, discr_construct_cofix t -> construct_cofix_view t.

  Equations cc_viewc t : construct_cofix_view t :=
    cc_viewc (tConstruct ind n ui) := ccview_construct ind n ui ;
    cc_viewc (tCoFix mfix idx) := ccview_cofix mfix idx ;
    cc_viewc t := ccview_other t I.

  Equations discr_construct0_cofix (t : term) : Prop :=
    discr_construct0_cofix (tConstruct ind n ui) := n <> 0 ;
    discr_construct0_cofix (tCoFix mfix idx) := False ;
    discr_construct0_cofix _ := True.

  Inductive construct0_cofix_view : term -> Type :=
  | cc0view_construct : forall ind ui, construct0_cofix_view (tConstruct ind 0 ui)
  | cc0view_cofix : forall mfix idx, construct0_cofix_view (tCoFix mfix idx)
  | cc0view_other : forall t, discr_construct0_cofix t -> construct0_cofix_view t.

  Equations cc0_viewc t : construct0_cofix_view t :=
    cc0_viewc (tConstruct ind 0 ui) := cc0view_construct ind ui ;
    cc0_viewc (tCoFix mfix idx) := cc0view_cofix mfix idx ;
    cc0_viewc t := cc0view_other t _.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ (zip (t,π)))
            (reduce : forall t' π', (forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (t',π') (t,π)) ->
                               { t'' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' })
    : { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t,π) /\ Pr t' π /\ Pr' t' } :=

    _reduce_stack Γ t π h reduce with red_viewc t π := {

    | red_view_Rel c π with inspect (nth_error (Γ ,,, stack_context π) c) := {
      | @exist None eq := False_rect _ _ ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := give (tRel c) π ;
        | @exist (Some b) H := rec reduce (lift0 (S c) b) π
        }
      } ;

    | red_view_LetIn A b B c π with RedFlags.zeta flags := {
      | true := rec reduce (subst10 b c) π ;
      | false := give (tLetIn A b B c) π
      } ;

    | red_view_Const c u π with RedFlags.delta flags := {
      | true with inspect (abstract_env_lookup X c) := {
        | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq :=
          let body' := subst_instance u body in
          rec reduce body' π ;
        | @exist (Some (InductiveDecl _)) eq := False_rect _ _ ;
        | @exist None eq := False_rect _ _ ;
        (* A bodiless constant (design §7.2).  An axiom stops the machine; a
           registered operation saturated on the stack evaluates its arguments
           left to right under the [Prim_app] frame, as [red_view_Fix] does its
           recursive argument under [Fix_app], and fires when they are all
           literals.  [whd_rel], the machine's graph, has one constructor per
           leaf below, except the readback-[None] leaf ([False_rect]), which
           [wf_prim_op_readback] makes unreachable. *)
        | @exist (Some (ConstantDecl {| cst_body := None |})) eq
            with inspect (abstract_prim_op_of X c) := {
          | @exist None eqop := give (tConst c u) π ;
          | @exist (Some op) eqop with inspect (decompose_stack π) := {
            | @exist (args, ρ) eqπ with inspect (arity op <=? #|args|) := {
              | @exist false hsat := give (tConst c u) π ;
              | @exist true hsat with inspect (split_lits (firstn (arity op) args)) := {
                | @exist (inl ls) eqs with inspect (prim_op_denote op ls) := {
                  | @exist None eqd := give (tConst c u) π ;
                  | @exist (Some r) eqd
                      with inspect (abstract_readback (po_shape (info op)) r) := {
                    | @exist (Some v) eqv := rec reduce v (appstack (skipn (arity op) args) ρ) ;
                    | @exist None eqv := False_rect _ _
                    }
                  } ;
                | @exist (inr (ls, a, rest)) eqs
                    with inspect (reduce a (Prim_app c u op (map term_of_lit ls)
                                     :: appstack (rest ++ skipn (arity op) args) ρ) _) := {
                  | @exist (@exist (t, ρ') prf) eqr with inspect (decompose_stack ρ') := {
                    | @exist (l, θ) eql with inspect (lit_of_term (mkApps t l)) := {
                      | @exist (Some lit) eqlit :=
                        rec reduce (tConst c u)
                          (appstack (map term_of_lit ls ++ mkApps t l
                                       :: rest ++ skipn (arity op) args) ρ) ;
                      | @exist None eqlit :=
                        give (tConst c u)
                          (appstack (map term_of_lit ls ++ mkApps t l
                                       :: rest ++ skipn (arity op) args) ρ)
                      }
                    }
                  }
                }
              }
            }
          }
        } ;
      | _ := give (tConst c u) π
      } ;

    | red_view_App f a π := rec reduce f (App_l a :: π) ;

    | red_view_Lambda na A t a args with inspect (RedFlags.beta flags) := {
      | @exist true eq1 := rec reduce (subst10 a t) args ;
      | @exist false eq1 := give (tLambda na A t) (App_l a :: args)
      } ;

    | red_view_Fix mfix idx π with RedFlags.fix_ flags := {
      | true with inspect (unfold_fix mfix idx) := {
        | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
          | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix_app mfix idx args :: ρ) _) := {
            | @exist (@exist (t, ρ') prf) eq3 with construct_viewc t := {
              | view_construct ind n ui with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  rec reduce fn (appstack args (App_l (mkApps (tConstruct ind n ui) l) :: ρ))
                } ;
              | view_other t ht with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  give (tFix mfix idx) (appstack args (App_l (mkApps t l) :: ρ))
                }
              }
            } ;
          | _ := give (tFix mfix idx) π
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | false := give (tFix mfix idx) π
      } ;

    | red_view_Case ci p c brs π with RedFlags.iota flags := {
      | true with inspect (reduce c (Case_discr ci p brs :: π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc_viewc t := {
            | ccview_construct ind' c' inst' with inspect (nth_error brs c') := {
              | exist (Some br) eqbr := rec reduce (iota_red ci.(ci_npar) p args br) π ;
              | exist None bot := False_rect _ _ } ;
            | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (narg, fn)) eq' :=
                rec reduce (tCase ci p (mkApps fn args) brs) π ;
              | @exist None bot := False_rect _ _
              } ;
            | ccview_other t ht := give (tCase ci p (mkApps t args) brs) π
            }
          }
        } ;
      | false := give (tCase ci p c brs) π
      } ;

    | red_view_Proj p c π with RedFlags.iota flags := {
      | true with inspect (reduce c (Proj p :: π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc0_viewc t := {
            | cc0view_construct ind' _
              with inspect (nth_error args (p.(proj_npars) + p.(proj_arg))) := {
              | @exist (Some arg) eqa := rec reduce arg π ;
              | @exist None eqa := False_rect _ _
              } ;
            | cc0view_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (rarg, fn)) eq' :=
                rec reduce (tProj p (mkApps fn args)) π ;
              | @exist None bot := False_rect _ _
              } ;
            | cc0view_other t ht := give (tProj p (mkApps t args)) π
            }
          }
        } ;
      | false := give (tProj p c) π
      } ;

    | red_view_other t π discr := give t π

    }.

  (* tRel *)
  Next Obligation.
    left.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ].
    pose proof (wt_context _ hΣ _ _ (h _ wfΣ)) as hc.
    cbn [fst snd] in hc.
    exact (rtf_rel Σ _ c hΣ hc (eq_sym eq)).
  Qed.

  (* tLetIn *)
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.

  (* tConst *)
  Next Obligation.
    left. econstructor. eapply red1_context.
    econstructor.
    - unfold declared_constant, declared_constant_gen.
      rewrite (abstract_env_lookup_correct _ _ _ wfΣ). rewrite <- eq. reflexivity.
    - cbn. reflexivity.
  Qed.
  (* tConst, a registered operation (design §7.2).  Equations places these
     right after the defined-constant obligation, because the bodiless clause
     shares its [cst_body] split. *)

  (* The operation fires: one [red_prim_op] step, under the over-applied tail. *)
  Next Obligation.
    left.
    symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs. symmetry in eqd. symmetry in eqv. symmetry in eqop.
    rewrite (abstract_readback_correct Σ wfΣ) in eqv.
    rewrite (abstract_prim_op_of_correct X c Σ wfΣ) in eqop.
    cbn. rewrite !zipc_appstack.
    repeat zip fold. eapply cored_context.
    assert (e : mkApps (tConst c u) args =
                mkApps (mkApps (tConst c u) (map term_of_lit ls)) (skipn (arity op) args)).
    { rewrite <- mkApps_app. f_equal. exact (prim_args_eq_inl eqs). }
    rewrite e. left. eapply red1_mkApps_f.
    eapply red_prim_op with (decl := {| cst_type := cst_type0; cst_body := None;
                                       cst_universes := cst_universes0;
                                       cst_relevance := cst_relevance0 |});
      [exact eqop| |reflexivity|exact eqd|exact eqv].
    unfold declared_constant, declared_constant_gen.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ). rewrite <- eq. reflexivity.
  Qed.
  Next Obligation.
    symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    match goal with H : Pr _ (appstack _ _) |- _ =>
      unfold Pr in H |- *; rewrite decompose_stack_appstack in H;
      rewrite decompose_stack_appstack; cbn in H |- *; exact H end.
  Qed.
  (* The readback of a fired operation cannot fail (§4.2(b)1, gate 4). *)
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    rewrite (abstract_readback_correct Σ wfΣ) in eqv.
    rewrite (abstract_prim_op_of_correct X c Σ wfΣ) in eqop.
    pose proof (abstract_env_lookup_correct' X c wfΣ) as hl. rewrite <- eq in hl.
    destruct (ref_prim_readback (wt := wt) Σ _ _ _ _ _ wΣ hl (eq_sym eqop) (eq_sym eqd)) as [v hv].
    rewrite hv in eqv. discriminate eqv.
  Qed.
  (* The [Prim_app] frame: the argument under evaluation is in the same term, to
     the right of the head. *)
  Next Obligation.
    symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs.
    eapply R_positionR.
    - cbn. rewrite !zipc_appstack. f_equal.
      rewrite mkApps_tApp_app. f_equal. symmetry. exact (prim_args_eq eqs).
    - simpl. rewrite ?stack_position_cons, ?stack_position_appstack. simpl.
      rewrite <- app_assoc. eapply positionR_poscat.
      apply positionR_repeat_app_r.
      pose proof (f_equal (@length _) (prim_args_eq eqs)) as hl.
      rewrite !length_app in hl. cbn in hl. rewrite ?length_app in hl.
      rewrite ?length_app. lia.
  Qed.
  (* The argument reduced to a literal: re-enter on the head.  The step is
     strict because the argument was not a literal. *)
  Next Obligation.
    clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs.
    assert (hne : mkApps t l <> a).
    { intros e. rewrite e in eqlit. rewrite (snd (split_lits_inr eqs)) in eqlit.
      discriminate eqlit. }
    destruct (prf Σ wfΣ) as [hreq [hpr _]].
    unfold Pr in hpr. cbn in hpr.
    symmetry in eql. rewrite eql in hpr. cbn in hpr. subst θ.
    apply decompose_stack_eq in eql. subst ρ'.
    destruct hreq as [heq | hR].
    - exfalso. apply hne. injection heq as -> hs.
      destruct l as [|x l]; [reflexivity|]. cbn in hs. discriminate hs.
    - dependent destruction hR.
      + left.
        match goal with H : cored _ _ _ _ |- _ =>
          cbn in H; rewrite !zipc_appstack in H; cbn in H; rewrite ?zipc_appstack in H;
          rewrite ?mkApps_tApp_app in H; rewrite <- (prim_args_eq eqs) in H;
          cbn; rewrite !zipc_appstack; exact H end.
      + exfalso. apply hne.
        match goal with
        | Hz : {| pr1 := ?y; pr2 := _ |} = {| pr1 := ?x; pr2 := _ |} |- _ =>
          assert (hzz : x = y) by (apply (f_equal pr1) in Hz; symmetry; exact Hz)
        end.
        apply (zipc_inj _ _ (Prim_app c u op (map term_of_lit ls)
                               :: appstack (rest ++ skipn (arity op) args) ρ)).
        rewrite <- zipc_appstack. exact hzz.
  Qed.
  Next Obligation.
    try clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    match goal with H : Pr _ (appstack _ _) |- _ =>
      unfold Pr in H |- *; rewrite decompose_stack_appstack in H;
      rewrite decompose_stack_appstack; cbn in H |- *; exact H end.
  Qed.
  (* The argument's weak-head form is not a literal: the application stops. *)
  Next Obligation.
    clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs.
    destruct (prf Σ wfΣ) as [hreq [hpr _]].
    unfold Pr in hpr. cbn in hpr.
    symmetry in eql. rewrite eql in hpr. cbn in hpr. subst θ.
    apply decompose_stack_eq in eql. subst ρ'.
    assert (hsame : mkApps t l = a ->
      Req Σ Γ (tConst c u, appstack (map term_of_lit ls ++ mkApps t l
                                       :: rest ++ skipn (arity op) args) ρ)
              (tConst c u, appstack args ρ)).
    { intros e. left. rewrite e, <- (prim_args_eq eqs). reflexivity. }
    destruct hreq as [heq | hR].
    - apply hsame. injection heq as -> hs.
      destruct l as [|x l]; [reflexivity|]. cbn in hs. discriminate hs.
    - dependent destruction hR.
      + right. left.
        match goal with H : cored _ _ _ _ |- _ =>
          cbn in H; rewrite !zipc_appstack in H; cbn in H; rewrite ?zipc_appstack in H;
          rewrite ?mkApps_tApp_app in H; rewrite <- (prim_args_eq eqs) in H;
          cbn; rewrite !zipc_appstack; exact H end.
      + apply hsame.
        match goal with
        | Hz : {| pr1 := ?y; pr2 := _ |} = {| pr1 := ?x; pr2 := _ |} |- _ =>
          assert (hzz : x = y) by (apply (f_equal pr1) in Hz; symmetry; exact Hz)
        end.
        apply (zipc_inj _ _ (Prim_app c u op (map term_of_lit ls)
                               :: appstack (rest ++ skipn (arity op) args) ρ)).
        rewrite <- zipc_appstack. exact hzz.
  Qed.
  Next Obligation.
    try clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    unfold Pr. cbn. rewrite !decompose_stack_appstack. reflexivity.
  Qed.

  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    specialize (h _ wfΣ).
    apply (wt_context _ wΣ) in h. cbn [fst snd] in h.
    destruct (rtf_const Σ _ _ _ wΣ h) as [decl d].
    unfold declared_constant, declared_constant_gen in d.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ), <- eq in d.
    discriminate.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    specialize (h _ wfΣ).
    apply (wt_context _ wΣ) in h. cbn [fst snd] in h.
    destruct (rtf_const Σ _ _ _ wΣ h) as [decl d].
    unfold declared_constant, declared_constant_gen in d.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ), <- eq in d.
    discriminate.
  Qed.

  (* tApp *)
  Next Obligation.
    right.
    simpl. unfold posR. simpl.
    rewrite stack_position_cons.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. rewrite e in h. cbn in h.
    assumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    left. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    case_eq (decompose_stack args). intros l ρ e.
    cbn. unfold Pr in h. rewrite e in h. cbn in h.
    assumption.
  Qed.
  Next Obligation.
    rewrite β in eq1. discriminate.
  Qed.

  (* tFix *)
  Next Obligation.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    eapply R_positionR.
    - cbn. rewrite zipc_appstack. cbn. reflexivity.
    - simpl. rewrite !stack_position_appstack, !stack_position_cons. simpl.
      rewrite <- app_assoc.
      eapply positionR_poscat.
      constructor.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite H in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. subst. clear e.

    case_eq (decompose_stack ρ'). intros ll s e1.
    pose proof (decompose_stack_eq _ _ _ e1). subst.

    eapply R_Req_R.
    - instantiate (1 := (tFix mfix idx, appstack (args ++ (mkApps (tConstruct ind n ui) l) :: l') π')).
      left. cbn. rewrite 2!zipc_appstack. cbn. rewrite zipc_appstack.
      repeat zip fold. eapply cored_context.
      assert (forall args l u v, mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l)) as thm.
      { clear. intro args. induction args ; intros l u v.
        - reflexivity.
        - cbn. rewrite IHargs. reflexivity.
      }
      rewrite thm.
      left. eapply red_fix.
      + eauto.
      + unfold is_constructor.
        rewrite nth_error_app2 by eauto.
        replace (#|args| - #|args|) with 0 by auto with arith.
        cbn.
        unfold isConstruct_app.
        rewrite decompose_app_mkApps by reflexivity.
        reflexivity.
    - destruct r.
      + inversion H0. subst.
        destruct ll.
        * cbn in H3. subst. cbn in eq4. inversion eq4. subst.
          reflexivity.
        * cbn in H3. discriminate H3.
      + dependent destruction H0.
        * cbn in H0. rewrite 2!zipc_appstack in H0.
          rewrite decompose_stack_appstack in eq4.
          case_eq (decompose_stack s). intros l0 s0 e2.
          rewrite e2 in eq4. cbn in eq4.
          destruct l0.
          -- rewrite app_nil_r in eq4. inversion eq4. subst. clear eq4.
             pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             symmetry in ee. subst.
             right. left.
             cbn. rewrite !zipc_appstack.
             unfold Pr in p. cbn in p.
             rewrite e1 in p. cbn in p. subst.
             cbn in H0.
             clear - H0.

             match goal with
             | |- ?A =>
               let e := fresh "e" in
               let B := type of H0 in
               assert (A = B) as e ; [| rewrite e ; assumption ]
             end.
             set (t := tConstruct ind n ui). clearbody t.
             set (f := tFix mfix idx). clearbody f.
             f_equal.
             ++ clear. revert ll π' l' t f.
                induction args ; intros ll π' l' t f.
                ** cbn. rewrite zipc_appstack. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
             ++ clear. revert π' l' c f.
                induction args ; intros π' l' c f.
                ** cbn. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
          -- pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             subst. exfalso.
             eapply decompose_stack_not_app. eassumption.
        * cbn in H1. inversion H1.
          rewrite 2!zipc_appstack in H3.
          unfold Pr in p. cbn in p.
          rewrite e1 in p. cbn in p. subst.
          cbn in H3. rewrite zipc_appstack in H3.
          apply zipc_inj in H3.
          apply PCUICAstUtils.mkApps_inj in H3.
          inversion H3. subst.
          rewrite e1 in eq4. inversion eq4. subst.
          reflexivity.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l1 ρ1 e.
    rewrite e in h. cbn in h. subst.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack. cbn.
    rewrite e. cbn. reflexivity.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2) as e2.
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite e2 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. subst. clear e.
    symmetry in eq4. apply decompose_stack_eq in eq4 as ?. subst.

    rewrite e2.
    destruct r as [r | r].
    - inversion r. subst.
      destruct l. 2: discriminate.
      cbn in *. subst.
      left. reflexivity.
    - unfold Pr in p. cbn in p.
      rewrite eq4 in p. simpl in p. subst.
      dependent destruction r.
      + cbn in H. rewrite zipc_appstack in H.
        cbn in H. rewrite !zipc_appstack in H.
        right. left. cbn. rewrite !zipc_appstack. cbn.
        rewrite !zipc_appstack. assumption.
      + cbn in H0. inversion H0.
        rewrite !zipc_appstack in H2. cbn in H2.
        rewrite zipc_appstack in H2.
        apply zipc_inj in H2. apply PCUICAstUtils.mkApps_inj in H2.
        inversion H2. subst.
        left. reflexivity.
  Qed.
  Next Obligation.
    symmetry in eq4.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    unfold Pr in p. cbn in p.
    rewrite eq4 in p. simpl in p. subst.
    unfold Pr. cbn.
    rewrite decompose_stack_appstack. cbn.
    case_eq (decompose_stack π). intros ll π' e. cbn.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2) as e2.
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'. cbn.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite e2 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. reflexivity.
  Qed.

  (* tCase *)
  Next Obligation.
    right. unfold posR. simpl.
    rewrite stack_position_cons.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    clear eq.
    pose proof (hΣ := hΣ _ wfΣ).
    sq. specialize (prf _ wfΣ). destruct prf as [r [p0 p1]].

    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'. specialize (h _ wfΣ).
    eapply red_wt in r' ; tea.
    zip fold in r'.
    apply wt_context in r'; auto; cbn in *.
    destruct (rtf_case_construct _ _ _ _ _ _ _ _ _ hΣ r') as (?&?&nth&?); subst.
    rewrite nth in eqbr; noconf eqbr.
    constructor.
    eapply cored_red_cored; cycle 1.
    - zip fold in r; exact r.
    - constructor.
      eapply red1_context.
      eapply red_iota; eauto.
  Qed.
  Next Obligation.
    clear eq.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'.
    eapply red_wt in r; eauto.
    zip fold in r.
    apply wt_context in r; auto; cbn in *.
    destruct (rtf_case_construct _ _ _ _ _ _ _ _ _ hΣ r) as (?&?&nth&?); subst.
    rewrite nth in bot; congruence.
  Qed.
  Next Obligation.
    clear eq.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'.
    constructor.
    eapply cored_red_cored; cycle 1.
    - zip fold in r'; exact r'.
    - constructor.
      eapply red1_context.
      eapply red_cofix_case; eauto.
  Qed.
  Next Obligation.
    clear eq. destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    pose proof r as r'.
    eapply red_wt in r; eauto.
    zip fold in r.
    apply wt_context in r; auto; cbn in *.
    pose proof (rtf_cofix _ _ _ _ hΣ r) as hn.
    unfold unfold_cofix in bot.
    match type of bot with context [nth_error ?m ?i] => destruct (nth_error m i) end;
      congruence.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    destruct r.
    - inversion H. subst.
      clear H.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      rewrite <- prf' in p0. cbn in p0. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* tProj *)
  Next Obligation.
    right. unfold posR. simpl.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    pose proof (hΣ := hΣ _ wfΣ).
    destruct (prf Σ wfΣ)  as [r [p' p0]].
    sq.
    left.
    apply Req_red in r as hr.
    sq.
    pose proof (red_wt _ hΣ (h _ wfΣ) hr) as hh.
    eapply cored_red_cored ; try eassumption.
    unfold Pr in p'. simpl in p'. pose proof p' as p''.
    rewrite <- prf' in p''. simpl in p''. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst. cbn. rewrite zipc_appstack. cbn.
    do 2 zip fold. eapply cored_context.
    constructor.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh. apply wt_context in hh. 2: assumption.
    simpl in hh. destruct (rtf_proj_construct _ _ _ _ _ _ _ hΣ hh) as [ei _].
    subst. constructor. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    sq.
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst.
    apply Req_red in r as hr.
    sq.
    pose proof (red_wt _ hΣ (h _ wfΣ) hr) as hh.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh.
    apply wt_context in hh. 2: assumption.
    simpl in hh.
    destruct (rtf_proj_construct _ _ _ _ _ _ _ hΣ hh) as (_ & _ & hlt).
    apply nth_error_Some in hlt. congruence.
  Qed.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    dependent destruction r.
    - inversion H. subst.
      left. eapply cored_context.
      constructor.
      simpl in prf'. inversion prf'. subst.
      eapply red_cofix_proj with (args := []). eauto.
    - clear eq.
      dependent destruction H.
      + left.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply cored_trans' ; try eassumption.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
      + left.
        cbn in H0. destruct y'. inversion H0. subst. clear H0.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        rewrite zipc_appstack in H2. cbn in H2.
        cbn. rewrite H2.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    sq.
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    assert (h' : wt Σ Γ (zip (tProj p (mkApps (tCoFix mfix idx) args), π))).
    { dependent destruction r.
      - inversion H. subst.
        simpl in prf'. inversion prf'. subst. now apply h.
      - clear eq. dependent destruction H.
        + apply cored_red in H. destruct H as [r].
          eapply red_wt ; eauto.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          cbn in r. rewrite zipc_appstack in r. cbn in r.
          assumption.
        + cbn in H0. destruct y'. inversion H0. subst. clear H0.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          rewrite zipc_appstack in H2. cbn in H2.
          cbn. rewrite <- H2. now apply h.
          }
    replace (zip (tProj p (mkApps (tCoFix mfix idx) args), π))
      with (zip (tCoFix mfix idx, appstack args (Proj p :: π)))
      in h'.
    - sq.
      apply wt_context in h' ; auto. simpl in h'.
      pose proof (rtf_cofix _ _ _ _ hΣ h') as hn.
      unfold unfold_cofix in bot.
      match type of bot with context [nth_error ?m ?i] => destruct (nth_error m i) end;
        congruence.
    - cbn. rewrite zipc_appstack. reflexivity.
  Qed.
  Next Obligation.
    clear eq.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    dependent destruction r.
    - inversion H. subst. cbn in prf'. inversion prf'. subst.
      cbn. reflexivity.
    - unfold Pr in pr. cbn in pr.
      rewrite <- prf' in pr. cbn in pr. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* Other *)
  Next Obligation.
    revert discr.
    apply_funelim (red_discr t π). all: auto.
  Qed.
  Next Obligation.
    revert discr hl.
    apply_funelim (red_discr t π). all: easy.
  Qed.

  Lemma welltyped_R_pres Σ (wfΣ : abstract_env_ext_rel X Σ) Γ :
    forall x y : term × stack, wt Σ Γ (zip x) -> R Σ Γ y x -> wt Σ Γ (zip y).
  Proof using TF hX.
    intros x y H HR.
    pose proof (hΣ := hΣ _ wfΣ).
    clear wfΣ.
    sq.
    destruct x as [x πx], y as [y πy].
    dependent induction HR.
    - eapply cored_wt. all: eauto.
    - simpl in H1. revert H1; intros [= H2 _].
      now rewrite <- H2.
  Qed.

  Section reducewf.
    Context (Γ : context).

    Notation sigmaarg :=
      (sigma (fun t => sigma (fun π => forall Σ, abstract_env_ext_rel X Σ -> wt Σ Γ (zipc t π)))).

    Local Instance wf_proof : WellFounded (fun x y : sigmaarg =>
        forall Σ, abstract_env_ext_rel X Σ -> R Σ Γ (pr1 x, pr1 (pr2 x)) (pr1 y, pr1 (pr2 y))).
    Proof using normalization_in hX.
      intros [t [π hwt]].
      (* We fuel the accessibility proof to run reduction inside Rocq. *)
      unshelve eapply (Acc_intro_generator
        (R:=fun x y : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (x.(pr1), x.(pr2).(pr1)) (y.(pr1), y.(pr2).(pr1)))
        (P:=fun x : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ (zip (x.(pr1), x.(pr2).(pr1))))
        (fun x y Px Hy => _) 1000 _ {| pr1 := t; pr2 := {| pr1 := π; pr2 := hwt |} |} hwt).
      - cbn in *. intros. destruct y as [t' [π' hwt']]. cbn. now apply hwt'.
      - cbn in *. intros.
        destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
        destruct (hΣ _ wfΣ) as [hΣ]. pose proof (R_Acc Γ (t0.(pr1), t0.(pr2).(pr1)) H).
        clear -H0. destruct t0 as [t [π hwt]].
        cbn in *. revert hwt.
        depind H0. intros hwt. constructor. intros. eapply H0.
        * cbn in H1. exact H1.
        * reflexivity.
  Defined.

  Equations reduce_stack_full (t : term) (π : stack) (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ (zip (t,π))) :
    { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t, π) /\ Pr t' π /\ Pr' t' }
    by wf (t, π) (fun (x y : term * stack) => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ x y) :=
    reduce_stack_full t π h := _reduce_stack Γ t π h (fun t' π' hr => reduce_stack_full t' π' (fun Σ wfΣ' => welltyped_R_pres Σ wfΣ' Γ _ _ (h Σ wfΣ') (hr Σ wfΣ'))).

  End reducewf.

  Definition reduce_stack Γ t π h :=
    let '(exist ts _) := reduce_stack_full Γ t π h in ts.

  Lemma reduce_stack_Req :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
     Req Σ Γ (reduce_stack Γ t π h) (t, π).
  Proof using Type.
    intros Σ wfΣ Γ t π h.
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r _]];
    eassumption.
  Qed.

  Theorem reduce_stack_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
      ∥ Σ ;;; Γ ⊢ zip (t, π) ⇝ zip (reduce_stack Γ t π h) ∥.
  Proof using EF hX.
    intros Σ wfΣ Γ t π h.
    assert (req := reduce_stack_Req Σ wfΣ _ _ _ h).
    eapply Req_red in req as [r].
    destruct (hΣ _ wfΣ) as [hP].
    sq. eapply into_closed_red; [exact r| |].
    - exact (ref_closed_context Σ Γ _ hP (h Σ wfΣ)).
    - exact (ref_open_term Σ Γ _ hP (h Σ wfΣ)).
  Qed.

  Lemma reduce_stack_decompose :
    forall Γ t π h,
      snd (decompose_stack (snd (reduce_stack Γ t π h))) =
      snd (decompose_stack π).
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p p']]];
    try eassumption.
    unfold Pr in p. symmetry. assumption.
  Qed.

  Lemma reduce_stack_context :
    forall Γ t π h,
      stack_context (snd (reduce_stack Γ t π h)) =
      stack_context π.
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (reduce_stack_decompose Γ t π h) as hd.
    case_eq (decompose_stack π). intros l ρ e1.
    case_eq (decompose_stack (snd (reduce_stack Γ t π h))). intros l' ρ' e2.
    rewrite e1 in hd. rewrite e2 in hd. cbn in hd. subst.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2) as eq.
    rewrite eq. subst.
    rewrite 2!stack_context_appstack. reflexivity.
  Qed.

  Definition isred (t : term * stack) :=
    isApp (fst t) = false /\
    (isLambda (fst t) -> isStackApp (snd t) = false).

  Lemma reduce_stack_isred :
    forall Γ t π h,
      RedFlags.beta flags ->
      isred (reduce_stack Γ t π h).
  Proof using Type.
    intros Γ t π h hr.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
    split.
    - assumption.
    - apply hLam. assumption.
  Qed.

  Lemma reduce_stack_noApp :
    forall Γ t π h,
      isApp (fst (reduce_stack Γ t π h)) = false.
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
  Qed.

  Lemma reduce_stack_noLamApp :
    forall Γ t π h,
      RedFlags.beta flags ->
      isLambda (fst (reduce_stack Γ t π h)) ->
      isStackApp (snd (reduce_stack Γ t π h)) = false.
  Proof using Type.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
  Qed.

  Definition reduce_term Γ t
    (h : forall Σ, abstract_env_ext_rel X Σ -> wt Σ Γ t) :=
    zip (reduce_stack Γ t [] h).

  Theorem reduce_term_sound :
    forall Γ t (h : forall Σ, abstract_env_ext_rel X Σ -> wt Σ Γ t)
      Σ, abstract_env_ext_rel X Σ ->
      ∥ Σ ;;; Γ ⊢ t ⇝ reduce_term Γ t h ∥.
  Proof using EF hX.
    intros Γ t h Σ wfΣ.
    unfold reduce_term.
    refine (reduce_stack_sound _ _ _ _ [] _); eauto.
  Qed.

  Lemma reduce_term_welltyped Γ t h Σ (wfΣ : abstract_env_ext_rel X Σ) :
    wt Σ Γ (reduce_term Γ t h).
  Proof using EF TF hX.
    destruct (reduce_term_sound Γ t h Σ wfΣ) as [r].
    destruct (hΣ Σ wfΣ) as [wΣ].
    exact (red_wt Σ wΣ (h Σ wfΣ) r).
  Qed.

  Scheme Acc_ind' := Induction for Acc Sort Prop.

  Lemma Fix_F_prop :
    forall A R P f (pred : forall x : A, P x -> Prop) x hx,
      (forall x aux, (forall y hy, pred y (aux y hy)) -> pred x (f x aux)) ->
      pred x (@Fix_F A R P f x hx).
  Proof using Type.
    intros A R P f pred x hx h.
    induction hx using Acc_ind'.
    cbn. eapply h. assumption.
  Qed.

  Lemma reduce_stack_prop :
    forall Γ t π h (P : term × stack -> term × stack -> Prop),
      (forall t π h aux,
          (forall t' π' hR, P (t', π') (` (aux t' π' hR))) ->
          P (t, π) (` (_reduce_stack Γ t π h aux))) ->
      P (t, π) (reduce_stack Γ t π h).
  Proof using Type.
    intros Γ t π h P hP.
    unfold reduce_stack.
    case_eq (reduce_stack_full Γ t π h).
    apply_funelim (reduce_stack_full Γ t π h); clear -hP.
    intros t π hwt ih [t' ρ] ? e.
    match type of e with
    | _ = ?u =>
      change (P (t, π) (` u))
    end.
    rewrite <- e.
    apply hP. intros t'0 π' hR.
    specialize (ih _ _ hR).
    set (r := reduce_stack_full _ _ _ _) in *.
    eapply (ih _ (proj2_sig r)). clearbody r. now destruct r.
  Qed.

  (** A variable bound by an assumption is in normal form: the machine returns it with
      the empty stack (plan I7 rev 13 [reduce_stack_vass], for any [wt]). From
      [reduce_stack_Req]: a variable without a body has no [red1] step, and a zipped
      term equal to a variable has the empty stack. *)
  Lemma reduce_stack_Rel_assum Γ n decl h :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    reduce_stack Γ (tRel n) [] h = (tRel n, []).
  Proof using Type.
    intros hn hb.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (reduce_stack_Req Σ wfΣ Γ (tRel n) [] h) as hr. revert hr.
    destruct (reduce_stack Γ (tRel n) [] h) as [u ρ]. intros hr.
    destruct hr as [heq | hR]; [exact heq|].
    exfalso. apply R_cases in hR as [hc | [hz hp]].
    - cbn in hc. exact (cored_Rel_assum Σ Γ n decl _ hn hb hc).
    - cbn in hz. destruct (zipc_tRel_inv u ρ n hz) as [-> ->]. cbn in hp. inversion hp.
  Qed.

  Lemma decompose_stack_at_appstack_None l s n :
    isStackApp s = false ->
    nth_error l n = None <->
    decompose_stack_at (appstack l s) n = None.
  Proof using Type.
    intros no_app.
    induction l in l, n |- *; cbn in *.
    - rewrite nth_error_nil.
      split; intros; try easy.
      destruct s as [|[]]; cbn in *; easy.
    - destruct n; [easy|].
      cbn in *.
      split.
      + rewrite IHl.
        now intros ->.
      + rewrite IHl.
        now destruct decompose_stack_at as [((?&?)&?)|]; intros.
  Qed.

  Lemma mkApps_tApp hd arg args :
    mkApps (tApp hd arg) args = mkApps hd (arg :: args).
  Proof using Type. reflexivity. Qed.

  Lemma tApp_mkApps hd args arg :
    tApp (mkApps hd args) arg = mkApps hd (args ++ [arg]).
  Proof using Type.
    change (tApp ?hd ?a) with (mkApps hd [a]).
    now rewrite mkApps_app.
  Qed.

  Definition isCoFix_app t :=
    match (decompose_app t).1 with
    | tCoFix _ _ => true
    | _ => false
    end.

  Lemma reduce_stack_whnf :
    forall Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ),
      let '(u, ρ) := reduce_stack Γ t π h in
       ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥.
  Proof using Type.
    intros Γ t π h Σ wfΣ.
    eapply reduce_stack_prop
      with (P := fun x y =>
        let '(u, ρ) := y in
        ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥
      ).
    clear -wfΣ hX EF TF.
    intros t π h aux.
    apply_funelim (_reduce_stack Γ t π h aux); clear -wfΣ hX EF TF.
    all: simpl.
    all: intros *.
    all: repeat match goal with
      [ |- (forall (t' : term) (π' : stack)
         (hR : forall Σ,
               abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ }) -> _ ] => intros reduce
    | [ |- (forall (t' : term) (π' : stack)
        (hR : forall Σ,
          abstract_env_ext_rel X Σ -> R Σ _ _ _), _) -> _ ] => intros haux
          | [ |- _ ] => intros ?
    end.
    all: try match goal with
             | |- context[False_rect _ ?f] => destruct f
             end.
    (* The bodiless-constant leaves of the Const branch (design §7.2), found by
       their [abstract_prim_op_of] equation; every other goal is left to the
       positional bullets below. *)
    all: try solve [
      repeat match goal with H : inspect _ = _ |- _ => clear H end;
      match goal with
      (* an axiom *)
      | hop : None = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c
        |- context [ zipp _ ?π ] =>
          unfold zipp; case_eq (decompose_stack π); intros;
          constructor; constructor; eapply whne_mkApps; eapply whne_const;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop ]
      (* a recursive call: the operation fired, or an argument became a literal *)
      | hop : Some _ = abstract_prim_op_of X _,
        rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), _
        |- _ =>
          match goal with |- context [ rf ?x ?y ?z ] =>
            case_eq (rf x y z); specialize (ha x y z);
            intros [t' π'] Ha eq'; cbn; rewrite eq' in ha; cbn in ha; assumption
          end
      (* unsaturated *)
      | hsat : false = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
        hop : Some ?op = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c |- _ =>
          unfold zipp; rewrite <- hπ; cbn; constructor;
          eapply whnf_primapp_partial;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop
          | apply Nat.leb_gt; symmetry; exact hsat ]
      (* saturated on literals, the denotation fails *)
      | hd : None = prim_op_denote ?op ?ls, hs : inl ?ls = split_lits (firstn (arity ?op) ?args),
        hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
        hop : Some ?op = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c |- _ =>
          symmetry in hs; symmetry in hsat; apply Nat.leb_le in hsat;
          unfold zipp; rewrite <- hπ; cbn;
          rewrite (prim_args_eq_inl hs), mkApps_app;
          constructor; constructor; eapply whne_mkApps; eapply whne_primapp_inert;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop
          | rewrite <- (split_lits_length_inl hs), length_firstn; lia
          | rewrite prim_reduct_lits, <- hd; reflexivity ]
      (* the reduced argument is not a literal: rigid, or ill-typed if over-applied *)
      | hlit : None = lit_of_term (mkApps ?t ?l), hl' : (?l, ?θ) = decompose_stack ?ρ',
        hs : inr (?ls, ?a, ?rest) = split_lits (firstn (arity ?op) ?args),
        hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
        hop : Some ?op = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c,
        rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), _ |- _ =>
          let hw := fresh "hw" in
          match goal with
          | hr : exist (t, ρ') ?prf = rf a ?s ?z |- _ =>
            pose proof (ha a s z) as hw; rewrite <- hr in hw; cbn in hw;
            destruct (prf Σ wfΣ) as [_ [hpr _]]; clear hr
          | hr : rf a ?s ?z = exist (t, ρ') ?prf |- _ =>
            pose proof (ha a s z) as hw; rewrite hr in hw; cbn in hw;
            destruct (prf Σ wfΣ) as [_ [hpr _]]; clear hr
          end;
          unfold Pr in hpr; cbn in hpr; rewrite <- hl' in hpr; cbn in hpr; subst θ;
          symmetry in hl'; apply decompose_stack_eq in hl'; subst ρ';
          unfold zipp in hw; rewrite decompose_stack_appstack in hw; cbn in hw;
          rewrite app_nil_r, ?stack_context_appstack in hw; cbn in hw;
          rewrite ?stack_context_appstack in hw;
          symmetry in hs; symmetry in hsat; apply Nat.leb_le in hsat;
          destruct (split_lits_inr hs) as [efirst _];
          assert (hlen : #|ls| + S #|rest| = arity op)
            by (apply (f_equal (@length _)) in efirst;
                rewrite length_firstn, length_app, length_map in efirst; cbn in efirst; lia);
          pose proof (decompose_stack_twice _ _ _ (eq_sym hπ)) as hρ;
          unfold zipp; rewrite decompose_stack_appstack, hρ; cbn;
          rewrite app_nil_r, stack_context_appstack;
          destruct (skipn (arity op) args) as [|x more] eqn:hsk;
          [ rewrite app_nil_r; destruct hw as [hw]; constructor;
            eapply whnf_primapp_rigid;
            [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
            | reflexivity
            | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop
            | exact hlen | exact hw | symmetry; exact hlit ]
          | exfalso;
            match goal with hwt : forall Σ, abstract_env_ext_rel X Σ -> wt Σ _ (zip (tConst _ _, _)) |- _ =>
              destruct (hΣ _ wfΣ) as [wΣ];
              pose proof (hwt _ wfΣ) as hwt';
              symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
              cbn in hwt'; rewrite zipc_appstack in hwt'; zip fold in hwt';
              apply wt_context in hwt'; [|exact wΣ]; cbn in hwt';
              eapply (rtf_prim_overapplied (wt := wt) _ _ _ _ _ _ wΣ
                        (eq_trans (eq_sym (abstract_prim_op_of_correct X _ _ wfΣ)) (eq_sym hop)));
              [|exact hwt'];
              apply (f_equal (@length _)) in hsk; rewrite length_skipn in hsk; cbn in hsk; lia
            end ]
      end ].
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] H eq.
      rewrite eq in haux. cbn in haux.
      assumption.
    - clear Heq.
      revert discr.
      revert h reduce haux; apply_funelim (red_discr t π); clear -wfΣ hX EF TF.
      all: intros; try destruct discr.
      all: try solve [ constructor ; constructor ].
      all: try solve [
        unfold zipp ; case_eq (decompose_stack π) ; intros ;
        do 2 constructor ; eapply whne_mkApps ; constructor
      ].
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eauto with pcuic.
        * exfalso.
          destruct (hΣ _ wfΣ) as [hΣ].
          cbn in h. zip fold in h.
          specialize (h _ wfΣ).
          apply wt_context in h; auto.
          simpl in h. rewrite stack_context_appstack in h.
          exact (rtf_app_sort _ _ _ _ hΣ h).
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eauto with pcuic.
        * exfalso.
          destruct (hΣ _ wfΣ) as [hΣ].
          cbn in h. zip fold in h.
          specialize (h _ wfΣ). apply wt_context in h; auto.
          simpl in h. rewrite stack_context_appstack in h.
          exact (rtf_app_prod _ _ _ _ _ _ hΣ h).
        + unfold zipp.
          case_eq (decompose_stack π). intros l ρ e.
          apply decompose_stack_eq in e. subst.
          destruct l.
          * simpl. eauto with pcuic.
          * exfalso.
            destruct (hΣ _ wfΣ) as [hΣ].
            cbn in h. zip fold in h.
            specialize (h _ wfΣ).
            apply wt_context in h; auto.
            simpl in h. rewrite stack_context_appstack in h.
            exact (rtf_app_prim _ _ _ _ hΣ h).
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. econstructor.
      rewrite <- eq. cbn.
      cbn in H. inversion e. reflexivity.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_letin_nozeta. assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_const_nodelta. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. destruct decompose_stack eqn:eq.
      apply decompose_stack_noStackApp in eq as ?.
      apply decompose_stack_eq in eq.
      destruct l.
      + cbn in *; subst.
        cbn in *; congruence.
      + cbn.
        constructor.
        apply whnf_mkApps.
        apply whne_app.
        now apply whne_lam_nobeta.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_mkApps.
      now apply whne_fix_nofix.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_fixapp.
      clear -e. unfold unfold_fix in e. now destruct nth_error.
    - unfold zipp.
      destruct decompose_stack eqn:eq.
      apply decompose_stack_noStackApp in eq as ?.
      apply decompose_stack_eq in eq.
      subst.
      constructor.
      apply whnf_fixapp.
      clear -e eq1 H. unfold unfold_fix in eq1. symmetry in e.
      apply <- decompose_stack_at_appstack_None in e ; eauto.
      destruct (nth_error mfix idx) ; [left | now right]. eexists; split ; now eauto.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        specialize (haux x y z) as ?;
        destruct (reduce x y z)
      end.
      destruct (a _ wfΣ) as (?&?&?&?).
      now destruct x.
    - match type of eq3 with
      | context [ reduce ?x ?y ?z ] =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq3; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -wfΣ hΣ eq4 ht eq2 eq1 h prf haux TF.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- eq4 in stacks.
      subst.
      symmetry in eq2.
      assert (narg = #|args|) as -> by (now apply decompose_stack_at_length in eq2).
      eapply decompose_stack_at_eq in eq2 as ->.
      symmetry in eq4.
      apply decompose_stack_eq in eq4.
      subst.
      rewrite zipc_appstack in h.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_wt in h; eauto.
      rewrite zipc_appstack in h.
      cbn in h.
      rewrite tApp_mkApps in h.
      unfold zipp in *.
      apply wt_zipc_zipp in h; auto.
      unfold zipp in *.
      rewrite decompose_stack_appstack in *.
      cbn.
      destruct (decompose_stack ρ) eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      cbn in *.
      rewrite <-mkApps_app in h.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in h;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      destruct H as (noapp&_); cbn in *.
      rewrite app_nil_r in *.
      rewrite <- app_assoc in *.
      cbn in *.
      destruct haux.
      symmetry in eq1.
      unfold unfold_fix in eq1.
      case_eq (nth_error mfix idx); [intros d e | intro e]; rewrite e in eq1; inversion eq1.
      match goal with
      | hw : whnf ?fl ?S ?G (mkApps ?u ?l) |- _ =>
        assert (hwne : ∥ whne fl S G (mkApps u l) ∥)
      end.
      { eapply (rtf_fix_arg_whne (wt := wt)); eauto.
        * unfold unfold_fix. now rewrite e.
        * now destruct t. }
      destruct hwne as [hwne].
      constructor.
      constructor.
      eapply whne_fixapp.
      + eassumption.
      + now apply nth_error_snoc.
      + exact hwne.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_mkApps.
      now apply whne_case_noiota.
    - match type of eq with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -hΣ wfΣ ht prf' h prf haux TF.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- prf' in stacks.
      subst.
      symmetry in prf'.
      apply decompose_stack_eq in prf' as ->.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_wt in h; eauto using sq.
      clear r.
      rewrite zipc_appstack in h.
      cbn in h.
      zip fold in h.
      apply wt_context in h; auto.
      cbn in *.
      unfold zipp in *.
      rewrite decompose_stack_appstack in haux; cbn in *.

      destruct decompose_stack eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in h;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      rewrite app_nil_r in *.
      destruct haux.
      match goal with
      | hw : whnf ?fl ?S ?G (mkApps ?u ?l) |- _ =>
        assert (hwne : ∥ whne fl S G (mkApps u l) ∥)
      end.
      { eapply (rtf_case_arg_whne (wt := wt)); eauto.
        destruct H as (noapp&_).
        now destruct t. }
      destruct hwne as [hwne].
      constructor.
      apply whnf_mkApps, whne_case.
      exact hwne.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_proj_noiota. assumption.
    - match type of eq with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -hΣ wfΣ ht prf' h prf haux TF.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- prf' in stacks.
      subst.
      symmetry in prf'.
      apply decompose_stack_eq in prf' as ->.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_wt in h; eauto using sq.
      clear r.
      rewrite zipc_appstack in h.
      cbn in h.
      zip fold in h.
      apply wt_context in h; auto.
      cbn in *.
      unfold zipp in *.
      rewrite decompose_stack_appstack in haux; cbn in *.

      destruct decompose_stack eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in h;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      rewrite app_nil_r in *.
      destruct haux.
      match goal with
      | hw : whnf ?fl ?S ?G (mkApps ?u ?l) |- _ =>
        assert (hwne : ∥ whne fl S G (mkApps u l) ∥)
      end.
      { eapply (rtf_proj_arg_whne (wt := wt)); eauto.
        destruct H as (noapp&_).
        now destruct t. }
      destruct hwne as [hwne].
      constructor. apply whnf_mkApps, whne_proj.
      exact hwne.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
  Qed.

  Theorem reduce_term_complete Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t h :
    ∥whnf flags Σ Γ (reduce_term Γ t h)∥.
  Proof using Type.
    pose proof (reduce_stack_whnf Γ t [] h _ wfΣ) as H.
    unfold reduce_term.
    unfold reduce_stack in *.
    destruct reduce_stack_full.
    destruct (a _ wfΣ) as (_&stack_eq&_).
    unfold Pr in stack_eq.
    cbn in stack_eq.
    destruct decompose_stack eqn:decomp.
    cbn in *.
    subst.
    apply decompose_stack_eq in decomp.
    unfold zip, zipp in *.
    destruct x; cbn in *.
    subst s.
    rewrite zipc_appstack.
    rewrite stack_context_appstack, decompose_stack_appstack in H.
    cbn in *.
    now rewrite app_nil_r in H.
  Qed.

  (** ** The machine computes [PCUICArityRed.whd_rel]

    With every flag on except possibly [zeta], the machine started on [t] and
    the stack [π] stops at the [whd_rel] form of [t] applied to the arguments
    of [π], in the context of [π]. *)

  Lemma whd_rel_fix_iota_app zeta (Σ : global_env) Γ mfix idx fn pre c post ind n ui cargs h l :
    unfold_fix mfix idx = Some (#|pre|, fn) ->
    whd_rel zeta Σ Γ c [] (tConstruct ind n ui) cargs ->
    whd_rel zeta Σ Γ fn (pre ++ mkApps (tConstruct ind n ui) cargs :: post) h l ->
    whd_rel zeta Σ Γ (tFix mfix idx) (pre ++ c :: post) h l.
  Proof using Type.
    intros hu hc hfn.
    eapply whd_fix_iota; [exact hu|apply nth_error_snoc; reflexivity|exact hc|].
    rewrite firstn_app_left by reflexivity.
    change (pre ++ c :: post) with (pre ++ [c] ++ post).
    rewrite (app_assoc pre [c] post).
    rewrite skipn_all_app_eq by (rewrite length_app; cbn; lia).
    exact hfn.
  Qed.

  Lemma whd_rel_fix_stuck_app zeta (Σ : global_env) Γ mfix idx fn pre c post t cargs :
    unfold_fix mfix idx = Some (#|pre|, fn) ->
    whd_rel zeta Σ Γ c [] t cargs -> whd_is_construct t = false ->
    whd_rel zeta Σ Γ (tFix mfix idx) (pre ++ c :: post)
      (tFix mfix idx) (pre ++ mkApps t cargs :: post).
  Proof using Type.
    intros hu hc ht.
    assert (e : pre ++ mkApps t cargs :: post =
      firstn #|pre| (pre ++ c :: post) ++ mkApps t cargs :: skipn (S #|pre|) (pre ++ c :: post)).
    { rewrite firstn_app_left by reflexivity.
      change (pre ++ c :: post) with (pre ++ [c] ++ post).
      rewrite (app_assoc pre [c] post).
      rewrite skipn_all_app_eq by (rewrite length_app; cbn; lia).
      reflexivity. }
    rewrite e.
    eapply whd_fix_stuck; [exact hu|apply nth_error_snoc; reflexivity|exact hc|exact ht].
  Qed.

  Lemma decompose_stack_App_l_fst a π :
    (decompose_stack (App_l a :: π)).1 = a :: (decompose_stack π).1.
  Proof using Type.
    cbn. now destruct (decompose_stack π).
  Qed.

  Lemma decompose_stack_appstack_App_l_fst args x ρ :
    (decompose_stack (appstack args (App_l x :: ρ))).1 = args ++ x :: (decompose_stack ρ).1.
  Proof using Type.
    rewrite decompose_stack_appstack. cbn. now destruct (decompose_stack ρ).
  Qed.

  Lemma decompose_stack_at_None_fst π n :
    decompose_stack_at π n = None -> nth_error (decompose_stack π).1 n = None.
  Proof using Type.
    intros h.
    destruct (decompose_stack π) as [l ρ] eqn:e. cbn.
    assert (hs : isStackApp ρ = false) by (eapply decompose_stack_noStackApp; exact e).
    apply decompose_stack_eq in e. subst π.
    exact (proj2 (decompose_stack_at_appstack_None l ρ n hs) h).
  Qed.

  Lemma red_discr_whd_stop_head t π :
    red_discr t π -> whd_stop_head t (decompose_stack π).1.
  Proof using Type.
    destruct t; cbn; try (intros; reflexivity); try (intros h; exact (False_rect _ h)).
    destruct π as [|[] π]; cbn; intros h; first [reflexivity|exact (False_rect _ h)].
  Qed.

  Lemma discr_construct_whd_is_construct t :
    discr_construct t -> whd_is_construct t = false.
  Proof using Type.
    destruct t; cbn; intros h; try reflexivity; exact (False_rect _ h).
  Qed.

  Lemma discr_construct_cofix_whd t :
    discr_construct_cofix t -> whd_is_construct t = false /\ whd_is_cofix t = false.
  Proof using Type.
    destruct t; cbn; intros h; try (split; reflexivity); exact (False_rect _ h).
  Qed.

  Lemma discr_construct0_cofix_whd t :
    discr_construct0_cofix t -> whd_is_construct0 t = false /\ whd_is_cofix t = false.
  Proof using Type.
    destruct t; cbn; intros h; try (split; reflexivity).
    - destruct n; [exact (False_rect _ (h eq_refl))|split; reflexivity].
    - exact (False_rect _ h).
  Qed.

  (** The term a discriminant reduces to is well typed in the position of the
      discriminant. *)
  Lemma reduce_discr_welltyped Σ (wfΣ : abstract_env_ext_rel X Σ) Γ c fr π t π' args ρ :
    isStackApp (fr :: π) = false ->
    wt Σ Γ (zip (c, fr :: π)) ->
    Req Σ Γ (t, π') (c, fr :: π) ->
    Pr (t, π') (fr :: π) ->
    (args, ρ) = decompose_stack π' ->
    wt Σ (Γ ,,, stack_context π) (fill_hole (mkApps t args) fr).
  Proof using TF hX.
    intros hs hwt r hpr hdec.
    assert (hd0 : decompose_stack (fr :: π) = ([], fr :: π)).
    { destruct fr; cbn in hs; try discriminate; reflexivity. }
    unfold Pr in hpr. cbn [snd] in hpr.
    rewrite hd0, <- hdec in hpr. cbn [snd] in hpr. subst ρ.
    symmetry in hdec. apply decompose_stack_eq in hdec. subst π'.
    destruct (hΣ _ wfΣ) as [wΣ].
    apply Req_red in r as [r].
    pose proof (red_wt Σ wΣ hwt r) as wt'.
    change (wt Σ Γ (zipc t (appstack args (fr :: π)))) in wt'.
    rewrite zipc_appstack in wt'.
    exact (wt_context Σ wΣ Γ (fill_hole (mkApps t args) fr, π) wt').
  Qed.

  Lemma reduce_stack_whd_rel
    (hbeta : RedFlags.beta flags) (hiota : RedFlags.iota flags)
    (hdelta : RedFlags.delta flags) (hfix : RedFlags.fix_ flags) :
    forall Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ),
      ∥ whd_rel (RedFlags.zeta flags) Σ.1 (Γ ,,, stack_context π) t
          (decompose_stack π).1 (fst (reduce_stack Γ t π h))
          (decompose_stack (snd (reduce_stack Γ t π h))).1 ∥.
  Proof using Type.
    intros Γ t π h Σ wfΣ.
    apply (reduce_stack_prop Γ t π h (fun x y =>
      ∥ whd_rel (RedFlags.zeta flags) Σ.1 (Γ ,,, stack_context (snd x)) (fst x)
          (decompose_stack (snd x)).1 (fst y) (decompose_stack (snd y)).1 ∥)).
    clear -wfΣ hbeta hiota hdelta hfix hX EF TF.
    intros t π h aux.
    apply_funelim (_reduce_stack Γ t π h aux); clear -wfΣ hbeta hiota hdelta hfix hX EF TF.
    all: intros *.
    all: repeat match goal with
      | [ |- (forall (t' : term) (π' : stack)
              (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ }) -> _ ] =>
          intros reduce
      | [ |- (forall (t' : term) (π' : stack)
              (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), _) -> _ ] =>
          intros haux
      | [ |- _ ] => intros ?
      end.
    all: try match goal with |- context [False_rect _ ?f] => destruct f end.
    all: cbn [fst snd proj1_sig] in *; try cbv zeta.
    (* The equations [inspect _ = _] of the elimination principle depend on the
       hypotheses that the branches rewrite; they are not needed. *)
    all: repeat match goal with H : inspect _ = _ |- _ => clear H end.
    (* The recursive call [rf] and its hypothesis [ha] are found by their types:
       a pattern under [all:] cannot name a local hypothesis. *)
    (* The discriminant of a fixpoint, a case or a projection: the machine's
       result on it, and for a case or a projection the typing of the term the
       discriminant reduced to. *)
    all: try match goal with
      | rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), ∥ _ ∥ |- _ =>
        match goal with
        | e : exist (?t0, ?π0) ?prf = rf ?c ?s ?z |- _ =>
          let hc := fresh "hc" in
          pose proof (ha c s z) as hc; rewrite <- e in hc;
          cbn [fst snd proj1_sig decompose_stack] in hc;
          repeat match goal with
            | e' : (_, _) = decompose_stack π0 |- _ =>
                match type of hc with context [decompose_stack π0] =>
                  rewrite <- e' in hc; cbn [fst snd] in hc end
            end;
          try match goal with
            | e' : (?args, ?ρ) = decompose_stack π0,
              hw : forall Σ, abstract_env_ext_rel X Σ -> wt Σ _ _ |- _ =>
                match s with
                | ?fr :: ?ρs =>
                  pose proof (reduce_discr_welltyped Σ wfΣ _ c fr ρs t0 π0 args ρ eq_refl
                    (hw Σ wfΣ) (proj1 (prf Σ wfΣ)) (proj1 (proj2 (prf Σ wfΣ))) e') as wtc
                end
            end
        end
      end.
    (* The recursive call that ends the branch. *)
    all: try match goal with
      | rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), ∥ _ ∥ |- _ =>
        match goal with
        | |- context [ rf ?x ?y ?z ] =>
          let hr := fresh "hr" in let er := fresh "er" in
          let tr := fresh "tr" in let πr := fresh "πr" in
          case_eq (rf x y z); pose proof (ha x y z) as hr;
          intros [tr πr] ? er; rewrite er in hr; cbn [fst snd proj1_sig] in hr |- *
        end
      end.
    (* The equations on machine results mention the branch's hypotheses through
       the obligations they carry; the closers below rewrite those hypotheses. *)
    all: repeat match goal with
      | H : exist _ _ = _ |- _ => clear H
      | H : _ = exist _ _ |- _ => clear H
      end.
    all: repeat match goal with H : ∥ _ ∥ |- _ => destruct H as [H] end.
    all: first
      [ exfalso; congruence
      (* tRel *)
      | constructor; eapply whd_rel_unfold;
        [symmetry; eassumption|symmetry; eassumption|eassumption]
      | constructor; eapply whd_rel_assum; [symmetry; eassumption|symmetry; eassumption]
      (* tLetIn *)
      | constructor; eapply whd_zeta; [assumption|eassumption]
      | constructor; apply whd_letin_stop; assumption
      (* tConst *)
      | constructor; eapply whd_delta;
        [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
        | reflexivity | eassumption ]
      | constructor; eapply whd_axiom;
        [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
        | reflexivity
        | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption ]
      (* a registered operation (design §7.2): one closer per leaf *)
      | match goal with
        | hsat : false = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π |- _ =>
          rewrite <- hπ; cbn [fst]; constructor; eapply whd_prim_partial;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_gt; symmetry; exact hsat ]
        end
      | match goal with
        | hd : None = prim_op_denote ?op ?ls, hs : inl ?ls = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π |- _ =>
          rewrite <- hπ; cbn [fst]; constructor; eapply whd_prim_inert;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | symmetry; exact hd ]
        end
      | match goal with
        | hd : Some ?r = prim_op_denote ?op ?ls, hv : Some ?v = abstract_readback _ ?r,
          hs : inl ?ls = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
          hr : whd_rel _ _ _ ?v _ _ _ |- _ =>
          let hρ := fresh "hρ" in
          pose proof (decompose_stack_twice _ _ _ (eq_sym hπ)) as hρ;
          assert (hctx : stack_context π = stack_context ρ)
            by (symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
                now rewrite stack_context_appstack);
          rewrite <- hπ; cbn [fst]; rewrite hctx;
          rewrite decompose_stack_appstack, hρ, stack_context_appstack in hr;
          cbn [fst] in hr; rewrite app_nil_r in hr;
          constructor; eapply whd_prim_fire;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | symmetry; exact hd
          | rewrite <- (abstract_readback_correct _ wfΣ); symmetry; exact hv
          | exact hr ]
        end
      | match goal with
        | hlit : Some _ = lit_of_term (mkApps ?t ?l),
          hs : inr (?ls, ?a, ?rest) = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
          hc : whd_rel _ _ (_ ,,, ?Δc) ?a _ ?t ?l,
          hr : whd_rel _ _ (_ ,,, ?Δr) (tConst _ _) _ _ _ |- _ =>
          let hρ := fresh "hρ" in
          pose proof (decompose_stack_twice _ _ _ (eq_sym hπ)) as hρ;
          assert (hctx : stack_context π = stack_context ρ)
            by (symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
                now rewrite stack_context_appstack);
          replace Δc with (stack_context ρ) in hc
            by (cbn; rewrite ?stack_context_appstack; reflexivity);
          replace Δr with (stack_context ρ) in hr
            by (rewrite ?stack_context_appstack; reflexivity);
          rewrite decompose_stack_appstack, hρ in hr; cbn [fst] in hr; rewrite app_nil_r in hr;
          rewrite <- hπ; cbn [fst]; rewrite hctx;
          constructor; eapply whd_prim_arg;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | exact hc
          | symmetry; exact hlit
          | exact hr ]
        end
      | match goal with
        | hlit : None = lit_of_term (mkApps ?t ?l),
          hs : inr (?ls, ?a, ?rest) = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
          hc : whd_rel _ _ (_ ,,, ?Δc) ?a _ ?t ?l |- _ =>
          let hρ := fresh "hρ" in
          pose proof (decompose_stack_twice _ _ _ (eq_sym hπ)) as hρ;
          assert (hctx : stack_context π = stack_context ρ)
            by (symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
                now rewrite stack_context_appstack);
          replace Δc with (stack_context ρ) in hc
            by (cbn; rewrite ?stack_context_appstack; reflexivity);
          rewrite <- hπ; cbn [fst]; rewrite hctx;
          rewrite decompose_stack_appstack, hρ; cbn [fst]; rewrite app_nil_r;
          constructor; eapply whd_prim_stuck;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | exact hc
          | symmetry; exact hlit ]
        end
      (* tApp *)
      | constructor; rewrite decompose_stack_App_l_fst in *; eapply whd_app; eassumption
      (* tLambda *)
      | constructor; rewrite decompose_stack_App_l_fst; eapply whd_beta; eassumption
      (* tFix *)
      | match goal with
        | e1 : Some (_, _) = unfold_fix _ _, e2 : Some (_, _, _) = decompose_stack_at ?π0 _ |- _ =>
            let hlen := fresh "hlen" in
            symmetry in e2;
            pose proof (decompose_stack_at_length _ _ _ _ _ e2) as hlen;
            apply decompose_stack_at_eq in e2; subst π0; subst;
            rewrite ?decompose_stack_appstack_App_l_fst, ?stack_context_appstack in *;
            constructor;
            first
              [ eapply whd_rel_fix_iota_app; [symmetry; exact e1|eassumption|eassumption]
              | eapply whd_rel_fix_stuck_app;
                [symmetry; exact e1|eassumption
                |apply discr_construct_whd_is_construct; assumption] ]
        end
      | match goal with
        | e1 : Some (_, _) = unfold_fix _ _, e2 : None = decompose_stack_at _ _ |- _ =>
            constructor; eapply whd_fix_noarg;
            [symmetry; exact e1|apply decompose_stack_at_None_fst; symmetry; exact e2]
        end
      | match goal with
        | e1 : None = unfold_fix _ _ |- _ =>
            constructor; apply whd_fix_nounfold; symmetry; exact e1
        end
      (* tCase on a constructor: the typing gives [ci_ind] and the argument count *)
      | match goal with
        | wtc : wt _ _ (fill_hole (mkApps (tConstruct ?ind' _ _) _) (Case_discr _ _ _)),
          eqbr : Some _ = nth_error _ _ |- _ =>
            let wΣ := fresh "wΣ" in
            let ei := fresh "ei" in let br' := fresh "br'" in
            let hbr := fresh "hbr" in let hlen := fresh "hlen" in
            cbn [fill_hole] in wtc;
            destruct (hΣ _ wfΣ) as [wΣ];
            destruct (rtf_case_construct _ _ _ _ _ _ _ _ _ wΣ wtc)
              as [ei [br' [hbr hlen]]];
            subst ind'; rewrite hbr in eqbr; noconf eqbr;
            constructor; eapply whd_iota; [eassumption|eassumption|eassumption|eassumption]
        end
      (* tProj on a constructor: the typing gives [proj_ind] *)
      | match goal with
        | wtc : wt _ _ (fill_hole (mkApps (tConstruct ?ind' _ _) _) (Proj _)) |- _ =>
            let wΣ := fresh "wΣ" in let ei := fresh "ei" in
            cbn [fill_hole] in wtc;
            destruct (hΣ _ wfΣ) as [wΣ];
            destruct (rtf_proj_construct _ _ _ _ _ _ _ wΣ wtc) as [ei _];
            subst ind';
            constructor; eapply whd_proj; [eassumption|symmetry; eassumption|eassumption]
        end
      (* cofixpoints and stuck discriminants *)
      | constructor; eapply whd_case_cofix; [eassumption|symmetry; eassumption|eassumption]
      | constructor; eapply whd_proj_cofix; [eassumption|symmetry; eassumption|eassumption]
      | match goal with
        | ht : discr_construct_cofix _ |- _ =>
            let h1 := fresh "h1" in let h2 := fresh "h2" in
            destruct (discr_construct_cofix_whd _ ht) as [h1 h2];
            constructor; eapply whd_case_stuck; eassumption
        end
      | match goal with
        | ht : discr_construct0_cofix _ |- _ =>
            let h1 := fresh "h1" in let h2 := fresh "h2" in
            destruct (discr_construct0_cofix_whd _ ht) as [h1 h2];
            constructor; eapply whd_proj_stuck; eassumption
        end
      (* every other head stops the machine *)
      | constructor; apply whd_stop; apply red_discr_whd_stop_head; assumption ].
  Qed.

  (** [reduce_term] is the [whd_rel] normal form, in applicative form. *)
  Theorem reduce_term_whd_rel
    (hbeta : RedFlags.beta flags) (hiota : RedFlags.iota flags)
    (hdelta : RedFlags.delta flags) (hfix : RedFlags.fix_ flags)
    Γ t h Σ (wfΣ : abstract_env_ext_rel X Σ) :
    exists hd l, reduce_term Γ t h = mkApps hd l /\
      ∥ whd_rel (RedFlags.zeta flags) Σ.1 Γ t [] hd l ∥.
  Proof using Type.
    unfold reduce_term.
    generalize (reduce_stack_whd_rel hbeta hiota hdelta hfix Γ t [] h Σ wfΣ)
      (reduce_stack_decompose Γ t [] h).
    destruct (reduce_stack Γ t [] h) as [u ρ]. cbn. intros w e.
    assert (eρ : ρ = appstack (decompose_stack ρ).1 []).
    { apply decompose_stack_eq. rewrite <- e. now destruct (decompose_stack ρ). }
    exists u, (decompose_stack ρ).1. split; [|exact w].
    transitivity (zipc u (appstack (decompose_stack ρ).1 [])).
    - f_equal. exact eρ.
    - exact (@zipc_appstack u (decompose_stack ρ).1 []).
  Qed.

End Reduce.

Section ReduceFns.

  Context {cf : checker_flags} {no : normalizing_flags}
          {wt : global_env_ext -> context -> term -> Prop} {wfP : global_env_ext -> Type}
          {EF : ReduceEnvFacts wt wfP} {TF : ReduceTypedFacts wt wfP}
          {X_type : abstract_env_impl} {X : X_type.π2.π1}
          {hX : AbstractEnvWf X_type X wfP}
          {normalization_in : forall Σ, wfP Σ -> Σ ∼_ext X -> NormalizationInWt wt Σ}.

  Local Definition hΣ' Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥ wfP Σ ∥ :=
    @abstract_env_wfP cf X_type X wfP hX Σ wfΣ.

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Definition hnf := @reduce_term cf no wt wfP EF TF RedFlags.default X_type X hX normalization_in.

  Theorem hnf_sound {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥ Σ ;;; Γ ⊢ t ⇝ hnf Γ t h ∥.
  Proof using Type.
    unfold hnf.
    destruct (reduce_term_sound RedFlags.default _ X _ _ h Σ wfΣ).
    sq. eapply into_closed_red; fvs.
  Defined.

  Theorem hnf_complete {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥whnf RedFlags.default Σ Γ (hnf Γ t h)∥.
  Proof using Type.
    apply reduce_term_complete; eauto.
  Qed.

  Equations? reduce_to_sort (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ t)
    : typing_result_comp (∑ u, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tSort u ∥) :=
    reduce_to_sort Γ t h with view_sortc t := {
      | view_sort_sort s => Checked_comp (s; _);
      | view_sort_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_sortc hnft := {
          | view_sort_sort s => Checked_comp (s; _);
          | view_sort_other hnft r => TypeError_comp (NotASort hnft) _
        }
      }.
  Proof using EF TF hX normalization_in.
    * pose proof (hw := h _ wfΣ).
      pose proof (hΣ := hΣ' _ wfΣ). sq.
      eapply into_closed_red; [reflexivity| |].
      + exact (ref_closed_context Σ Γ _ hΣ hw).
      + exact (ref_open_term Σ Γ _ hΣ hw).
    * pose proof (hnf_sound (h:=h)).
      now rewrite eq.
    * destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]. specialize (X1 _ wfΣ).
      pose proof (hΣ := hΣ' _ wfΣ). sq.
      destruct (ref_cb (wt := wt) Σ hΣ) as [cbΣ].
      edestruct (@hnf_complete Γ t h) as [wh]; eauto.
      edestruct (@hnf_sound Γ t h) as [r']; eauto.
      eapply closed_red_confluence_cb in X1 as (?&r1&r2); eauto.
      apply invert_red_sort_gen in r2 as ->.
      eapply (rtf_whnf_red_inv (wt := wt)) in r1; eauto. destruct r1 as [r1].
      depelim r1.
      rewrite H in r.
      now cbn in r.
  Qed.

  Lemma reduce_to_sort_complete {Γ t hwt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_sort Γ t hwt = TypeError_comp e p ->
    (forall s, red Σ Γ t (tSort s) -> False).
  Proof using Type.
    intros _ s r.
    apply p.
    exists s.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ' _ wfΣ). sq.
    eapply into_closed_red; [exact r| |].
    + exact (ref_closed_context Σ Γ t hΣ (hwt Σ wfΣ)).
    + exact (ref_open_term Σ Γ t hΣ (hwt Σ wfΣ)).
    Unshelve. eauto.
  Qed.

  Equations? reduce_to_prod (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ t)
    : typing_result_comp (∑ na a b, forall  Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tProd na a b ∥) :=
    reduce_to_prod Γ t h with view_prodc t := {
      | view_prod_prod na a b => Checked_comp (na; a; b; _);
      | view_prod_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_prodc hnft := {
          | view_prod_prod na a b => Checked_comp (na; a; b; _);
          | view_prod_other hnft _ => TypeError_comp (NotAProduct t hnft) _
        }
      }.
  Proof using EF TF hX normalization_in.
    * pose proof (hw := h _ wfΣ).
      pose proof (hΣ := hΣ' _ wfΣ). sq.
      eapply into_closed_red; [reflexivity| |].
      + exact (ref_closed_context Σ Γ _ hΣ hw).
      + exact (ref_open_term Σ Γ _ hΣ hw).
    * pose proof (hnf_sound (h:=h)).
      now rewrite eq.
    * destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (X3 _ wfΣ).
      sq.
      edestruct (@hnf_complete Γ t h) as [wh]; eauto.
      edestruct (@hnf_sound Γ t h) as [r']; eauto.
      destruct (hΣ' _ wfΣ) as [hΣ].
      destruct (ref_cb (wt := wt) Σ hΣ) as [cbΣ].
      eapply closed_red_confluence_cb in X3 as (?&r1&r2); eauto.
      apply invert_red_prod_cb in r2 as (?&?&[-> ? ?]); auto.
      eapply (rtf_whnf_red_inv (wt := wt)) in r1; eauto. destruct r1 as [r1].
      depelim r1.
      now rewrite H in n0.
  Qed.

  Lemma reduce_to_prod_complete {Γ t hwt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_prod Γ t hwt = TypeError_comp e p ->
    (forall na a b, red Σ Γ t (tProd na a b) -> False).
  Proof using Type.
    intros _ na a b r.
    apply p.
    exists na, a, b.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ' _ wfΣ). sq.
    eapply into_closed_red; [exact r| |].
    + exact (ref_closed_context Σ Γ t hΣ (hwt Σ wfΣ)).
    + exact (ref_open_term Σ Γ t hΣ (hwt Σ wfΣ)).
    Unshelve. eauto.
  Qed.

  Equations? reduce_to_ind (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ t)
    : typing_result_comp (∑ i u l, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ mkApps (tInd i u) l ∥) :=
    reduce_to_ind Γ t h with inspect (decompose_app t) := {
      | exist (thd, args) eq_decomp with view_indc thd := {
        | view_ind_tInd i u => Checked_comp (i; u; args; _);
        | view_ind_other thd _ with inspect (reduce_stack RedFlags.default _ X Γ t [] h) := {
          | exist (hnft, π) eq with view_indc hnft := {
            | view_ind_tInd i' u with inspect (decompose_stack π) := {
              | exist (l, _) eq_decomp' => Checked_comp (i'; u; l; _)
              };
            | view_ind_other _ _ => TypeError_comp (NotAnInductive t) _
            }
          }
        }
      }.
  Proof using EF TF hX normalization_in.
    - pose proof (hw := h _ wfΣ).
      assert (Xeq : mkApps (tInd i u) args = t).
      { etransitivity. 2: symmetry; eapply mkApps_decompose_app.
        now rewrite <- eq_decomp. }
      rewrite Xeq. pose proof (hΣ := hΣ' _ wfΣ); sq.
      eapply into_closed_red; [reflexivity| |].
      + exact (ref_closed_context Σ Γ _ hΣ hw).
      + exact (ref_open_term Σ Γ _ hΣ hw).
    - pose proof (reduce_stack_sound RedFlags.default _ X _ wfΣ _ _ [] h).
      rewrite <- eq in H.
      cbn in *.
      assert (π = appstack l []) as ->.
      2: { now rewrite zipc_appstack in H. }
      unfold reduce_stack in eq.
      edestruct reduce_stack_full as (?&_&stack_val&?); eauto.
      subst x.
      unfold Pr in stack_val.
      cbn in *.
      assert (decomp: decompose_stack π = ((decompose_stack π).1, [])).
      { rewrite stack_val.
        now destruct decompose_stack. }
      apply decompose_stack_eq in decomp as ->.
      now rewrite <- eq_decomp'.
    - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (X3 _ wfΣ).
      pose proof (hΣ := hΣ' _ wfΣ). sq.
      destruct (ref_cb (wt := wt) Σ hΣ) as [cbΣ].
      pose proof (ref_closed_context Σ Γ t hΣ (h Σ wfΣ)) as clΓ.
      pose proof (ref_open_term Σ Γ t hΣ (h Σ wfΣ)) as clt.
      pose proof (reduce_stack_whnf RedFlags.default _ X Γ t [] h _  wfΣ) as wh.
      unfold reduce_stack in *.
      edestruct reduce_stack_full as ((hd&π')&r'&stack_valid&(notapp&_)); eauto.
      destruct wh as [wh].
      apply Req_red in r' as [r'].
      unfold Pr in stack_valid.
      cbn in *.
      apply (fun r => into_closed_red r clΓ clt) in r'.
      eapply closed_red_confluence_cb in r' as (?&r1&r2).
      2 : exact X3.
      assert (exists args, π' = appstack args []) as (?&->).
      { exists ((decompose_stack π').1).
        assert (decomp: decompose_stack π' = ((decompose_stack π').1, [])).
        { now rewrite stack_valid; destruct decompose_stack; cbn. }
        now apply decompose_stack_eq in decomp. }
      unfold zipp in wh.
      rewrite stack_context_appstack, decompose_stack_appstack in wh.
      rewrite zipc_appstack in r2.
      cbn in *.
      rewrite app_nil_r in wh.
      eapply (rtf_whnf_red_inv (wt := wt)) in r2; eauto. destruct r2 as [r2].
      apply invert_red_mkApps_tInd_cb in r1 as (?&[-> _ ?]); auto.
      apply whnf_red_mkApps_inv in r2 as (?&?); auto.
      depelim w.
      noconf eq.
      discriminate i0.
  Qed.

  Lemma reduce_to_ind_complete  Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ty wat e p :
    reduce_to_ind Γ ty wat = TypeError_comp e p ->
    forall ind u args,
      red Σ Γ ty (mkApps (tInd ind u) args) ->
      False.
  Proof using Type.
    intros _ ind u args' r.
    apply p.
    exists ind, u, args'.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ' _ wfΣ). sq.
    eapply into_closed_red; [exact r| |].
    + exact (ref_closed_context Σ Γ ty hΣ (wat Σ wfΣ)).
    + exact (ref_open_term Σ Γ ty hΣ (wat Σ wfΣ)).
    Unshelve. eauto.
  Qed.

  (* Definition of assumption-only arities (without lets) *)
  Definition arity_ass := aname * term.

  Fixpoint mkAssumArity (l : list arity_ass) (s : sort) : term :=
    match l with
    | [] => tSort s
    | (na, A) :: l => tProd na A (mkAssumArity l s)
    end.

  Definition arity_ass_context := rev_map (fun '(na, A) => vass na A).

  Lemma assumption_context_arity_ass_context l :
    assumption_context (arity_ass_context l).
  Proof using Type.
    unfold arity_ass_context.
    rewrite rev_map_spec.
    induction l using MRList.rev_ind; cbn.
    - constructor.
    - rewrite map_app, rev_app_distr.
      cbn.
      destruct x.
      constructor; auto.
  Qed.

  Lemma mkAssumArity_it_mkProd_or_LetIn (l : list arity_ass) (s : sort) :
    mkAssumArity l s = it_mkProd_or_LetIn (arity_ass_context l) (tSort s).
  Proof using Type.
    unfold arity_ass_context.
    rewrite rev_map_spec.
    induction l; auto.
    cbn.
    destruct a.
    rewrite IHl, it_mkProd_or_LetIn_app; auto.
  Qed.

  Lemma isArity_mkAssumArity l s :
    isArity (mkAssumArity l s).
  Proof using Type.
    induction l as [|(na & A) l IH]; cbn; auto.
  Qed.

  Record conv_arity {Γ T} : Type :=
    build_conv_arity {
        conv_ar_context : list arity_ass;
        conv_ar_univ : sort;
        conv_ar_red : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ T ⇝ mkAssumArity conv_ar_context conv_ar_univ ∥
      }.

  Global Arguments conv_arity : clear implicits.

  Lemma conv_arity_Is_conv_to_Arity {Γ T} :
    is_closed_context Γ ->
    is_open_term Γ T ->
    conv_arity Γ T ->
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), Is_conv_to_Arity Σ Γ T.
  Proof using Type.
    intros clΓ clT [asses univ r] Σ wfΣ.
    eexists. destruct (r _ wfΣ). split; [sq|]; tea.
    apply isArity_mkAssumArity.
  Qed.

  Lemma isArity_red Σ Γ u v :
    isArity u ->
    red Σ Γ u v ->
    isArity v.
  Proof using Type.
    intros arity_u r.
    induction r using red_rect_n1; [easy|].
    eapply isArity_red1; eassumption.
  Qed.

  Lemma Is_conv_to_Arity_red Σ {wfΣ : ClosedBodies Σ} Γ T T' :
    Is_conv_to_Arity Σ Γ T ->
    Σ ;;; Γ ⊢ T ⇝ T' ->
    Is_conv_to_Arity Σ Γ T'.
  Proof using Type.
    unfold Is_conv_to_Arity.
    intros [T'' (redT'' & is_arity)] red.
    sq.
    destruct (closed_red_confluence_cb red redT'') as (a & reda' & reda'').
    exists a.
    split; [easy|].
    clear -is_arity reda''.
    eapply isArity_red; eauto. exact reda''.
  Qed.

  Local Instance wellfounded Σ wfΣ {normalization : NormalizationInWt wt Σ} :
    WellFounded (hnf_subterm_rel (wt := wt) (Σ := Σ)) :=
    wf_hnf_subterm (WR := rtf_wt_red) (normalization := normalization) (HΣ := hΣ' Σ wfΣ).

End ReduceFns.
