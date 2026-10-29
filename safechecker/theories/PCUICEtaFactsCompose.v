(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICNormal PCUICReduction PCUICPosition
     PCUICWellScopedCumulativity PCUICTypingEta PCUICGlobalEnvEta PCUICClosedTypEta PCUICWellScopedCumulativityEta
     PCUICContextConversionEta.
From MetaRocq.SafeChecker Require Import PCUICWfReductionEta PCUICSafeReduceEta PCUICSafeConversionEtaFacts
  PCUICTypingEtaDefs PCUICTypingEtaHyps.
From MetaRocq.SafeChecker Require PCUICSafeReduceEtaBridge.
(* Last: [zip], [stack_context], [no_Eta_arg] below are the η stack's (the text of EtaPosK4's hypothesis);
   the base stack of [ReduceTypedFactsE] is written [PCUICPosition.*]. *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.

(** * ETAK (EtaK7): the E hypotheses at the composition, without the five repeats

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29. Five named hypotheses of the composed E checker repeat a
  fact that another named hypothesis states (EtaHypProve's audit C §4.2; its lemmas [hyp_dup_*], Qed'd in
  [PCUICTypingEtaHypsProved] @ [29c23129], are restated here, proofs unchanged except for the names of
  this branch). This file supplies each repeat from the hypothesis it repeats, by builder instances whose
  premises are bundle classes, so each fact is assumed once:
  - [WtRed welltypedE wf_extE] (subject reduction, row T1) from [EtaFacts]'s T1 [subject_reduction];
  - [rtf_whnf_red_invE] from [EtaFacts]'s U [whnf_red_inv];
  - [rtf_contextE] (REDUCE, base stacks) and [ctf_contextE] (CONV) from EtaPosK4's [welltypedE_context]
    (the class [WelltypedEContextE] below carries it, same name and statement);
  - [closed_context_conversionE] (EtaPosK4/EtaConv/the oracle) from [EtaFacts]'s T0
    [closed_context_cumulativity] ([closed_context_conversionE_of_facts], squashed for the oracle).
  [ReduceTypedFactsE] is then BUILT ([reduce_typed_facts_E_of_core]) from its six other fields (the class
  [ReduceTypedFactsCoreE], same statements) and the two classes above. The machine and the checker copies
  are unchanged; only the composition (the forecast entry point) binds these classes instead.
  Everything here is a Prop: extraction erases it. *)

(** ** The embedding of base stacks ([PCUICPosition]) into η stacks ([PCUICPositionEta]), EtaHypProve's *)
Definition hyp_eta_def_hole (h : PCUICPosition.def_hole) : PCUICPositionEta.def_hole :=
  match h with
  | PCUICPosition.def_hole_type na b r => PCUICPositionEta.def_hole_type na b r
  | PCUICPosition.def_hole_body na t r => PCUICPositionEta.def_hole_body na t r
  end.

Definition hyp_eta_mfix_hole (m : PCUICPosition.mfix_hole) : PCUICPositionEta.mfix_hole :=
  let '(m1, h, m2) := m in (m1, hyp_eta_def_hole h, m2).

Definition hyp_eta_predicate_hole (p : PCUICPosition.predicate_hole) : PCUICPositionEta.predicate_hole :=
  match p with
  | PCUICPosition.pred_hole_params p1 p2 u ctx r => PCUICPositionEta.pred_hole_params p1 p2 u ctx r
  | PCUICPosition.pred_hole_return ps u ctx => PCUICPositionEta.pred_hole_return ps u ctx
  end.

Definition hyp_eta_branches_hole (b : PCUICPosition.branches_hole) : PCUICPositionEta.branches_hole :=
  let '(b1, h, b2) := b in
  (b1, match h with PCUICPosition.branch_hole_body c => PCUICPositionEta.branch_hole_body c end, b2).

Definition hyp_eta_stack_entry (se : PCUICPosition.stack_entry) : PCUICPositionEta.stack_entry :=
  match se with
  | PCUICPosition.App_l v => PCUICPositionEta.App_l v
  | PCUICPosition.App_r u => PCUICPositionEta.App_r u
  | PCUICPosition.Prim_app c u op d => PCUICPositionEta.Prim_app c u op d
  | PCUICPosition.Fix_app mfix idx args => PCUICPositionEta.Fix_app mfix idx args
  | PCUICPosition.Fix m idx => PCUICPositionEta.Fix (hyp_eta_mfix_hole m) idx
  | PCUICPosition.CoFix_app mfix idx args => PCUICPositionEta.CoFix_app mfix idx args
  | PCUICPosition.CoFix m idx => PCUICPositionEta.CoFix (hyp_eta_mfix_hole m) idx
  | PCUICPosition.Case_pred ci p c brs => PCUICPositionEta.Case_pred ci (hyp_eta_predicate_hole p) c brs
  | PCUICPosition.Case_discr ci p brs => PCUICPositionEta.Case_discr ci p brs
  | PCUICPosition.Case_branch ci p c brs => PCUICPositionEta.Case_branch ci p c (hyp_eta_branches_hole brs)
  | PCUICPosition.Proj p => PCUICPositionEta.Proj p
  | PCUICPosition.Prod_l na B => PCUICPositionEta.Prod_l na B
  | PCUICPosition.Prod_r na A => PCUICPositionEta.Prod_r na A
  | PCUICPosition.Lambda_ty na b => PCUICPositionEta.Lambda_ty na b
  | PCUICPosition.Lambda_bd na A => PCUICPositionEta.Lambda_bd na A
  | PCUICPosition.LetIn_bd na B t => PCUICPositionEta.LetIn_bd na B t
  | PCUICPosition.LetIn_ty na b t => PCUICPositionEta.LetIn_ty na b t
  | PCUICPosition.LetIn_in na b B => PCUICPositionEta.LetIn_in na b B
  | PCUICPosition.PrimArray_ty l v d => PCUICPositionEta.PrimArray_ty l v d
  | PCUICPosition.PrimArray_def l v ty => PCUICPositionEta.PrimArray_def l v ty
  | PCUICPosition.PrimArray_val l bef aft d ty => PCUICPositionEta.PrimArray_val l bef aft d ty
  end.

Ltac hyp_destruct_holes :=
  repeat match goal with
  | m : PCUICPosition.mfix_hole |- _ => destruct m as [[? []] ?]
  | p : PCUICPosition.predicate_hole |- _ => destruct p
  | b : PCUICPosition.branches_hole |- _ => destruct b as [[? []] ?]
  end.

Lemma hyp_eta_fill_hole t se :
  PCUICPositionEta.fill_hole t (hyp_eta_stack_entry se) = PCUICPosition.fill_hole t se.
Proof. destruct se; hyp_destruct_holes; reflexivity. Qed.

Lemma hyp_eta_stack_entry_context se :
  PCUICPositionEta.stack_entry_context (hyp_eta_stack_entry se) = PCUICPosition.stack_entry_context se.
Proof. destruct se; hyp_destruct_holes; reflexivity. Qed.

Lemma hyp_eta_zipc t π :
  PCUICPositionEta.zipc t (map hyp_eta_stack_entry π) = PCUICPosition.zipc t π.
Proof.
  induction π as [|se π IH] in t |- *; [reflexivity|].
  cbn [map PCUICPositionEta.zipc PCUICPosition.zipc]. rewrite hyp_eta_fill_hole. apply IH.
Qed.

Lemma hyp_eta_stack_context π :
  PCUICPositionEta.stack_context (map hyp_eta_stack_entry π) = PCUICPosition.stack_context π.
Proof.
  induction π as [|se π IH]; [reflexivity|].
  rewrite /PCUICPositionEta.stack_context /PCUICPosition.stack_context /= in IH |- *.
  rewrite hyp_eta_stack_entry_context IH. reflexivity.
Qed.

Lemma hyp_eta_no_Eta_arg π : PCUICPositionEta.no_Eta_arg (map hyp_eta_stack_entry π).
Proof.
  induction π as [|se π IH]; [reflexivity|].
  cbn [map PCUICPositionEta.no_Eta_arg]. rewrite IH. destruct se; reflexivity.
Qed.

(** ** The repeated facts, derived (EtaHypProve's [hyp_dup_*]) *)

Lemma hyp_dup_rtf_wt_red {cf : checker_flags} {H1 : T1_facts} : WtRed welltypedE wf_extE.
Proof.
  intros Σ Γ u v wfΣ [T h] r. exists T.
  exact (subject_reduction Σ Γ u v T (wf_extE_wfE Σ wfΣ) h r).
Qed.

Lemma hyp_dup_rtf_whnf_red_inv {cf : checker_flags} {HU : U_facts} :
  forall Σ Γ t t', wf_extE Σ ->
    whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> ∥ whnf_red Σ Γ t t' ∥.
Proof.
  intros Σ Γ t t' wfΣ hw r. constructor. exact (whnf_red_inv Γ t t' (wf_extE_wfE Σ wfΣ) hw r).
Qed.

Lemma hyp_dup_closed_context_conversionE {cf : checker_flags} {H0 : T0_facts} :
  forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T.
Proof.
  intros Σ wfΣ Γ t T Γ' h wfΓ' c.
  exact (closed_context_cumulativity (wfΣ := wfΣ) Γ h wfΓ'
           (ws_cumul_ctx_pbE_sym (wfΣ := wfE_ClosedBodies Σ) c)).
Qed.

Lemma hyp_dup_ctf_context {cf : checker_flags}
  (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    PCUICPositionEta.no_Eta_arg (snd t) -> welltypedE Σ Γ (PCUICPositionEta.zip t) ->
    welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context (snd t)) (fst t)) :
  forall Σ Γ t π, wf_extE Σ -> PCUICPositionEta.no_Eta_arg π ->
    welltypedE Σ Γ (PCUICPositionEta.zipc t π) -> welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context π) t.
Proof.
  intros Σ Γ t π wfΣ hna h. exact (welltypedE_context Σ (wf_extE_wfE Σ wfΣ) Γ (t, π) hna h).
Qed.

Lemma hyp_dup_rtf_context {cf : checker_flags}
  (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    PCUICPositionEta.no_Eta_arg (snd t) -> welltypedE Σ Γ (PCUICPositionEta.zip t) ->
    welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context (snd t)) (fst t)) :
  forall Σ Γ (t : term × PCUICPosition.stack), wf_extE Σ ->
    welltypedE Σ Γ (PCUICPosition.zip t) -> welltypedE Σ (Γ ,,, PCUICPosition.stack_context (snd t)) (fst t).
Proof.
  intros Σ Γ [t π] wfΣ h. cbn [fst snd] in h |- *.
  rewrite -hyp_eta_stack_context.
  apply (welltypedE_context Σ (wf_extE_wfE Σ wfΣ) Γ (t, map hyp_eta_stack_entry π) (hyp_eta_no_Eta_arg π)).
  rewrite /PCUICPositionEta.zip /= hyp_eta_zipc. exact h.
Qed.

(** ** The two classes the composition binds *)

(** EtaPosK4's named hypothesis [welltypedE_context] ([PCUICPositionEtaTyping], section [EtaTypingE]), as a
    class: same name, same statement (it stays counted there, once). *)
Class WelltypedEContextE {cf : checker_flags} : Prop := {
  welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    no_Eta_arg (snd t) -> welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t) }.

(** The six fields of [ReduceTypedFactsE] that nothing else states (same statements, names [rtfc_*]). *)
Class ReduceTypedFactsCoreE {cf : checker_flags} : Prop := {
  rtfc_case_construct : forall Σ Γ ci p ind' i u brs args, wf_extE Σ ->
    welltypedE Σ Γ (tCase ci p (mkApps (tConstruct ind' i u) args) brs) ->
    ci.(ci_ind) = ind' /\
    exists br, nth_error brs i = Some br /\
      (#|args| = ci.(ci_npar) + context_assumptions br.(bcontext))%nat;
  rtfc_proj_construct : forall Σ Γ p i' c u l, wf_extE Σ ->
    welltypedE Σ Γ (tProj p (mkApps (tConstruct i' c u) l)) ->
    p.(proj_ind) = i' /\ c = 0 /\ (p.(proj_npars) + p.(proj_arg) < #|l|)%nat;
  rtfc_prim_overapplied : forall Σ Γ c u op args, wf_extE Σ ->
    prim_op_of Σ c = Some op -> (arity op < #|args|)%nat ->
    welltypedE Σ Γ (mkApps (tConst c u) args) -> False;
  rtfc_fix_arg_whne : forall flags Σ Γ mfix idx body t before args aftr, wf_extE Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    welltypedE Σ Γ (mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr)) ->
    ∥ whne flags Σ Γ (mkApps t args) ∥;
  rtfc_case_arg_whne : forall flags Σ Γ hd args ci p brs, wf_extE Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    welltypedE Σ Γ (tCase ci p (mkApps hd args) brs) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥;
  rtfc_proj_arg_whne : forall flags Σ Γ hd args p, wf_extE Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    welltypedE Σ Γ (tProj p (mkApps hd args)) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥ }.

(** ** The builders (premises: bundle classes only) *)

#[export] Instance wt_red_E_of_facts {cf : checker_flags} {EF : EtaFacts} : WtRed welltypedE wf_extE.
Proof. destruct (@eta_T1 _ EF) as [H1]. exact (@hyp_dup_rtf_wt_red cf H1). Qed.

#[export] Instance reduce_typed_facts_E_of_core {cf : checker_flags} {C : ReduceTypedFactsCoreE}
  {EF : EtaFacts} {WC : WelltypedEContextE} : ReduceTypedFactsE.
Proof.
  constructor.
  - exact wt_red_E_of_facts.
  - exact (hyp_dup_rtf_context (@welltypedE_context cf WC)).
  - exact rtfc_case_construct.
  - exact rtfc_proj_construct.
  - exact rtfc_prim_overapplied.
  - exact rtfc_fix_arg_whne.
  - exact rtfc_case_arg_whne.
  - exact rtfc_proj_arg_whne.
  - destruct (@eta_U _ EF) as [HU]. exact (@hyp_dup_rtf_whnf_red_inv cf HU).
Qed.

#[export] Instance conv_typed_facts_E_of_ctx {cf : checker_flags} {WC : WelltypedEContextE} : ConvTypedFactsE.
Proof. constructor. exact (hyp_dup_ctf_context (@welltypedE_context cf WC)). Qed.

(** The oracle's [closed_context_conversionE] (squashed) from [EtaFacts]'s T0. *)
Lemma closed_context_conversionE_of_facts {cf : checker_flags} {EF : EtaFacts} :
  ∥ forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T ∥.
Proof. destruct (@eta_T0 _ EF) as [H0]. constructor. exact (@hyp_dup_closed_context_conversionE cf H0). Qed.

(** ** Satisfying instances of the two new classes' fields (the same concrete points as before)

  [ReduceTypedFactsCoreE]'s fields are fields of [ReduceTypedFactsE] under new names: their instances are
  EtaReduce's ([PCUICSafeReduceEtaBridge], restated for the small fields). [rtfc_prim_overapplied] has
  none by design (premise unsatisfiable; argument at [PCUICSafeReduceEta.ReduceTypedFacts]).
  [WelltypedEContextE.welltypedE_context] is EtaPosK4's hypothesis (same name and statement). EtaPosK4's
  instance [PCUICPositionEtaTyping.welltyped_context_inst] is at base [welltyped]/[wf] and does NOT discharge
  the [welltypedE] instantiation (row T6 remains); the concrete E instance is [welltypedE_context_inst]
  below. *)
(* Tags (the lane's convention; "non-degenerate" here: the instance has the head the field is about, in a typed
   term; see lanes/eta/etak/instance-coverage-9c6bdd2a.md). *)
(* non-degenerate *)
Definition rtfc_case_construct_inst := PCUICSafeReduceEtaBridge.rtf_case_constructE_inst.
(* non-degenerate *)
Definition rtfc_proj_construct_inst := PCUICSafeReduceEtaBridge.rtf_proj_constructE_inst.
(* non-degenerate *)
Definition rtfc_fix_arg_whne_inst := PCUICSafeReduceEtaBridge.rtf_fix_arg_whneE_inst.
(* non-degenerate *)
Definition rtfc_case_arg_whne_inst := PCUICSafeReduceEtaBridge.rtf_case_arg_whneE_inst.
(* non-degenerate *)
Definition rtfc_proj_arg_whne_inst := PCUICSafeReduceEtaBridge.rtf_proj_arg_whneE_inst.
(* [rtfc_prim_overapplied]: degenerate: IMPOSSIBLE — the field concludes [False] from a typed term whose head is
   a registered operation applied to more than its arity; by the typing rules the saturated application has the
   operation's result type (an inductive or a primitive type constant, never a product), and the E cumulativity
   relates neither to a product (PCUICEtaA6.v:176-316), so no environment and term satisfy the premises. The
   argument is on the head and the rule set; it is EtaReduce's, at [PCUICSafeReduceEta.ReduceTypedFacts]. *)

(* degenerate: NOT BUILT — the stack is empty, so the instance does not exercise a frame; a non-degenerate point
   needs a typed term under a binder frame at E (e.g. [Prod_r] with its context entry). COST: one base typing
   derivation of a product in [si_Σ], lifted by [typing_incl_E], about 20 lines. *)
(** [welltypedE_context] (T6) at E, concrete (the FRAC convention of [PCUICSafeReduceEtaBridge]: premises ×
    conclusion, every premise proved): the empty η stack in the bridge's [si_Σ]. *)
Section WelltypedEContextInst.
  #[local] Existing Instance default_checker_flags.
  Lemma welltypedE_context_inst :
    wfE (PCUICSafeReduceEtaBridge.SI.si_Σ).1 ×
    no_Eta_arg (snd (PCUICSafeReduceEtaBridge.SI.si_P, @nil stack_entry)) ×
    welltypedE PCUICSafeReduceEtaBridge.SI.si_Σ [] (zip (PCUICSafeReduceEtaBridge.SI.si_P, @nil stack_entry)) ×
    welltypedE PCUICSafeReduceEtaBridge.SI.si_Σ
      ([] ,,, stack_context (snd (PCUICSafeReduceEtaBridge.SI.si_P, @nil stack_entry)))
      (fst (PCUICSafeReduceEtaBridge.SI.si_P, @nil stack_entry)).
  Proof.
    split; [exact (wf_extE_wfE _ PCUICSafeReduceEtaBridge.si_wf_extE)|].
    split; [reflexivity|]. split; exact PCUICSafeReduceEtaBridge.si_P_wtE.
  Qed.
End WelltypedEContextInst.
