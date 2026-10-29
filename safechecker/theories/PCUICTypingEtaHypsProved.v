(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICPrimitive PCUICLiftSubst PCUICUnivSubst
     PCUICSigmaCalculus PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosed PCUICTyping PCUICCumulativity
     PCUICCumulativitySpec PCUICWellScopedCumulativity PCUICContextSubst PCUICCases PCUICNormal PCUICPosition
     PCUICConversion PCUICFixWitness PCUICWfUniverses PCUICClosedBodies PCUICSpine PCUICWeakeningEnv
     PCUICInductiveInversion PCUICContextConversionTyp PCUICRenameDef
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind
     PCUICEtaA6More PCUICGlobalEnvEta
     PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWsCumulEtaCtx
     PCUICWeakeningTypEta PCUICRenameTypEta PCUICInstDefEta PCUICInstTypEta PCUICCasesWfTypEta PCUICGuardClosureEta
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution PCUICSR PCUICInduction PCUICPositionEta
  PCUICInstConv PCUICContexts PCUICWeakeningConv.
From Stdlib Require Import Program.Equality.
From MetaRocq.SafeChecker Require Import PCUICWfReductionEta PCUICSafeReduceEta PCUICTypingEtaDefs
  PCUICTypingEtaHyps.
(* The eight lemmas of the REDUCE and ConvTypedFacts rows and the universe helpers of row 36 are in
   [PCUICEtaTypedFactsProved] (moved by EtaIntegrate9, same names and statements); imported here. *)
From MetaRocq.SafeChecker Require Import PCUICEtaTypedFactsProved.

(** * ETAK (EtaHypProve): the PROVABLE-NOW named hypotheses of the E bundles, proved

  BET-64 EtaCheckerLane, worker EtaHypProve, 2026-10-29. Audit [lanes/eta/etak/hyp-audit-C.md] classified
  56 of the 112 named hypotheses of the E checker's bundles as PROVABLE NOW; EtaHypProve proved all 56
  ([fork/wip/etak-hypprove-2026-10-29] @ [29c23129]).

  PRUNED on the forecast tree [fc/etak-forecast1]: EtaK7 integrated the 47 K7 rows (T0 37, U 8, T1 1,
  T6BD 1), with their helpers, into [PCUICTypingEtaHyps] (section "PROVED rows"), where those fields became
  lemmas; their [<field>_fits] checks no longer typecheck there (a field is no longer a projection; first
  error at the former line 167, [All_mfix_wf_fits]: "The term H has type T0_facts while it is expected to
  have type global_env * universes_decl"), so they are removed. EtaIntegrate9 moved the 8 lemmas of the
  REDUCE and ConvTypedFacts rows ([rtf_{rel,const,cofix,app_sort,app_prod,app_prim}_proved],
  [ctf_{case_brs_length,wf_universes}_proved]) to [PCUICEtaTypedFactsProved] (imported above). This file keeps:
  - the identity checks [<field>_fits] of those 8 rows: REDUCE (6), fields of [ReduceTypedFacts]
    ([PCUICSafeReduceEta]) at [wt := welltypedE], [wfP := wf_extE]; EtaConv (2), fields of [ConvTypedFacts]
    ([PCUICSafeConversionEtaFacts] @ [c7cbbe73]) at the same instantiation;
  - EtaPosK4 (1): [typingE_rename_P_proved] and its check ([PCUICPositionEtaTyping] @ [767d50c6]);
  - the section "Duplicate GENUINE hypotheses" ([hyp_dup_*], conditional lemmas, with its helpers [hyp_eta_*]).
  Identity check, by the type checker: [<field>_fits] ascribes the lemma to the field's type as projected from
  its class ([type of (@field cf H)]); for the sources not in this branch ([ConvTypedFacts], [EtaTypingE])
  [<field>_fits] restates the source text and is defined as the lemma.
  [Print Assumptions] of the 9 lemmas at the end. [depelim] is Equations' ([DepElim.depelim]). *)

(** ** REDUCE: fields of [ReduceTypedFacts] ([PCUICSafeReduceEta]) at [wt := welltypedE], [wfP := wf_extE]
    (the named hypothesis [PCUICSafeReduceEtaBridge.reduce_factsE]). The six lemmas [rtf_*_proved] are in
    [PCUICEtaTypedFactsProved] (moved by EtaIntegrate9); their identity checks stay here. *)

Definition rtf_rel_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_rel cf welltypedE wf_extE H) in exact T) := @rtf_rel_proved cf.

Definition rtf_const_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_const cf welltypedE wf_extE H) in exact T) := @rtf_const_proved cf.

Definition rtf_cofix_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_cofix cf welltypedE wf_extE H) in exact T) := @rtf_cofix_proved cf.

Definition rtf_app_sort_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_sort cf welltypedE wf_extE H) in exact T) := @rtf_app_sort_proved cf.

Definition rtf_app_prod_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_prod cf welltypedE wf_extE H) in exact T) := @rtf_app_prod_proved cf.

Definition rtf_app_prim_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_prim cf welltypedE wf_extE H) in exact T) := @rtf_app_prim_proved cf.

(** ** EtaConv: field [ctf_case_brs_length] of [ConvTypedFacts] ([PCUICSafeConversionEtaFacts] @ [c7cbbe73],
    not in this branch) at [wt := welltypedE], [wfP := wf_extE] (the hypothesis [conv_factsE]). The lemma is
    in [PCUICEtaTypedFactsProved] (moved by EtaIntegrate9). *)

Definition ctf_case_brs_length_fits {cf : checker_flags} :
  forall Σ Γ ci p c brs, wf_extE Σ -> welltypedE Σ Γ (tCase ci p c brs) ->
      exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|
  := @ctf_case_brs_length_proved cf.

(** ** EtaPosK4: section variable [typingE_rename_P] of [EtaTypingE] ([PCUICPositionEtaTyping] @ [767d50c6],
    not in this branch) *)

Lemma typingE_rename_P_proved {cf : checker_flags} :
  forall P (Σ : global_env_ext) Γ Δ f t A, wfE Σ.1 ->
    wf_localE Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f ->
    Σ ;;; Γ |-E t : A -> Σ ;;; Δ |-E rename f t : rename f A.
Proof.
  intros P Σ Γ Δ f t A wfΣ hr h. exact (typing_rename_PE (wfΣ := wfΣ) hr h).
Qed.
Definition typingE_rename_P_fits {cf : checker_flags} :
  forall P (Σ : global_env_ext) Γ Δ f t A, wfE Σ.1 ->
    wf_localE Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f ->
    Σ ;;; Γ |-E t : A -> Σ ;;; Δ |-E rename f t : rename f A
  := @typingE_rename_P_proved cf.

(** ** EtaConv: field [ctf_wf_universes] of [ConvTypedFacts] ([PCUICSafeConversionEtaFacts] @ [c7cbbe73]); the
    lemma is in [PCUICEtaTypedFactsProved]. *)
Definition ctf_wf_universes_fits {cf : checker_flags} :
  forall Σ Γ t, wf_extE Σ -> welltypedE Σ Γ t -> wf_universes Σ t := @ctf_wf_universes_proved cf.

(** ** Duplicate GENUINE hypotheses (audit C §4.2): each derivation below obtains one GENUINE hypothesis
    from ONE GENUINE hypothesis of another file, by glue only (instantiation, [wf_extE_wfE], a squash,
    the proved symmetry [ws_cumul_ctx_pbE_sym], the embedding of base stacks into η stacks). These are
    conditional lemmas: their premise stays a hypothesis. They show which hypotheses repeat a fact
    stated elsewhere; the repeated one disappears when the other is proved. *)

(** K7 T1 [subject_reduction] gives REDUCE [rtf_wt_red] (the field [WtRed welltypedE wf_extE]). *)
Lemma hyp_dup_rtf_wt_red {cf : checker_flags} {H1 : T1_facts} : WtRed welltypedE wf_extE.
Proof.
  intros Σ Γ u v wfΣ [T h] r. exists T.
  exact (subject_reduction Σ Γ u v T (wf_extE_wfE Σ wfΣ) h r).
Qed.
Definition hyp_dup_rtf_wt_red_fits {cf : checker_flags} (H1 : T1_facts)
  (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_wt_red cf welltypedE wf_extE H) in exact T) := @hyp_dup_rtf_wt_red cf H1.

(** K7 U [whnf_red_inv] gives REDUCE [rtf_whnf_red_inv]. *)
Lemma hyp_dup_rtf_whnf_red_inv {cf : checker_flags} {HU : U_facts} :
  forall Σ Γ t t', wf_extE Σ ->
    whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> ∥ whnf_red Σ Γ t t' ∥.
Proof.
  intros Σ Γ t t' wfΣ hw r. constructor. exact (whnf_red_inv Γ t t' (wf_extE_wfE Σ wfΣ) hw r).
Qed.
Definition hyp_dup_rtf_whnf_red_inv_fits {cf : checker_flags} (HU : U_facts)
  (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_whnf_red_inv cf welltypedE wf_extE H) in exact T) :=
  @hyp_dup_rtf_whnf_red_inv cf HU.

(** K7 T0 [closed_context_cumulativity] at [Conv] with [ws_cumul_ctx_pbE_sym] gives EtaPosK4's
    [closed_context_conversionE] (statement text of [PCUICPositionEtaTyping] @ [767d50c6]). *)
Lemma hyp_dup_closed_context_conversionE {cf : checker_flags} {H0 : T0_facts} :
  forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T.
Proof.
  intros Σ wfΣ Γ t T Γ' h wfΓ' c.
  exact (closed_context_cumulativity (wfΣ := wfΣ) Γ h wfΓ'
           (ws_cumul_ctx_pbE_sym (wfΣ := wfE_ClosedBodies Σ) c)).
Qed.

(** EtaPosK4's [welltypedE_context] (η stack of [PCUICPositionEta]; its text, names qualified) gives
    EtaConv's [ctf_context] at [wt := welltypedE], [wfP := wf_extE] ([PCUICSafeConversionEtaFacts] @
    [c7cbbe73], names qualified). *)
Lemma hyp_dup_ctf_context {cf : checker_flags}
  (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    PCUICPositionEta.no_Eta_arg (snd t) -> welltypedE Σ Γ (PCUICPositionEta.zip t) ->
    welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context (snd t)) (fst t)) :
  forall Σ Γ t π, wf_extE Σ -> PCUICPositionEta.no_Eta_arg π ->
    welltypedE Σ Γ (PCUICPositionEta.zipc t π) -> welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context π) t.
Proof.
  intros Σ Γ t π wfΣ hna h. exact (welltypedE_context Σ (wf_extE_wfE Σ wfΣ) Γ (t, π) hna h).
Qed.

(** The embedding of base stacks ([PCUICPosition]) into η stacks ([PCUICPositionEta], the same frames
    plus [Eta_app] and [Eta_arg]): it commutes with [zipc] and [stack_context] and has no [Eta_arg]. *)
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

(** EtaPosK4's [welltypedE_context] gives REDUCE [rtf_context] (base stack), through the embedding. *)
Lemma hyp_dup_rtf_context {cf : checker_flags}
  (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    PCUICPositionEta.no_Eta_arg (snd t) -> welltypedE Σ Γ (PCUICPositionEta.zip t) ->
    welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context (snd t)) (fst t)) :
  forall Σ Γ (t : term × stack), wf_extE Σ ->
    welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t).
Proof.
  intros Σ Γ [t π] wfΣ h. cbn [fst snd] in h |- *.
  rewrite -hyp_eta_stack_context.
  apply (welltypedE_context Σ (wf_extE_wfE Σ wfΣ) Γ (t, map hyp_eta_stack_entry π) (hyp_eta_no_Eta_arg π)).
  rewrite /PCUICPositionEta.zip /= hyp_eta_zipc. exact h.
Qed.
Definition hyp_dup_rtf_context_fits {cf : checker_flags}
  (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    PCUICPositionEta.no_Eta_arg (snd t) -> welltypedE Σ Γ (PCUICPositionEta.zip t) ->
    welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context (snd t)) (fst t))
  (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_context cf welltypedE wf_extE H) in exact T) :=
  @hyp_dup_rtf_context cf welltypedE_context.

(** Within one file (not part of audit C §4.2's count): K7 T1 [subject_reduction] gives K7 T1 [isType_red]. *)
Lemma hyp_dup_isType_red {cf : checker_flags} {H1 : T1_facts} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {U : term}, isTypeE Σ Γ T -> PCUICReduction.red Σ Γ T U -> isTypeE Σ Γ U.
Proof.
  intros Σ wfΣ Γ T U (hr & s & hs & hrel) r.
  split; [exact hr|]. exists s. split; [|exact hrel].
  exact (subject_reduction Σ Γ T U (tSort s) wfΣ hs r).
Qed.
Definition hyp_dup_isType_red_fits {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@isType_red cf H1) in exact T) := @hyp_dup_isType_red cf H1.

(** ** Print Assumptions of every kept [<field>_proved] lemma *)

Print Assumptions rtf_rel_proved.
Print Assumptions rtf_const_proved.
Print Assumptions rtf_cofix_proved.
Print Assumptions rtf_app_sort_proved.
Print Assumptions rtf_app_prod_proved.
Print Assumptions rtf_app_prim_proved.
Print Assumptions ctf_case_brs_length_proved.
Print Assumptions typingE_rename_P_proved.
Print Assumptions ctf_wf_universes_proved.
