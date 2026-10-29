(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICLiftSubst PCUICUnivSubst
     PCUICSigmaCalculus PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosed PCUICTyping PCUICCumulativity
     PCUICCumulativitySpec PCUICWellScopedCumulativity PCUICContextSubst PCUICCases PCUICNormal PCUICPosition
     PCUICConversion PCUICFixWitness PCUICWfUniverses PCUICClosedBodies PCUICSpine PCUICWeakeningEnv
     PCUICInductiveInversion PCUICContextConversionTyp PCUICRenameDef
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind
     PCUICEtaA6More PCUICGlobalEnvEta
     PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWsCumulEtaCtx
     PCUICWeakeningTypEta PCUICRenameTypEta PCUICInstTypEta PCUICCasesWfTypEta PCUICGuardClosureEta.
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution.
From Stdlib Require Import Program.Equality.
From MetaRocq.SafeChecker Require Import PCUICSafeReduceEta PCUICTypingEtaDefs PCUICTypingEtaHyps.

(** * ETAK (EtaHypProve): the PROVABLE-NOW named hypotheses of the E bundles, proved

  BET-64 EtaCheckerLane, worker EtaHypProve, 2026-10-29. Audit [lanes/eta/etak/hyp-audit-C.md] classified
  56 of the 112 named hypotheses of the E checker's bundles as PROVABLE NOW (a route through lemmas that
  are already proved). This file proves them, one lemma [<field>_proved] per hypothesis, whose statement
  is the hypothesis's statement text copied verbatim from its source:
  - REDUCE: fields of [ReduceTypedFacts] ([PCUICSafeReduceEta]) at [wt := welltypedE], [wfP := wf_extE]
    (the hypothesis [PCUICSafeReduceEtaBridge.reduce_factsE]);
  - EtaConv: fields of [ConvTypedFacts] ([PCUICSafeConversionEtaFacts] @ [c7cbbe73]) at the same
    instantiation (the hypothesis [conv_factsE] of [PCUICSafeConversionEta]);
  - EtaPosK4: section variable [typingE_rename_P] of [EtaTypingE] ([PCUICPositionEtaTyping] @ [767d50c6]);
  - K7: fields of the classes of [PCUICTypingEtaHyps].
  Identity check, by the type checker: after each lemma, [<field>_fits] ascribes the lemma to the field's
  type as projected from its class at the same parameters ([type of (@field cf H)]); for the two sources not
  in this branch ([ConvTypedFacts], [EtaTypingE]) [<field>_fits] restates the source text and is defined as
  the lemma. The textual comparison is [lanes/eta/etak/hypprove-identity.py].
  No proof uses a class field, a section variable or an admitted fact: [Print Assumptions] at the end.
  The lemmas named [hyp_*] are helpers. Integration (replacing a hypothesis by its lemma) is for the
  owners of the source files. *)

(** ** REDUCE: fields of [ReduceTypedFacts] ([PCUICSafeReduceEta]) at [wt := welltypedE], [wfP := wf_extE]
    (the named hypothesis [PCUICSafeReduceEtaBridge.reduce_factsE]) *)

Lemma rtf_rel_proved {cf : checker_flags} :
  forall Σ Γ n, wf_extE Σ -> welltypedE Σ Γ (tRel n) -> nth_error Γ n <> None.
Proof.
  intros Σ Γ n wfΣ [T h] e.
  destruct (inversion_Rel Σ (wf_extE_wfE Σ wfΣ) h) as [decl [_ [e' _]]].
  rewrite e' in e. discriminate.
Qed.
Definition rtf_rel_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_rel cf welltypedE wf_extE H) in exact T) := @rtf_rel_proved cf.

Lemma rtf_const_proved {cf : checker_flags} :
  forall Σ Γ c u, wf_extE Σ -> welltypedE Σ Γ (tConst c u) ->
    exists decl, declared_constant Σ c decl.
Proof.
  intros Σ Γ c u wfΣ [T h].
  destruct (inversion_Const Σ (wf_extE_wfE Σ wfΣ) h) as [decl [_ [d _]]].
  now exists decl.
Qed.
Definition rtf_const_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_const cf welltypedE wf_extE H) in exact T) := @rtf_const_proved cf.

Lemma rtf_cofix_proved {cf : checker_flags} :
  forall Σ Γ mfix idx, wf_extE Σ -> welltypedE Σ Γ (tCoFix mfix idx) ->
    nth_error mfix idx <> None.
Proof.
  intros Σ Γ mfix idx _ [T h].
  remember (tCoFix mfix idx) as t0 eqn:heqt. revert mfix idx heqt.
  induction h; intros mfix' idx' heqt; try discriminate heqt.
  - injection heqt; intros; subst. congruence.
  - match goal with IH : forall m i, _ = tCoFix m i -> _ |- _ => exact (IH _ _ heqt) end.
Qed.
Definition rtf_cofix_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_cofix cf welltypedE wf_extE H) in exact T) := @rtf_cofix_proved cf.

Lemma rtf_app_sort_proved {cf : checker_flags} :
  forall Σ Γ s a, wf_extE Σ -> welltypedE Σ Γ (tApp (tSort s) a) -> False.
Proof.
  intros Σ Γ s a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  remember (tApp (tSort s) a) as t0 eqn:heqt. revert s a heqt.
  induction h; intros s' a' heqt; try discriminate heqt.
  - injection heqt; intros; subst.
    match goal with H : typingE _ _ (tSort _) (tProd _ _ _) |- _ =>
      destruct (inversion_Sort Σ wfΣ' H) as [_ [_ c]] end.
    exact (ws_cumul_pb_Sort_Prod_inv (wfΣ := wfΣ') Cumul c).
  - match goal with IH : forall s0 a0, _ = tApp (tSort s0) a0 -> False |- _ => exact (IH _ _ heqt) end.
Qed.
Definition rtf_app_sort_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_sort cf welltypedE wf_extE H) in exact T) := @rtf_app_sort_proved cf.

Lemma rtf_app_prod_proved {cf : checker_flags} :
  forall Σ Γ na A B a, wf_extE Σ -> welltypedE Σ Γ (tApp (tProd na A B) a) -> False.
Proof.
  intros Σ Γ na A B a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  remember (tApp (tProd na A B) a) as t0 eqn:heqt. revert na A B a heqt.
  induction h; intros na' A' B' a' heqt; try discriminate heqt.
  - injection heqt; intros; subst.
    match goal with H : typingE _ _ (tProd _ _ _) (tProd _ _ _) |- _ =>
      destruct (inversion_Prod Σ wfΣ' H) as [s1 [s2 [_ [_ c]]]] end.
    exact (ws_cumul_pb_Sort_Prod_inv (wfΣ := wfΣ') Cumul c).
  - match goal with IH : forall na0 A0 B0 a0, _ = tApp (tProd na0 A0 B0) a0 -> False |- _ =>
      exact (IH _ _ _ _ heqt) end.
Qed.
Definition rtf_app_prod_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_prod cf welltypedE wf_extE H) in exact T) := @rtf_app_prod_proved cf.

(** The inversion of a primitive value over [typingE] (as K7's [inversion_*] in [PCUICTypingEtaHyps]). *)
Lemma hyp_inversion_Prim {cf : checker_flags} (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ p T} :
  Σ ;;; Γ |-E tPrim p : T ->
  ∑ prim_ty cdecl, [× primitive_constant Σ (prim_val_tag p) = Some prim_ty,
    declared_constant Σ prim_ty cdecl, primitive_invariants (prim_val_tag p) cdecl &
    Σ ;;; Γ ⊢E prim_type p prim_ty ≤ T].
Proof.
  intros h. remember (tPrim p) as t0 eqn:heqt. revert p heqt.
  induction h; intros p' heqt; try discriminate heqt.
  - injection heqt; intros; subst. exists prim_ty, cdecl. split; try assumption.
    eapply typing_ws_cumul_pbE. eapply typeE_Prim; eassumption.
  - match goal with IH : forall p0, _ = tPrim p0 -> _ |- _ =>
      destruct (IH _ heqt) as (pt & cd & [e1 e2 e3 cc]) end.
    exists pt, cd. split; try assumption. refine (cumul_stepE _ _ _ cc); eassumption.
Qed.

Lemma rtf_app_prim_proved {cf : checker_flags} :
  forall Σ Γ p a, wf_extE Σ -> welltypedE Σ Γ (tApp (tPrim p) a) -> False.
Proof.
  intros Σ Γ p a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  remember (tApp (tPrim p) a) as t0 eqn:heqt. revert p a heqt.
  induction h; intros p' a' heqt; try discriminate heqt.
  - injection heqt; intros; subst.
    match goal with H : typingE _ _ (tPrim _) (tProd _ _ _) |- _ =>
      destruct (hyp_inversion_Prim Σ wfΣ' H) as (pt & cd & [hpc hdecl hinv cc]) end.
    pose proof wfΣ' as (_ & wfr & _).
    exact (invert_cumul_prim_type_prodE (wfΣ := wfE_ClosedBodies Σ) hdecl hinv
             (prim_op_of_primitive_constant Σ _ _ wfr hpc) cc).
  - match goal with IH : forall p0 a0, _ = tApp (tPrim p0) a0 -> False |- _ => exact (IH _ _ heqt) end.
Qed.
Definition rtf_app_prim_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_prim cf welltypedE wf_extE H) in exact T) := @rtf_app_prim_proved cf.

(** ** EtaConv: field [ctf_case_brs_length] of [ConvTypedFacts] ([PCUICSafeConversionEtaFacts] @ [c7cbbe73],
    not in this branch) at [wt := welltypedE], [wfP := wf_extE] (the hypothesis [conv_factsE]) *)

Lemma ctf_case_brs_length_proved {cf : checker_flags} :
  forall Σ Γ ci p c brs, wf_extE Σ -> welltypedE Σ Γ (tCase ci p c brs) ->
      exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|.
Proof.
  intros Σ Γ ci p c brs _ [T h].
  remember (tCase ci p c brs) as t0 eqn:heqt. revert ci p c brs heqt.
  induction h; intros ci' p' c' brs' heqt; try discriminate heqt.
  - injection heqt; intros; subst.
    match goal with H : case_branch_typing _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as [_ hbrs] end.
    exists mdecl, idecl. split; [assumption|]. apply All2i_length in hbrs. lia.
  - match goal with IH : forall ci0 p0 c0 brs0, _ = tCase ci0 p0 c0 brs0 -> _ |- _ =>
      exact (IH _ _ _ _ heqt) end.
Qed.
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

(** ** K7 ([PCUICTypingEtaHyps]): the exact twins of [Typing/PCUICWeakeningTypEta] *)

Lemma All_mfix_wf_proved {cf : checker_flags} :
    forall (Σ : global_env × universes_decl) (Γ : context) (mfix : list (def term)), wfE Σ.1 -> wf_localE Σ Γ -> All (fun d : def term => isTypeRelE Σ Γ (dtype d) (binder_relevance (dname d))) mfix -> wf_localE Σ (Γ,,, fix_context mfix).
Proof. intros Σ Γ mfix. exact (All_mfix_wfE Σ Γ mfix). Qed.
Definition All_mfix_wf_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@All_mfix_wf cf H) in exact T) := @All_mfix_wf_proved cf.

Lemma isTypeRel_lift_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} {r : relevance} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeRelE Σ (skipn n Γ) ty r -> isTypeRelE Σ Γ (lift0 n ty) r.
Proof. intros Σ n Γ ty r isdecl. exact (isTypeRel_liftE isdecl). Qed.
Definition isTypeRel_lift_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isTypeRel_lift cf H) in exact T) := @isTypeRel_lift_proved cf.

Print Assumptions rtf_rel_proved.
Print Assumptions rtf_const_proved.
Print Assumptions rtf_cofix_proved.
Print Assumptions rtf_app_sort_proved.
Print Assumptions rtf_app_prod_proved.
Print Assumptions rtf_app_prim_proved.
Print Assumptions ctf_case_brs_length_proved.
Print Assumptions typingE_rename_P_proved.
Print Assumptions All_mfix_wf_proved.
Print Assumptions isTypeRel_lift_proved.
