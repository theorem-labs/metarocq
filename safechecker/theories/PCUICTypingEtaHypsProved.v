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
  No proof uses a class field, a section variable or an admitted fact: [Print Assumptions] at the end
  (Rocq's primitive-type axioms and [functional_extensionality_dep] only). Where a lemma landed on
  [frac/eta] inhabits a row ([PCUICSREtaConv] @ [da1eb84b], [Typing/PCUICWeakeningTypEta],
  [Typing/PCUICRenameTypEta]), the proof is that lemma. [depelim] is Equations' ([DepElim.depelim]): this
  file loads [Program.Equality] after Equations, and Stdlib's [depelim] would add [eq_rect_eq].
  Helpers carry a prefix: [hyp_*], [stc_*] (structural spines), [univ_*] (universes), [rdx_*]
  (reduction), [sbs_*] (substitution), [smh_*] (smash/expand_lets). The section "Duplicate GENUINE
  hypotheses" derives, as conditional lemmas [hyp_dup_*], the GENUINE hypotheses that repeat a fact
  stated in another file. Integration (replacing a hypothesis by its lemma) is for the owners of the
  source files. *)

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
  intros Σ Γ mfix idx wfΣ [T h] e.
  destruct (inversion_CoFixE Σ (wf_extE_wfE Σ wfΣ) h) as (decl & _ & hn & _).
  rewrite hn in e. discriminate.
Qed.
Definition rtf_cofix_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_cofix cf welltypedE wf_extE H) in exact T) := @rtf_cofix_proved cf.

Lemma rtf_app_sort_proved {cf : checker_flags} :
  forall Σ Γ s a, wf_extE Σ -> welltypedE Σ Γ (tApp (tSort s) a) -> False.
Proof.
  intros Σ Γ s a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  destruct (inversion_AppE Σ wfΣ' h) as (na & A & B & hf & _ & _).
  destruct (inversion_Sort Σ wfΣ' hf) as [_ [_ c]].
  exact (ws_cumul_pb_Sort_Prod_inv (wfΣ := wfΣ') Cumul c).
Qed.
Definition rtf_app_sort_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_sort cf welltypedE wf_extE H) in exact T) := @rtf_app_sort_proved cf.

Lemma rtf_app_prod_proved {cf : checker_flags} :
  forall Σ Γ na A B a, wf_extE Σ -> welltypedE Σ Γ (tApp (tProd na A B) a) -> False.
Proof.
  intros Σ Γ na A B a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  destruct (inversion_AppE Σ wfΣ' h) as (na' & A' & B' & hf & _ & _).
  destruct (inversion_Prod Σ wfΣ' hf) as [s1 [s2 [_ [_ c]]]].
  exact (ws_cumul_pb_Sort_Prod_inv (wfΣ := wfΣ') Cumul c).
Qed.
Definition rtf_app_prod_fits {cf : checker_flags} (H : ReduceTypedFacts welltypedE wf_extE) :
  ltac:(let T := type of (@rtf_app_prod cf welltypedE wf_extE H) in exact T) := @rtf_app_prod_proved cf.

Lemma rtf_app_prim_proved {cf : checker_flags} :
  forall Σ Γ p a, wf_extE Σ -> welltypedE Σ Γ (tApp (tPrim p) a) -> False.
Proof.
  intros Σ Γ p a wfΣ [T h].
  have wfΣ' : wfE Σ := wf_extE_wfE Σ wfΣ.
  destruct (inversion_AppE Σ wfΣ' h) as (na & A & B & hf & _ & _).
  destruct (inversion_PrimE Σ wfΣ' hf) as (pt & cd & [_ hpc hdecl hinv _ cc]).
  pose proof wfΣ' as (_ & wfr & _).
  exact (invert_cumul_prim_type_prodE (wfΣ := wfE_ClosedBodies Σ) hdecl hinv
           (prim_op_of_primitive_constant Σ _ _ wfr hpc) cc).
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

Lemma isType_lift_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeE Σ (skipn n Γ) ty -> isTypeE Σ Γ (lift0 n ty).
Proof. intros Σ n Γ ty isdecl. exact (isType_liftE isdecl). Qed.
Definition isType_lift_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isType_lift cf H) in exact T) := @isType_lift_proved cf.

Lemma weaken_ctx_proved {cf : checker_flags} :
    forall {Σ : global_env × universes_decl} {Γ : context} {t : term} {T : term} (Δ : context), wfE Σ.1 -> wf_localE Σ Δ -> Σ;;; Γ |-E t : T -> Σ;;; Δ,,, Γ |-E t : T.
Proof. intros Σ Γ t T Δ. exact (weaken_ctxE Δ). Qed.
Definition weaken_ctx_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@weaken_ctx cf H) in exact T) := @weaken_ctx_proved cf.

Lemma weaken_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env × universes_decl} {Δ : context} (Γ : context), wfE Σ.1 -> wf_localE Σ Γ -> wf_localE Σ Δ -> wf_localE Σ (Γ,,, Δ).
Proof. intros Σ Δ Γ. exact (weaken_wf_localE Γ). Qed.
Definition weaken_wf_local_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@weaken_wf_local cf H) in exact T) := @weaken_wf_local_proved cf.

Lemma weakening_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Γ' : list context_decl} {Γ'' : list context_decl}, wf_localE Σ (Γ,,, Γ') -> wf_localE Σ (Γ,,, Γ'') -> wf_localE Σ (Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ').
Proof. intros Σ wfΣ Γ Γ' Γ''. exact (weakening_wf_localE (wfΣ := wfΣ)). Qed.
Definition weakening_wf_local_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@weakening_wf_local cf H) in exact T) := @weakening_wf_local_proved cf.

Lemma isType_weaken_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term}, wf_localE Σ Γ -> isTypeE Σ [] T -> isTypeE Σ Γ T.
Proof.
  intros Σ wfΣ Γ T wfΓ h. exact (lift_typing_weaken_ctxE Σ [] Γ _ wfΣ wfΓ h).
Qed.
Definition isType_weaken_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isType_weaken cf H) in exact T) := @isType_weaken_proved cf.

Lemma wf_rel_weak_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context), wf_localE Σ Γ -> forall (Γ' : context), wf_localE Σ Γ' -> wf_local_relE Σ Γ Γ'.
Proof.
  intros Σ wfΣ Γ wfΓ Γ' wfΓ'.
  induction wfΓ' as [|Δ na t wfΔ IH h|Δ na b t wfΔ IH h].
  - exact All_local_rel_nil.
  - apply All_local_rel_abs; [exact IH|].
    exact (lift_typing_weaken_ctxE Σ Δ Γ _ wfΣ wfΓ h).
  - apply All_local_rel_def; [exact IH|].
    exact (lift_typing_weaken_ctxE Σ Δ Γ _ wfΣ wfΓ h).
Qed.
Definition wf_rel_weak_fits {cf : checker_flags} (H : @T6BD_facts cf) :
  ltac:(let T := type of (@wf_rel_weak cf H) in exact T) := @wf_rel_weak_proved cf.

(** ** K7: inversions of products *)

Lemma isType_tProd_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, isTypeE Σ Γ (tProd na A B) <~> isTypeRelE Σ Γ A (binder_relevance na) × isTypeE Σ (Γ,, vass na A) B.
Proof.
  intros Σ wfΣ Γ na A B. split; intro HH.
  - destruct HH as (_ & s & H & _).
    destruct (inversion_Prod Σ wfΣ H) as [s1 [s2 [HA [HB _]]]].
    apply lift_sorting_forget_univ in HA.
    split; [exact HA|exact (has_sort_isTypeE _ HB)].
  - destruct HH as [HA HB].
    pose proof (lift_sorting_extract HA).
    destruct HB as (_ & sB & HB & _).
    eapply has_sort_isTypeE.
    eapply typeE_Prod; eassumption.
Qed.
Definition isType_tProd_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isType_tProd cf H) in exact T) := @isType_tProd_proved cf.

Lemma welltyped_prod_codomain_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, welltypedE Σ Γ (tProd na A B) -> welltypedE Σ (Γ,, vass na A) B.
Proof.
  intros Σ wfΣ Γ na A B [T hT].
  destruct (inversion_Prod Σ wfΣ hT) as (s1 & s2 & _ & hB & _).
  econstructor. exact hB.
Qed.
Definition welltyped_prod_codomain_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@welltyped_prod_codomain cf H) in exact T) := @welltyped_prod_codomain_proved cf.

(** [PCUICArities.it_mkProd_or_LetIn_wf_local] over [typingE]. *)
Lemma hyp_it_mkProd_or_LetIn_wf_local {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ T U} :
  Σ ;;; Γ |-E it_mkProd_or_LetIn Δ T : U -> wf_localE Σ (Γ ,,, Δ).
Proof.
  move: Γ T U. induction Δ as [|d Δ IHΔ] using rev_ind => Γ T U.
  - cbn. intros h. exact (typingE_wf_local h).
  - rewrite it_mkProd_or_LetIn_app. destruct d as [na [b|] ty]; cbn; move=> H.
    + destruct (inversion_LetIn Σ wfΣ H) as (A & _ & HT & _).
      apply IHΔ in HT. rewrite /app_context -app_assoc. exact HT.
    + destruct (inversion_Prod Σ wfΣ H) as (s1 & s2 & _ & HT & _).
      apply IHΔ in HT. rewrite /app_context -app_assoc. exact HT.
Qed.

Lemma isType_it_mkProd_or_LetIn_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {T : term}, isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_localE Σ (Γ,,, Δ).
Proof.
  intros Σ wfΣ Γ Δ T (_ & s & Hs & _). exact (hyp_it_mkProd_or_LetIn_wf_local (wfΣ := wfΣ) Hs).
Qed.
Definition isType_it_mkProd_or_LetIn_wf_local_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isType_it_mkProd_or_LetIn_wf_local cf H) in exact T) :=
  @isType_it_mkProd_or_LetIn_wf_local_proved cf.

(** ** K7: structural spine and context facts (T0 rows 4, 5, 23, 24, 25, 26, 29) and T1 [isType_prim_arg_types]
    (helpers [stc_*]) *)

(** [PCUICSpine.ctx_inst_subst_length] at [typingE]. *)
Lemma stc_ctx_inst_subE_length {cf : checker_flags} {Σ : global_env_ext} {Γ} {Δ : context} {args}
  (c : ctx_instE Σ Γ args Δ) :
  #|ctx_inst_subE c| = #|Δ|.
Proof.
  induction c; simpl; auto; try lia;
  rewrite length_app IHc subst_telescope_length /=; lia.
Qed.

(** [PCUICSpine.ctx_inst_sub_spec] at [typingE]. *)
Lemma stc_ctx_inst_subE_spec {cf : checker_flags} {Σ : global_env_ext} {Γ Δ args}
  (c : ctx_instE Σ Γ args Δ) :
  make_context_subst Δ args [] = Some (ctx_inst_subE c).
Proof.
  induction c; simpl; auto.
  now apply (make_context_subst_tele [] [i]) in IHc.
  apply (make_context_subst_tele [] [b]) in IHc.
  now rewrite subst_empty.
Qed.

(** [PCUICSpine.ctx_inst_app] at [typingE]. *)
Lemma stc_ctx_instE_app {cf : checker_flags} {Σ : global_env_ext} {Γ} {Δ : context} {Δ' args args'}
  (dom : ctx_instE Σ Γ args Δ) :
  ctx_instE Σ Γ args' (subst_telescope (ctx_inst_subE dom) 0 Δ') ->
  ctx_instE Σ Γ (args ++ args') (Δ ++ Δ').
Proof.
  induction dom in args', Δ' |- *; simpl.
  - now rewrite subst_telescope_empty.
  - rewrite subst_app_telescope /= stc_ctx_inst_subE_length /= subst_telescope_length Nat.add_0_r /=.
    move/IHdom => IH.
    constructor => //.
    now rewrite subst_telescope_app Nat.add_0_r.
  - rewrite subst_app_telescope /= stc_ctx_inst_subE_length /= subst_telescope_length Nat.add_0_r /=.
    move/IHdom => IH.
    constructor => //.
    now rewrite subst_telescope_app Nat.add_0_r.
Qed.

(** Row 26. Port of [PCUICSpine.spine_subst_ctx_inst] (syntactic in the typing judgment). *)
Lemma spine_subst_ctx_inst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {Δ : context} {args : list term} {s : list term}, spine_substE Σ Γ args s Δ -> ctx_instE Σ Γ args (List.rev Δ).
Proof.
  intros Σ Γ Δ args s [wfd _ cs subsl].
  induction subsl in args, cs |- *.
  - DepElim.depelim cs. constructor.
  - DepElim.depelim cs.
    specialize (IHsubsl _ cs).
    unshelve eapply stc_ctx_instE_app; tea. cbn.
    rewrite /map_decl /=. repeat constructor.
    pose proof (stc_ctx_inst_subE_spec IHsubsl) as msub.
    eapply make_context_subst_spec in msub.
    rewrite List.rev_involutive in msub.
    now pose proof (context_subst_fun cs msub); subst s.
  - DepElim.depelim cs.
    specialize (IHsubsl _ cs). cbn.
    rewrite -(app_nil_r args).
    unshelve eapply stc_ctx_instE_app; tea. cbn.
    rewrite /map_decl /=. repeat constructor.
Qed.

Definition spine_subst_ctx_inst_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@spine_subst_ctx_inst cf H) in exact T) := @spine_subst_ctx_inst_proved cf.

(** Row 29. Only the [context_subst] component of the spine is used (as in [PCUICSR.spine_subst_inst_subst]). *)
Lemma spine_subst_inst_subst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {inst : list term} {s : list term} {Δ : context} {Δ' : context}, spine_substE Σ Γ inst s Δ -> subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ').
Proof.
  intros Σ Γ inst s Δ Δ' sp.
  have cs := inst_ctx_substE sp.
  have hl := context_subst_length2 cs.
  rewrite (context_subst_subst_extended_subst _ _ _ cs).
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite PCUICSR.subst_context_subst_context.
  rewrite extended_subst_length Nat.add_0_l.
  rewrite PCUICInductives.subst_context_lift_context_cancel //.
  now rewrite List.length_rev hl.
Qed.

Definition spine_subst_inst_subst_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@spine_subst_inst_subst cf H) in exact T) := @spine_subst_inst_subst_proved cf.

(** Row 4. Port of [PCUICSpine.ctx_inst_open_terms] with [subject_is_open_termE]. *)
Lemma ctx_inst_open_terms_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (args : list term) (Δ : context), ctx_instE Σ Γ args Δ -> All (fun t : term => on_free_vars (shiftnP #|Γ| xpred0) t) args.
Proof.
  intros Σ wfΣ Γ args Δ c.
  induction c.
  - constructor.
  - constructor; [|exact IHc].
    match goal with H : typingE _ _ _ _ |- _ => exact (subject_is_open_termE (wfΣ := wfΣ) H) end.
  - exact IHc.
Qed.

Definition ctx_inst_open_terms_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@ctx_inst_open_terms cf H) in exact T) := @ctx_inst_open_terms_proved cf.

(** [PCUICSpine.ctx_inst_smash_acc] at [typingE] (its proof is [Proof using Type]: no typing fact used). *)
Lemma stc_ctx_instE_smash_acc {cf : checker_flags} {Σ : global_env_ext} {Γ i Δ} :
  ctx_instE Σ Γ i Δ <~>
  ctx_instE Σ Γ i (List.rev (smash_context [] (List.rev Δ))).
Proof.
  split.
  - induction 1.
    + constructor.
    + simpl.
      rewrite smash_context_app_ass. len.
      rewrite List.rev_app_distr /=.
      constructor. auto.
      rewrite subst_telescope_subst_context.
      rewrite -smash_context_subst /=; len.
      now rewrite subst_context_rev_subst_telescope.
    + simpl. rewrite smash_context_app_def.
      now rewrite subst_context_rev_subst_telescope.
  - induction Δ using PCUICInduction.ctx_length_ind in i |- *; simpl; auto.
    destruct d as [na [b|] ty] => /=.
    * rewrite smash_context_app_def /=.
      rewrite subst_context_rev_subst_telescope.
      intros ctxi. constructor.
      apply X => //. now rewrite subst_telescope_length //.
    * rewrite smash_context_app_ass List.rev_app_distr /=.
      intros ctxi; DepElim.depelim ctxi.
      constructor => //.
      apply X. rewrite subst_telescope_length //.
      rewrite subst_telescope_subst_context in ctxi.
      rewrite -(smash_context_subst []) in ctxi.
      now rewrite subst_context_rev_subst_telescope in ctxi.
Qed.

(** Row 5. Port of [PCUICSpine.ctx_inst_smash]. *)
Lemma ctx_inst_smash_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {i : list term} {Δ : list context_decl}, ctx_instE Σ Γ i (List.rev Δ) <~> ctx_instE Σ Γ i (List.rev (smash_context [] Δ)).
Proof.
  intros Σ Γ i Δ. split; intros X.
  - apply (fst stc_ctx_instE_smash_acc) in X. now rewrite List.rev_involutive in X.
  - apply (snd stc_ctx_instE_smash_acc). now rewrite List.rev_involutive.
Qed.

Definition ctx_inst_smash_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@ctx_inst_smash cf H) in exact T) := @ctx_inst_smash_proved cf.

(** Row 23. Port of [PCUICContexts.sorts_local_ctx_wf_local]. *)
Lemma sorts_local_ctx_wf_local_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : list sort), wf_localE Σ Γ -> sorts_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ).
Proof.
  intros Σ Γ Δ. induction Δ as [|[na [b|] ty] Δ IH]; intros s wfΓ wfctx.
  - exact wfΓ.
  - cbn in wfctx. destruct wfctx as [h1 h2].
    constructor; [exact (IH _ wfΓ h1)|exact h2].
  - destruct s as [|u s]; cbn in wfctx; [destruct wfctx|].
    destruct wfctx as [h1 h2].
    constructor; [exact (IH _ wfΓ h1)|].
    exact (lift_sorting_forget_univ h2).
Qed.

Definition sorts_local_ctx_wf_local_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@sorts_local_ctx_wf_local cf H) in exact T) := @sorts_local_ctx_wf_local_proved cf.

(** Row 24. Port of [PCUICContexts.type_local_ctx_wf_local]. *)
Lemma type_local_ctx_wf_local_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : sort), wf_localE Σ Γ -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ).
Proof.
  intros Σ Γ Δ s wfΓ. induction Δ as [|[na [b|] ty] Δ IH]; intros wfctx.
  - exact wfΓ.
  - cbn in wfctx. destruct wfctx as [h1 h2].
    constructor; [exact (IH h1)|exact h2].
  - cbn in wfctx. destruct wfctx as [h1 h2].
    constructor; [exact (IH h1)|].
    exact (lift_sorting_forget_univ h2).
Qed.

Definition type_local_ctx_wf_local_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@type_local_ctx_wf_local cf H) in exact T) := @type_local_ctx_wf_local_proved cf.

(** [PCUICSpine.subslet_app] at [typingE]. *)
Lemma stc_subsletE_app {cf : checker_flags} (Σ : global_env_ext) Γ s s' Δ Δ' :
  subsletE Σ Γ s (subst_context s' 0 Δ) ->
  subsletE Σ Γ s' Δ' ->
  subsletE Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
  induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
  - DepElim.depelim sub'. auto.
  - rewrite subst_context_snoc in sub' => sub''.
    move:(subslet_length sub') => /=.
    rewrite /snoc /= subst_context_length /= => Hlen.
    destruct a as [na [b|] ty].
    * DepElim.depelim sub'; simpl in t0, Hlen.
      rewrite -subst_app_simpl' /=. lia.
      constructor. eauto.
      now rewrite - !subst_app_simpl' in t0; try lia.
    * rewrite /subst_decl /map_decl /snoc /= in sub'.
      DepElim.depelim sub'; simpl in Hlen.
      rewrite - !subst_app_simpl' in t0; try lia.
      simpl; constructor; eauto.
Qed.

(** Row 25. Port of [PCUICSpine.spine_subst_app]. *)
Lemma spine_subst_app_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : list context_decl} {Δ : context} {Δ' : list context_decl} {inst : list term} {inst' : list term} {insts : list term}, #|inst| = context_assumptions Δ -> wf_localE Σ (Γ,,, Δ,,, Δ') -> spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ -> spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') -> spine_substE Σ Γ (inst ++ inst') insts (Δ,,, Δ').
Proof.
  intros Σ Γ Δ Δ' inst inst' insts len wf [wfdom wfcodom cs subst] [wfdom' wfcodom' cs' subst'].
  split; auto.
  now rewrite app_context_assoc.
  eapply context_subst_app_inv; split; auto.
  rewrite skipn_all_app_eq; try lia. auto.
  rewrite (firstn_app_left) ?Nat.add_0_r // firstn_0 // app_nil_r //.
  rewrite -(firstn_skipn #|Δ'| insts).
  eapply stc_subsletE_app; auto.
Qed.

Definition spine_subst_app_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@spine_subst_app cf H) in exact T) := @spine_subst_app_proved cf.

(** T1 [isType_prim_arg_types]. Port of [PCUICSR.isType_prim_arg_types] (same premises): [typeE_Const] for
    the domain, [isType_liftE] for the codomain, [typeE_Prod] inlined for [isType_tProd]. *)
Lemma isType_prim_arg_types_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {tags : list prim_tag} {res : term} {T : term}, wf_localE Σ Γ -> (forall t : prim_tag, In t tags -> t <> primArray) -> All (prim_op_tag_declared Σ) tags -> PCUICPrimOpType.prim_arg_types (retroknowledge Σ.1) tags res = Some T -> isTypeE Σ Γ res -> isTypeE Σ Γ T.
Proof.
  intros Σ wfΣ Γ tags res T wfΓ.
  induction tags as [|t tags ih] in T |- *; cbn; intros hna hall h hres.
  - noconf h. exact hres.
  - depelim hall.
    destruct (PCUICPrimOpType.prim_tag_type _ t) as [a|] eqn:ht => //.
    destruct (PCUICPrimOpType.prim_arg_types _ tags res) as [rest|] eqn:hr => //.
    cbn in h. noconf h.
    destruct p as (kn & d & [hpc hd hinv]).
    unfold PCUICPrimOpType.prim_tag_type in ht.
    destruct (EnvironmentTyping.retro_type_constant _ t) as [kn'|] eqn:hrt => //.
    cbn in ht. noconf ht.
    assert (ept : primitive_constant Σ t = EnvironmentTyping.retro_type_constant (retroknowledge Σ) t)
      by (destruct t; reflexivity).
    rewrite ept hrt in hpc. noconf hpc.
    assert (hnat : t <> primArray) by (apply hna; now left).
    assert (hrest : isTypeE Σ Γ rest).
    { eapply (ih rest); tea; try reflexivity. intros t' ht'. apply hna. now right. }
    (* the domain: a type constant, of sort [Set], relevant *)
    assert (hdom : isTypeRelE Σ Γ (tConst kn' []) Relevant).
    { destruct t; try congruence; cbn in hinv.
      all: destruct hinv as [hty hbod huniv]; split; [constructor|];
        exists (Sort.type0@[[]]); repeat split.
      all: try reflexivity.
      all: change (tSort ?s@[[]]) with (tSort s)@[[]];
        rewrite <- hty; refine (typeE_Const _ _ _ [] _ wfΓ hd _); rewrite huniv //. }
    have hcod : isTypeE Σ (Γ ,, vass (mkBindAnn nAnon Relevant) (tConst kn' [])) (lift0 1 rest).
    { eapply (isType_liftE (n := 1) (Γ := Γ ,, vass (mkBindAnn nAnon Relevant) (tConst kn' []))); cbn; tea.
      + lia.
      + constructor; tea. }
    unfold tImpl.
    pose proof (lift_sorting_extract hdom) as hA.
    destruct hcod as (_ & sB & HB & _).
    eapply has_sort_isTypeE.
    eapply typeE_Prod; eassumption.
Qed.

Definition isType_prim_arg_types_fits {cf : checker_flags} (H : T1_facts) : ltac:(let T := type of (@isType_prim_arg_types cf H) in exact T) := @isType_prim_arg_types_proved cf.

(** ** The universe facts of [typingE] (helpers [univ_*])

  Rows: [wf_universes_inst], [LSet_in_global_bounded] (U_facts); [type_local_ctx_wf],
  [typing_wf_universes], [typing_wf_sort], [isType_wf_universes] (T0_facts); [ctf_wf_universes]
  (ConvTypedFacts of EtaConv @ c7cbbe73, at [welltypedE]/[wf_extE]).

  Transport. Base proves the universe lemmas under a premise [wf Σ] that their proofs read only
  through [on_global_univs Σ.(universes)]. [univ_strip Σ] keeps the universes and the
  retroknowledge of [Σ] and drops the declarations: [wfE Σ] gives base [wf (univ_strip Σ)]
  (no declaration is left to type, [univ_wf_strip]), and every universe notion ([global_levels],
  [global_ext_levels], [wf_universes], [wf_instance], [wf_ctx_universes], [on_udecl_prop]) reads
  only [Σ.(universes)], so it is CONVERTIBLE between [Σ] and [univ_strip Σ]. The base lemma
  applied at [univ_strip Σ] therefore type-checks at [Σ]. *)

Definition univ_strip (Σ : global_env) : global_env :=
  {| universes := Σ.(universes); declarations := []; retroknowledge := Σ.(retroknowledge) |}.

Lemma univ_wf_strip {cf : checker_flags} {Σ : global_env} : wfE Σ -> wf (univ_strip Σ).
Proof.
  intros [onu [onr _]]. split; [exact onu|]. split; [exact onr|]. cbn. constructor.
Qed.

Lemma univ_extends_strip {Σ Σ' : global_env} : extends Σ Σ' -> extends (univ_strip Σ) (univ_strip Σ').
Proof.
  intros [hu _ hr]. split; [exact hu| |exact hr].
  intros c. exists []. reflexivity.
Qed.

(** U_facts [wf_universes_inst] (audit hyp-audit-C.md line 182: syntactic): base
    [PCUICWfUniverses.wf_universes_inst] at [univ_strip Σ.1]. *)
Lemma wf_universes_inst_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} (univs : universes_decl) (t : term) (u : list LevelSet.elt), wfE Σ -> on_udecl_prop Σ.1 univs -> wf_instance Σ u -> wf_universes (Σ.1, univs) t -> wf_universes Σ t@[u].
Proof.
  intros Σ univs t u wfΣ ond wfu wft.
  exact (@PCUICWfUniverses.wf_universes_inst cf (univ_strip Σ.1, Σ.2) univs t u (univ_wf_strip wfΣ) ond wfu wft).
Qed.
Definition wf_universes_inst_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@wf_universes_inst cf H) in exact T) := @wf_universes_inst_proved cf.

(** U_facts [LSet_in_global_bounded] (line 182: [not_var_global_levels] reads only
    [on_global_univs]): base [PCUICInductiveInversion.LSet_in_global_bounded] at [univ_strip Σ]. *)
Lemma LSet_in_global_bounded_proved {cf : checker_flags} :
  forall {Σ : global_env} {l : LevelSet.elt} (k : nat), wfE Σ -> LevelSet.In l (global_levels Σ) -> closedu_level k l.
Proof.
  intros Σ l k wfΣ hin.
  exact (@PCUICInductiveInversion.LSet_in_global_bounded cf (univ_strip Σ) l k (univ_wf_strip wfΣ) hin).
Qed.
Definition LSet_in_global_bounded_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@LSet_in_global_bounded cf H) in exact T) := @LSet_in_global_bounded_proved cf.

(** T0 row 48 [type_local_ctx_wf] (structural): base [PCUICInductives.type_local_ctx_wf]'s proof;
    the empty context case of [type_local_ctx] is [wf_sort Σ s] itself. *)
Lemma type_local_ctx_wf_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ Δ : context} {s : sort}, wfE Σ.1 -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_sort Σ s.
Proof.
  intros Σ Γ Δ s wfΣ.
  induction Δ as [|[na [b|] ty] Δ]; simpl; intuition auto.
Qed.
Definition type_local_ctx_wf_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@type_local_ctx_wf cf H) in exact T) := @type_local_ctx_wf_proved cf.

(** Helpers for T0 row 36 [typing_wf_universes]: the port of base [PCUICWfUniverses.wf_types]
    over [typingE_ind_env]. *)

Ltac univ_to_prop :=
  repeat match goal with
  | [ H: is_true (?x && ?y) |- _ ] =>
   let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
  end.

Ltac univ_to_wfu :=
  repeat match goal with
  | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_universe_reflect _ x)) in H
  | [ |- is_true (wf_universeb _ ?x) ] => apply (ssrbool.introT (@wf_universe_reflect _ x))
  | [ H: is_true (Sort.on_sort (wf_universeb _) _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_sort_reflect _ x)) in H
  | [ |- is_true (Sort.on_sort (wf_universeb _) _ ?x) ] => apply (ssrbool.introT (@wf_sort_reflect _ x))
  | [ H: is_true (wf_sortb _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_sort_reflect _ x)) in H
  | [ |- is_true (wf_sortb _ ?x) ] => apply (ssrbool.introT (@wf_sort_reflect _ x))
  end.

Ltac univ_specIH :=
  repeat match goal with
  | [ H : on_udecl _ _, H' : on_udecl _ _ -> _ |- _ ] => specialize (H' H)
  end.

Lemma univ_weaken_wf_universes {cf : checker_flags} {Σ Σ' : global_env} φ t :
  wfE Σ -> wfE Σ' -> extends Σ Σ' -> wf_universes (Σ, φ) t -> wf_universes (Σ', φ) t.
Proof.
  intros wfΣ wfΣ' ext.
  exact (@PCUICWfUniverses.weaken_wf_universes cf (univ_strip Σ, φ) (univ_strip Σ') t
    (univ_wf_strip wfΣ) (univ_wf_strip wfΣ') (univ_extends_strip ext)).
Qed.

(** E copy of base [PCUICWfUniverses.wf_universes_weaken] (same proof). *)
Lemma univ_wf_universes_weakenE {cf : checker_flags} :
  weaken_env_prop cumulSpecE0 (lift_typing typingE)
    (fun Σ _ j => option_default (wf_universes Σ) (j_term j) true && wf_universes Σ (j_typ j) && option_default (wf_sortb Σ) (j_univ j) true).
Proof.
  intros Σ Σ' φ wfΣ wfΣ' Hext _ j Hj.
  pose proof (fun t => @univ_weaken_wf_universes cf Σ Σ' φ t wfΣ wfΣ' Hext) as H.
  rtoProp; repeat split; auto.
  1: destruct j_term => //; cbn in *; auto.
  1: destruct j_univ => //; cbn in *; now apply (H (tSort _)).
Qed.

Lemma univ_wf_ctx_universes_closed {cf : checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {univs ctx} :
  on_udecl_prop Σ univs ->
  wf_ctx_universes (Σ, univs) ctx ->
  test_context (closedu #|polymorphic_instance univs|) ctx.
Proof.
  exact (@PCUICWfUniverses.wf_ctx_universes_closed cf (univ_strip Σ) (univ_wf_strip wfΣ) univs ctx).
Qed.

(** Base [PCUICWfUniverses.closed_ind_predicate_context] without its unused premises
    ([wf Σ], [declared_inductive]); same proof. *)
Lemma univ_closed_ind_predicate_context {ind mdecl idecl} :
  test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (ind_params mdecl) ->
  test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (ind_indices idecl) ->
  test_context (closedu #|abstract_instance (ind_universes mdecl)|) (ind_predicate_context ind mdecl idecl).
Proof.
  rewrite /ind_predicate_context; cbn.
  rewrite closedu_mkApps /=.
  rewrite closedu_abstract_instance /= => clpars clinds.
  apply/andP; split.
  * apply closedu_expand_lets_ctx. now rewrite clpars clinds.
  * apply closedu_to_extended_list_k.
    rewrite test_context_app.
    rewrite (closedu_smash_context _ _ clpars).
    apply closedu_expand_lets_ctx => //.
    now rewrite clpars.
Qed.

(** Base [PCUICWfUniverses.closedu_inds] without its unused premise [wf Σ]; same proof. *)
Lemma univ_closedu_inds {ind mdecl} :
  forallb (closedu #|abstract_instance (ind_universes mdecl)|)
    (inds ind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl)).
Proof.
  rewrite /inds.
  induction #|ind_bodies mdecl|; cbn; auto.
  rewrite IHn andb_true_r.
  eapply closedu_abstract_instance.
Qed.

(** The port of base [wf_types]. Inside a module so that the local hypothesis-naming hook
    (the E twin of base's, [PCUICWeakeningEnvTypEta.my_rename_hypE]) ends with the module
    (checked, build u5: after [End univ_WfTypesE], [rename_all_hyps] leaves a [wfE] and a
    [typingE] hypothesis unrenamed, so the parts concatenated after this one are unaffected). The
    script is base's with: [typing_ind_env] → [typingE_ind_env], [declared_*_inv] →
    [declared_*_invE], [wf_universes_weaken] → [univ_wf_universes_weakenE], [wf_universes_inst] →
    [wf_universes_inst_proved], [wf_ctx_universes_closed] / [closed_ind_predicate_context] /
    [closedu_inds] → the [univ_] helpers above. The [typeE_Cumul] case is closed by the preamble's
    [auto] from the two induction hypotheses; the conversion premise is not read. *)
Module univ_WfTypesE.

#[local] Ltac rename_hyp h ht ::= my_rename_hypE h ht.

Theorem univ_wf_typesE {cf : checker_flags} :
  env_propE (fun Σ Γ t T => wf_universes Σ t && wf_universes Σ T)
    (fun Σ _ j => lift_wfbu_term (wf_universes Σ) (wf_sortb Σ) j)
    (fun Σ Γ => wf_ctx_universes Σ Γ).
Proof.
    apply typingE_ind_env; unfold lift_wfbu_term; intros; rename_all_hyps; cbn; rewrite -!/(wf_universes _ _) ;
    univ_specIH; univ_to_prop;
    cbn; auto.

    - eapply MRReflect.introT. 1: apply lift_wfu_wfbu_term.
      apply lift_typing_subjtyp with (1 := X) => //= t T [] _ /andP[] //.

    - apply All_local_env_cst, All_forallb in X0.
      apply forallb_impl with (2 := X0) => [] [na bo ty] _ //= /andP[] //=.

    - rewrite wf_universes_lift.
      eapply forallb_nth_error with (n := n) in H0. rewrite heq_nth_error /= in H0.
      now move/andP: H0.

    - apply/andP; split; univ_to_wfu; cbn ; eauto with pcuic.

    - cbn in *; univ_to_wfu ; eauto with pcuic.
    - rewrite wf_universes_subst. constructor. univ_to_wfu; auto. constructor.
      now move/andP: H1 => [].

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constant_invE _ _ _ _ univ_wf_universes_weakenE wf X H0) as [[_ X0]%andb_and _]%andb_and.
      unshelve eapply declared_constant_to_gen in H0; eauto.
      epose proof (weaken_lookup_on_global_env' Σ.1 _ _ wf H0).
      eapply wf_universes_inst_proved. 2:eauto. all:eauto.
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_inductive_invE univ_wf_universes_weakenE wf X isdecl).
      move/onArity : X0 => /andP[] /andP[] /= _ Hind _.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      eapply wf_universes_inst_proved; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 isdecl)).
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constructor_invE univ_wf_universes_weakenE wf X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_universes_subst.
      { apply wf_universes_inds.
        now eapply consistent_instance_ext_wf. }
      move/on_ctype : onc => /andP[] /andP[] /= _ onc _.
      clear nthe. unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      eapply wf_universes_inst_proved; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 isdecl))).
      now eapply consistent_instance_ext_wf.

    - rewrite wf_universes_mkApps in H6.
      move/andP: H6 => /= [] wfu; rewrite forallb_app.
      move/andP=> [] wfpars wfinds.
      cbn in wfu.
      rewrite wfu /= wfpars wf_universes_mkApps /=
        forallb_app wfinds /= H0 /= !andb_true_r.
      pose proof (declared_inductive_invE univ_wf_universes_weakenE wf X isdecl).
      move:(onArityRed X3) => /andP[] /andP[] /= _ hty _.
      rewrite !wf_universes_it_mkProd_or_LetIn in hty.
      move/and3P: hty => [] wfp wfindis wfisort.
      have ond : on_udecl_prop Σ (ind_universes mdecl).
      { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      }
      eapply univ_wf_ctx_universes_closed in wfp => //.
      eapply univ_wf_ctx_universes_closed in wfindis => //.
      rewrite (consistent_instance_length H2).
      erewrite closedu_compare_decls; tea.
      rewrite univ_closed_ind_predicate_context // /=.
      unfold test_branch.
      apply/andP; split.
      * have wfbrctx : All (fun cdecl =>
          test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (cstr_args cdecl))
          (ind_ctors idecl).
        { pose proof (onConstructors := onConstructors X3).
          clear -wf ond onConstructors.
          red in onConstructors. solve_all. destruct X.
          move : on_ctype => /andP[] /andP[] /= _ wfty _.
          rewrite cstr_eq in wfty.
          rewrite !wf_universes_it_mkProd_or_LetIn in wfty.
          move/and3P: wfty => [] _ clargs _.
          apply univ_wf_ctx_universes_closed in clargs => //. }
        solve_all.
        erewrite closedu_compare_decls; [|tea].
        rewrite /cstr_branch_context.
        eapply closedu_expand_lets_ctx.
        rewrite wfp. eapply closedu_subst_context.
        rewrite a.
        now rewrite univ_closedu_inds.
      * rewrite wf_universes_it_mkLambda_or_LetIn H7 andb_true_r.
        move: H4.
        rewrite /wf_ctx_universes forallb_app => /andP[hctx _].
        apply (MRReflect.introT onctxP).
        solve_all. unfold ondecl, wf_decl_universes, on_decl_universes in *.
        move/andP:H3 => [Hb Ht] //; split; tas.
        now destruct decl_body.

    - rewrite /subst1. rewrite wf_universes_subst.
      constructor => //. eapply All_rev.
      rewrite wf_universes_mkApps in H2.
      move/andP: H2 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_invE univ_wf_universes_weakenE wf X isdecl).
      destruct (declared_inductive_invE); simpl in *.
      destruct ind_ctors as [|cs []] => //.
      destruct ind_cunivs as [|cunivs []] => //;
      destruct X0 as [[[? ?] ?] ?] => //.
      red in o0.
      destruct nth_error eqn:heq => //.
      destruct o0  as [_ ->].
      rewrite wf_universes_mkApps {1}/wf_universes /= -!/(wf_universes _ _)
        wf_universeb_instance_forall in H2.
      move/andP: H2 => [/wf_instanceP wfu wfargs].
      unshelve eapply declared_projection_to_gen in isdecl; eauto.
      eapply (wf_universes_inst_proved (ind_universes mdecl)); eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 (proj1 isdecl)))).
      rewrite wf_universes_subst.
      eapply wf_universes_inds; eauto.
      eapply wf_abstract_instance.
      rewrite wf_universes_subst. apply wf_projs.
      rewrite wf_universes_lift.
      rewrite smash_context_app smash_context_acc in heq.
      autorewrite with len in heq. rewrite nth_error_app_lt in heq.
      autorewrite with len. lia.
      rewrite PCUICSubstitution.nth_error_subst_context in heq.
      autorewrite with len in heq. simpl in heq.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl)) _ _).
      autorewrite with len in H0. simpl in H0. rewrite -> H0 in heq. clear H0.
      autorewrite with len in heq.
      simpl in heq.
      destruct nth_error eqn:hnth; simpl in * => //.
      noconf heq. simpl.
      rewrite wf_universes_subst.
      apply wf_extended_subst.
      move:onArityRed => /andP[] /andP[] /= _ Hs _.
      rewrite !wf_universes_it_mkProd_or_LetIn in Hs.
      now move/andP: Hs => /andP /andP [].
      rewrite wf_universes_lift.
      eapply PCUICWfUniverses.wf_universes_local_ctx_smash in s.
      eapply wf_universes_local_ctx_nth_error in s; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - apply/andP; split; eauto.
      destruct X0; cbn => //.
      rtoProp; intuition eauto. solve_all.
      destruct X0; cbn => //.
      simp prim_type. cbn. rtoProp; intuition.
Qed.

End univ_WfTypesE.

(** T0 row 36 [typing_wf_universes]: base [PCUICWfUniverses.typing_wf_universes] over the port. *)
Lemma typing_wf_universes_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ : context} {t : term} {T : term}, wfE Σ -> Σ;;; Γ |-E t : T -> wf_universes Σ t && wf_universes Σ T.
Proof.
  intros Σ Γ t T wfΣ Hty.
  exact (env_propE_typing univ_WfTypesE.univ_wf_typesE _ wfΣ _ _ _ Hty).
Qed.
Definition typing_wf_universes_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@typing_wf_universes cf H) in exact T) := @typing_wf_universes_proved cf.

(** T0 row 35 [typing_wf_sort]: from row 36, base's proof. *)
Lemma typing_wf_sort_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ : context} {t : term} {s : sort}, wfE Σ -> Σ;;; Γ |-E t : tSort s -> wf_sort Σ s.
Proof.
  intros Σ Γ t s wfΣ Hty.
  apply typing_wf_universes_proved in Hty as [_ wfs]%andb_and; auto.
  cbn in wfs. now univ_to_wfu.
Qed.
Definition typing_wf_sort_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@typing_wf_sort cf H) in exact T) := @typing_wf_sort_proved cf.

(** T0 row 20 [isType_wf_universes]: from row 36, base's proof. *)
Lemma isType_wf_universes_proved {cf : checker_flags} :
  forall {Σ : global_env × universes_decl} {Γ : context} {T : term}, wfE Σ.1 -> isTypeE Σ Γ T -> wf_universes Σ T.
Proof.
  intros Σ Γ T wfΣ (_ & s & Hs & _).
  now eapply typing_wf_universes_proved in Hs as [HT _]%andb_and.
Qed.
Definition isType_wf_universes_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@isType_wf_universes cf H) in exact T) := @isType_wf_universes_proved cf.

(** [ConvTypedFacts.ctf_wf_universes] of EtaConv's [PCUICSafeConversionEtaFacts.v] @ [c7cbbe73] (class not
    in this branch), at [wt := welltypedE], [wfP := wf_extE]: row 36, as the base instance
    [conv_typed_facts_base] does with base [typing_wf_universes]. *)
Lemma ctf_wf_universes_proved {cf : checker_flags} :
  forall Σ Γ t, wf_extE Σ -> welltypedE Σ Γ t -> wf_universes Σ t.
Proof.
  intros Σ Γ t wfΣ [T typ].
  pose proof (typing_wf_universes_proved (Σ := Σ) (fst wfΣ) typ) as h.
  apply andb_prop in h as [h _]. exact h.
Qed.
Definition ctf_wf_universes_fits {cf : checker_flags} :
  forall Σ Γ t, wf_extE Σ -> welltypedE Σ Γ t -> wf_universes Σ t := @ctf_wf_universes_proved cf.

(** ** K7 T0 [isType_it_mkProd_or_LetIn] (row 47): base [PCUICInductiveInversion.isType_it_mkProd_or_LetIn]'s
    proof; the let case types [tLetIn] at [tSort s] through [typing_wf_sort_proved] (row 35) and the zeta
    step [red1_cumulSpec], included into [cumulSpecE] by [cumulSpec0_incl_E]. *)
Lemma isType_it_mkProd_or_LetIn_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ Δ : list context_decl} {T : term}, wfE Σ.1 -> isTypeE Σ (Γ,,, Δ) T -> isTypeE Σ Γ (it_mkProd_or_LetIn Δ T).
Proof.
  intros Σ Γ Δ T wfΣ. revert T.
  induction Δ as [|[na [b|] ty] Δ IHΔ].
  - now simpl.
  - intros T Hty.
    rewrite /= /mkProd_or_LetIn /=.
    eapply IHΔ.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    have wf : wf_localE Σ ((Γ ,,, Δ) ,, vdef na b ty) := typingE_wf_local Hs.
    apply All_local_env_tip in wf as [wf hd].
    eapply type_Cumul'.
    + eapply typeE_LetIn; [exact hd|exact Hs].
    + eapply isType_Sort; [exact (typing_wf_sort_proved (Σ := Σ) wfΣ Hs)|exact wf].
    + apply cumulSpec0_incl_E. eapply convSpec_cumulSpec, red1_cumulSpec. repeat constructor.
  - intros T (_ & s & Hs & _).
    apply IHΔ.
    have wf : wf_localE Σ ((Γ ,,, Δ) ,, vass na ty) := typingE_wf_local Hs.
    apply All_local_env_tip in wf as [_ hd].
    pose proof (lift_sorting_extract hd).
    eapply has_sort_isTypeE with (s := Sort.sort_of_product _ s).
    eapply typeE_Prod; eassumption.
Qed.
Definition isType_it_mkProd_or_LetIn_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isType_it_mkProd_or_LetIn cf H) in exact T) := @isType_it_mkProd_or_LetIn_proved cf.

(** ** K7 reduction facts and telescope inversions: U rows [closed_red_confluence], [closed_red_from_empty],
    [red_expand_let], [red_it_mkProd_or_LetIn_smash], [red_mkApps_smash_witness],
    [red_rec_arg_check_one_fix]; T0 rows [inversion_it_mkProd_or_LetIn], [ind_arity_relevant].
    Reduction is unchanged in E: the base proofs go through over [ClosedBodies Σ], which [wfE Σ] gives
    ([wfE_ClosedBodies]); three U rows are inhabited directly by lemmas landed in [PCUICSREtaConv]
    ([frac/eta] @ [da1eb84b]). Helpers carry the prefix [rdx_]. *)

(** [closed_red_confluence] (U): base [PCUICContextConversion.closed_red_confluence] over
    [red_confluence_cb] ([PCUICConfluence.v:4070]). *)
Lemma closed_red_confluence_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {t : term} {u : term} {v : term}, Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v -> ∑ v' : term, Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v'.
Proof.
  intros Σ wfΣ Γ t u v [clΓ clT r] [clΓ' clT' r'].
  pose proof (wfE_ClosedBodies Σ) as cbΣ.
  have clu : is_open_term Γ u := red_is_open_term_cb (cf := cf) (wfΣ := cbΣ) t u r clΓ clT.
  have clv : is_open_term Γ v := red_is_open_term_cb (cf := cf) (wfΣ := cbΣ) t v r' clΓ clT.
  destruct (PCUICConfluence.red_confluence_cb (Γ := exist Γ clΓ) (t := exist t clT) r r') as [v' [redl redr]].
  exists v'. split.
  - exact (into_closed_red redl clΓ clu).
  - exact (into_closed_red redr clΓ clv).
Qed.
Definition closed_red_confluence_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@closed_red_confluence cf H) in exact T) := @closed_red_confluence_proved cf.

(** [closed_red_from_empty] (U): inhabited by the landed [closed_red_from_empty_cb]
    ([pcuic/theories/PCUICSREtaConv.v:524], [frac/eta] @ [da1eb84b]), at [wfE_ClosedBodies Σ]. *)
Lemma closed_red_from_empty_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {M : term} {N : term}, on_free_vars_ctx xpred0 Γ -> closed M -> PCUICReduction.red Σ [] M N -> Σ ;;; Γ ⊢ M ⇝ N.
Proof.
  intros Σ wfΣ Γ M N.
  exact (@closed_red_from_empty_cb cf Σ (wfE_ClosedBodies Σ) Γ M N).
Qed.
Definition closed_red_from_empty_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@closed_red_from_empty cf H) in exact T) := @closed_red_from_empty_proved cf.

(** [red_expand_let] (U): inhabited by the landed [red_expand_letE] ([PCUICSREtaConv.v:512]). *)
Lemma red_expand_let_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {na : aname} {b : term} {ty : term} {t : term}, wf_localE Σ (Γ,,, [vdef na b ty]) -> on_free_vars (shiftnP #|Γ,,, [vdef na b ty]| (fun _ : nat => false)) t -> Σ ;;; Γ,, vdef na b ty ⊢ t ⇝ lift0 1 (t {0 := b}).
Proof.
  intros Σ wfΣ Γ na b ty t.
  exact (@red_expand_letE cf Σ wfΣ Γ na b ty t).
Qed.
Definition red_expand_let_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@red_expand_let cf H) in exact T) := @red_expand_let_proved cf.

(** [red_it_mkProd_or_LetIn_smash] (U): inhabited by the landed [red_it_mkProd_or_LetIn_smash_cb]
    ([PCUICSREtaConv.v:540]), at [wfE_ClosedBodies Σ]. *)
Lemma red_it_mkProd_or_LetIn_smash_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (ctx : context) (t : term) (u : term) (n : nat) (c : context_decl), Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> ∑ (ctx' : context) (t' : term) (d : context_decl), [× decompose_prod_assum [] u = (ctx', t'), nth_error (List.rev (smash_context [] ctx')) n = Some d & Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d].
Proof.
  intros Σ wfΣ.
  exact (@red_it_mkProd_or_LetIn_smash_cb cf Σ (wfE_ClosedBodies Σ)).
Qed.
Definition red_it_mkProd_or_LetIn_smash_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@red_it_mkProd_or_LetIn_smash cf H) in exact T) := @red_it_mkProd_or_LetIn_smash_proved cf.

(** The base proof scripts below come from [PCUICInductives.v] and [PCUICFixWitness.v]; they run with
    the settings and imports of [PCUICInductives.v] (all modules already loaded), kept local by the
    section. *)
Section RdxBaseScripts.
Import PCUICTactics PCUICInduction PCUICContexts PCUICSubstitution.
Local Set SimplIsCbn.
Local Arguments subst_context !s _ !Γ.
Local Arguments it_mkProd_or_LetIn !l _.

(** Base [PCUICInductives.red_it_mkProd_or_LetIn_to_smash] (:2268): its [wf] premise is unused, so the
    same script proves it with no environment premise. *)
Lemma rdx_red_it_mkProd_or_LetIn_to_smash {Σ : global_env_ext} Γ Δ T :
  is_closed_context Γ ->
  is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ T ⇝ it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
Proof.
  intros clΓ clt.
  eapply into_closed_red => //.
  clear clΓ clt.
  induction Δ in Γ, T |- * using ctx_length_rev_ind; simpl; auto.
  - rewrite expand_lets_nil. reflexivity.
  - rewrite PCUICContexts.smash_context_app_expand /=.
    destruct d as [na [b|] ty].
    * rewrite expand_lets_vdef {1}it_mkProd_or_LetIn_app /= subst_context_nil app_context_nil_l.
      rewrite PCUICContexts.expand_lets_smash_context /= PCUICContexts.expand_lets_k_ctx_nil.
      rewrite /expand_lets_ctx /expand_lets_k_ctx /= subst_empty lift0_id lift0_context.
      rewrite /mkProd_or_LetIn /=.
      etransitivity.
      + eapply red1_red, red_zeta.
      + rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
        now eapply X; len.
    * rewrite expand_lets_vass it_mkProd_or_LetIn_app /=.
      rewrite it_mkProd_or_LetIn_app /=.
      eapply red_prod. reflexivity.
      rewrite PCUICContexts.expand_lets_smash_context /= PCUICContexts.expand_lets_k_ctx_nil.
      rewrite expand_lets_ctx_assumption_context. repeat constructor.
      now eapply X.
Qed.

(** [red_mkApps_smash_witness] (U): the script of base [PCUICFixWitness.red_mkApps_smash_witness]. *)
Lemma red_mkApps_smash_witness_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {C : term} {ctx : context} {i : inductive} {u : Instance.t} {l : list term}, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) -> ∑ l' : list term, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (mkApps (tInd i u) l').
Proof.
  intros Σ wfΣ Γ C ctx i u l r.
  pose proof (wfE_ClosedBodies Σ) as cbΣ.
  have clΓ := clrel_ctx r.
  have opr : is_open_term Γ (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l))
    := closed_red_open_right_cb (cf := cf) r.
  have h : Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) ⇝
           it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx (mkApps (tInd i u) l)).
  { now eapply rdx_red_it_mkProd_or_LetIn_to_smash. }
  rewrite expand_lets_mkApps in h.
  rewrite /expand_lets /expand_lets_k /= in h.
  eexists.
  transitivity (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l)); [exact r|exact h].
Qed.

(** Base [PCUICInductives.closed_red_it_mkProd_or_LetIn_assum_nth] (:2246): its [wf] premise is unused. *)
Lemma rdx_closed_red_it_mkProd_or_LetIn_assum_nth {Σ : global_env_ext} Γ sctx T n c A' :
  assumption_context sctx ->
  is_open_term Γ (it_mkProd_or_LetIn sctx T) ->
  nth_error (List.rev sctx) n = Some c ->
  Σ ;;; Γ ,,, skipn (#|sctx| - n) sctx ⊢ decl_type c ⇝ A' ->
  ∑ sctx',
    [× assumption_context sctx',
       #|sctx'| = #|sctx|,
       nth_error (List.rev sctx') n = Some (vass (decl_name c) A'),
       (forall i, i <> n -> nth_error (List.rev sctx') i = nth_error (List.rev sctx) i) &
       Σ ;;; Γ ⊢ it_mkProd_or_LetIn sctx T ⇝ it_mkProd_or_LetIn sctx' T].
Proof.
  intros ass op hnth hred.
  have clΓ : is_closed_context Γ.
  { move: (clrel_ctx hred). rewrite on_free_vars_ctx_app => /andP[] //. }
  destruct (PCUICInductives.red_it_mkProd_or_LetIn_assum_nth (Σ := Σ) Γ sctx T n c A' ass hnth (clrel_rel hred))
    as [sctx' [ass' hlen hnth' hother r]].
  exists sctx'; split; try assumption.
  now apply into_closed_red.
Qed.

(** [red_rec_arg_check_one_fix] (U): the script of base [PCUICInductives.red_rec_arg_check_one_fix]
    over the two helpers above. *)
Lemma red_rec_arg_check_one_fix_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (d : def term) (ctx : context) (concl : term) (c : context_decl) (ind : inductive) (u : Instance.t) (args : list term), on_free_vars (shiftnP #|Γ| xpred0) (dtype d) -> decompose_prod_assum [] (dtype d) = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) (rarg d) = Some c -> Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - rarg d) (smash_context [] ctx) ⊢ decl_type c ⇝ mkApps (tInd ind u) args -> has_rec_arg d × (∑ ty : term, Σ ;;; Γ ⊢ dtype d ⇝ ty × check_one_fix (def_with_type d ty) = Some (inductive_mind ind)).
Proof.
  intros Σ wfΣ Γ d ctx concl c ind u args op decomp hnth hred.
  pose proof (wfE_ClosedBodies Σ) as cbΣ.
  have clΓ : is_closed_context Γ.
  { move: (clrel_ctx hred). rewrite on_free_vars_ctx_app => /andP[] //. }
  have eqty := PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp.
  cbn in eqty.
  have r1 : Σ ;;; Γ ⊢ dtype d ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx concl).
  { rewrite eqty. apply rdx_red_it_mkProd_or_LetIn_to_smash => //. now rewrite -eqty. }
  have ass : assumption_context (smash_context [] ctx).
  { apply PCUICContexts.smash_context_assumption_context; constructor. }
  destruct (rdx_closed_red_it_mkProd_or_LetIn_assum_nth Γ _ _ _ _ _ ass (closed_red_open_right_cb (cf := cf) r1) hnth hred)
    as [sctx' [ass' hlen hnth' _ r2]].
  split.
  - have hlt := nth_error_Some_length hnth. rewrite List.length_rev smash_context_length /= in hlt.
    rewrite /has_rec_arg decomp /=. now apply Nat.ltb_lt.
  - exists (it_mkProd_or_LetIn sctx' (expand_lets ctx concl)). split.
    + now transitivity (it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx concl)).
    + eapply PCUICInductives.check_one_fix_it_mkProd_or_LetIn_assum; [exact ass'|exact hnth'|reflexivity].
Qed.

End RdxBaseScripts.

Definition red_mkApps_smash_witness_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@red_mkApps_smash_witness cf H) in exact T) := @red_mkApps_smash_witness_proved cf.
Definition red_rec_arg_check_one_fix_fits {cf : checker_flags} (H : U_facts) : ltac:(let T := type of (@red_rec_arg_check_one_fix cf H) in exact T) := @red_rec_arg_check_one_fix_proved cf.

(** ** T0 rows [ind_arity_relevant] and [inversion_it_mkProd_or_LetIn] *)

(** A sort comparison as a [ws_cumul_pbE] between the two sorts. *)
Lemma rdx_sort_le {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {a b : sort} :
  is_closed_context Γ -> leq_sort Σ a b -> Σ ;;; Γ ⊢E tSort a ≤ tSort b.
Proof.
  intros clΓ h.
  apply into_ws_cumul_pbE_spec; [|exact clΓ|reflexivity|reflexivity].
  apply eq_term_upto_univ_cumulSpec. constructor. exact h.
Qed.

(** The let-in step of row 9's route (hyp-audit-C §3.5 row 9): [ws_cumul_pbE_LetIn_l_inv]
    ([PCUICEtaA6.v:361]), [red_expand_letE], [weakening_ws_cumul_pbE] ([PCUICWsCumulEtaSubst.v:189]). *)
Lemma rdx_letin_le_sort {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname}
  {b B A : term} {s : sort} :
  wf_localE Σ (Γ ,, vdef na b B) -> is_open_term (Γ ,, vdef na b B) A ->
  Σ ;;; Γ ⊢E tLetIn na b B A ≤ tSort s -> Σ ;;; Γ ,, vdef na b B ⊢E A ≤ tSort s.
Proof.
  intros wfΓ opA c.
  have c1 : Σ ;;; Γ ⊢E A {0 := b} ≤ tSort s by exact (ws_cumul_pbE_LetIn_l_inv c).
  have clΓ : is_closed_context (Γ ,,, [vdef na b B]) by exact (wf_local_closed_contextE wfΓ).
  have w : Σ ;;; Γ ,, vdef na b B ⊢E lift0 1 (A {0 := b}) ≤ tSort s
    by exact (weakening_ws_cumul_pbE (Γ := Γ) (Γ' := []) (Γ'' := [vdef na b B]) c1 clΓ).
  have r : Σ ;;; Γ ,, vdef na b B ⊢ A ⇝ lift0 1 (A {0 := b}) by exact (@red_expand_letE cf Σ wfΣ Γ na b B A wfΓ opA).
  exact (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ (red_ws_cumul_pb (pb := Cumul) r) w).
Qed.

(** Inversion of a typed telescope that stops before the final cumulativity: the body has a type
    below the telescope's sort. Unlike [inversion_it_mkProd_or_LetIn], it needs no [wf_sort] of that
    sort, because it never retypes the body at it. *)
Lemma rdx_inversion_it_mkProd_or_LetIn_le {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  (Δ : context) : forall (Γ : context) (T X : term) (s : sort),
  Σ ;;; Γ |-E it_mkProd_or_LetIn Δ T : X -> Σ ;;; Γ ⊢E X ≤ tSort s ->
  ∑ X' : term, Σ ;;; Γ ,,, Δ |-E T : X' × Σ ;;; Γ ,,, Δ ⊢E X' ≤ tSort s.
Proof.
  induction Δ as [|d Δ IH]; intros Γ T X s h c.
  - exists X. split; assumption.
  - destruct (IH Γ (mkProd_or_LetIn d T) X s h c) as [X1 [h1 c1]].
    destruct d as [na [b|] ty]; cbn [mkProd_or_LetIn decl_body decl_name decl_type] in h1.
    + destruct (inversion_LetIn Σ wfΣ h1) as [A [_ [hA cA]]].
      exists A. split; [exact hA|].
      apply rdx_letin_le_sort.
      * exact (typingE_wf_local hA).
      * exact (type_is_open_termE hA).
      * exact (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ cA c1).
    + destruct (inversion_Prod Σ wfΣ h1) as [s1 [s2 [_ [hB cB]]]].
      exists (tSort s2). split; [exact hB|].
      have clΓ : is_closed_context (Γ ,,, Δ ,, vass na ty) by exact (wf_local_closed_contextE (typingE_wf_local hB)).
      have hle : leq_sort Σ (Sort.sort_of_product s1 s2) s
        by exact (ws_cumul_pbE_Sort_inv Cumul (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ cB c1)).
      exact (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _
               (rdx_sort_le clΓ (leq_sort_product _ s1 s2)) (rdx_sort_le clΓ hle)).
Qed.

(** [ind_arity_relevant] (T0, row 7): base [PCUICInductiveInversion.ind_arity_relevant] with
    [rdx_inversion_it_mkProd_or_LetIn_le] in place of [inversion_it_mkProd_or_LetIn], then K7
    [inversion_Sort], [ws_cumul_pbE_Sort_inv] ([PCUICEtaA6.v:176]), [leq_relevance], [relevance_super]. *)
Lemma ind_arity_relevant_proved {cf : checker_flags} : forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in isTypeE Σ [] ind_type -> isTypeRelE Σ [] ind_type rel_of_Type.
Proof.
  intros Σ mdecl idecl wfΣ ind_type (_ & s & Hs & _ & _).
  repeat (eexists; tea). cbn in Hs |- *.
  rewrite /ind_type in Hs.
  rewrite -it_mkProd_or_LetIn_app in Hs.
  destruct (rdx_inversion_it_mkProd_or_LetIn_le (wfΣ := wfΣ) _ _ _ _ s Hs (typing_ws_cumul_pbE (le := Cumul) Hs))
    as [X [hX cX]].
  destruct (inversion_Sort Σ wfΣ hX) as [_ [_ cS]].
  have hle : leq_sort Σ (Sort.super (ind_sort idecl)) s
    by exact (ws_cumul_pbE_Sort_inv Cumul (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ cS cX)).
  eapply leq_relevance; tea.
  eapply relevance_super.
Qed.
Definition ind_arity_relevant_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@ind_arity_relevant cf H) in exact T) := @ind_arity_relevant_proved cf.

(** [inversion_it_mkProd_or_LetIn] (T0, row 9): base [PCUICSpine.inversion_it_mkProd_or_LetIn] reaches
    the body's sort through [type_it_mkProd_or_LetIn_inv]; here [rdx_inversion_it_mkProd_or_LetIn_le]
    gives a type of the body below [tSort s], and K7 [type_ws_cumul_pb] retypes it at [tSort s], whose
    well-formedness is [typing_wf_sort_proved] (row 35, above). *)
Lemma inversion_it_mkProd_or_LetIn_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {t : term} {s : sort}, Σ;;; Γ |-E it_mkProd_or_LetIn Δ t : tSort s -> Σ;;; Γ,,, Δ |-E t : tSort s.
Proof.
  intros Σ wfΣ Γ Δ t s h.
  destruct (rdx_inversion_it_mkProd_or_LetIn_le Δ Γ t (tSort s) s h (typing_ws_cumul_pbE (le := Cumul) h))
    as [X [hX cX]].
  apply (type_ws_cumul_pb (pb := Cumul) X hX); [|exact cX].
  apply isType_Sort; [exact (typing_wf_sort_proved wfΣ h)|exact (typingE_wf_local hX)].
Qed.
Definition inversion_it_mkProd_or_LetIn_fits {cf : checker_flags} (H : T0_facts) : ltac:(let T := type of (@inversion_it_mkProd_or_LetIn cf H) in exact T) := @inversion_it_mkProd_or_LetIn_proved cf.

(** ** K7 substitution and spine facts: T0 rows 30, 31, 14, 34, 27, 2, 6 (helpers [sbs_*]) *)

(** [PCUICSubstitution.subslet_untyped_subslet] over [subsletE]. *)
Lemma sbs_subsletE_untyped {cf : checker_flags} {Σ : global_env_ext} {Γ s Δ} :
  subsletE Σ Γ s Δ -> PCUICSubstitution.untyped_subslet Γ s Δ.
Proof. induction 1; constructor; auto. Qed.

(** [PCUICSubstitution.subslet_nth_error] over [subsletE]. *)
Lemma sbs_subsletE_nth_error {cf : checker_flags} {Σ Γ s Δ decl n} :
  subsletE Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  ∑ t, nth_error s n = Some t ×
  let ty := subst0 (skipn (S n) s) (decl_type decl) in
  Σ ;;; Γ |-E t : ty ×
  match decl_body decl return Type with
  | Some t' =>
    let b := subst0 (skipn (S n) s) t' in
    (t = b)
  | None => unit
  end.
Proof.
  intros h; induction h as [|Δ s na t T h IH ht|Δ s na t T h IH ht] in n |- *.
  - intros hn. rewrite nth_error_nil in hn. discriminate.
  - destruct n as [|n]; cbn.
    + intros [= <-]. exists t. split; [reflexivity|]. cbn. split; [exact ht|exact tt].
    + intros hn. exact (IH n hn).
  - destruct n as [|n]; cbn.
    + intros [= <-]. exists (subst0 s t). split; [reflexivity|]. cbn. split; [exact ht|reflexivity].
    + intros hn. exact (IH n hn).
Qed.

(** The terms of a [subsletE] are open in its context. *)
Lemma sbs_subsletE_open {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ s Δ} :
  subsletE Σ Γ s Δ -> forallb (is_open_term Γ) s.
Proof.
  intros h; induction h as [|Δ s na t T h IH ht|Δ s na t T h IH ht]; cbn [forallb].
  - reflexivity.
  - rewrite IH andb_true_r. exact (subject_is_open_termE ht).
  - rewrite IH andb_true_r. exact (subject_is_open_termE ht).
Qed.

Section SbsSigma.
  Local Open Scope sigma_scope.
  Local Set Keyed Unification.

  (** [PCUICSubstitution.subslet_well_subst] over [subsletE] / [well_substE]; base's proof. *)
  Lemma sbs_subslet_well_substE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ} :
    subsletE Σ Γ s Γ' ->
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ->
    well_substE Σ (Γ ,,, Γ' ,,, Δ) (⇑^#|Δ| (s ⋅n ids)) (Γ ,,, subst_context s 0 Δ).
  Proof.
    intros hs hsΔ. split.
    2: exact (PCUICSubstitution.subslet_usubst (sbs_subsletE_untyped hs)).
    intros x decl hx. rewrite PCUICInstConv.lift0_inst inst_assoc. revert hx.
    case: nth_error_app_context => //.
    { intros d hnth hn [= ->].
      rewrite {1}Upn_eq subst_consn_lt; len => //. rewrite /subst_fn.
      rewrite idsn_lt //.
      eapply meta_convE.
      - econstructor; auto.
        rewrite nth_error_app_lt; len => //.
        now rewrite PCUICSubstitution.nth_error_subst_context hnth.
      - rewrite /subst_decl. simpl.
        sigma. rewrite -shiftk_shift -subst_compose_assoc -shiftk_shift.
        rewrite subst_shift_comm.
        rewrite -subst_fn_subst_consn. lia_f_equal. }
    { intros n hnth; len; intros hd [= ->].
      pose proof (subslet_length hs) as H.
      move: hnth; case: nth_error_app_context => //.
      * intros n hnth hx [= ->].
        rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
        rewrite subst_consn_compose.
        rewrite subst_consn_lt; len; try lia.
        unfold subst_fn. rewrite nth_error_map.
        destruct (sbs_subsletE_nth_error hs hnth) as [t [hnths [hty hb]]].
        rewrite hnths /=. sigma in hty.
        eapply meta_convE in hty.
        2:now rewrite skipn_subst ?Upn_0; try lia.
        eapply (shift_typingE (Δ := subst_context s 0 Δ)) in hty.
        2:tas.
        2:now len.
        rewrite inst_assoc in hty.
        rewrite Upn_eq.
        eapply meta_convE; eauto.
        eapply inst_ext.
        rewrite (shift_subst_consn_ge (S x)); len; try lia.
        rewrite subst_compose_assoc.
        now replace (S x - #|Δ|) with (S (x - #|Δ|)) by lia.
      * intros n hnth hn [= ->].
        eapply meta_conv_allE.
        2:reflexivity.
        2:{ rewrite Upn_subst_consn_ge; try lia. rewrite compose_ids_l.
            instantiate (1 := tRel (x - #|s|)).
            rewrite /shiftk. lia_f_equal. }
        2:{ econstructor; eauto. }
        eapply meta_convE.
        { econstructor; tas.
          rewrite nth_error_app_context_ge; len; try lia.
          rewrite H. erewrite <- hnth. lia_f_equal. }
        rewrite PCUICInstConv.lift0_inst.
        rewrite Upn_eq.
        rewrite shift_subst_consn_ge; len; try lia.
        rewrite subst_consn_compose shift_subst_consn_ge; len; try lia.
        rewrite H. rewrite shiftk_compose. lia_f_equal.
    }
  Qed.
End SbsSigma.

(** *** Row 31: [substitution_wf_local] (base [PCUICSubstitution.All_local_env_inst], over [type_instE]) *)
Lemma substitution_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl}, subsletE Σ Γ s Γ' -> wf_localE Σ (Γ,,, Γ',,, Δ) -> wf_localE Σ (Γ,,, subst_context s 0 Δ).
Proof.
  intros Σ wfΣ Γ Γ' s Δ hs wf.
  pose proof (env_propE_wf_local type_instE Σ wfΣ _ wf) as X. cbv beta in X.
  eapply All_local_env_app_inv in X as [_ XΔ].
  have wfΓ : wf_localE Σ Γ.
  { apply wf_localE_app_l in wf. exact (wf_localE_app_l _ _ _ wf). }
  rewrite PCUICInstConv.subst_context_inst_context.
  eapply (wf_local_app_instE _ (Γ ,,, Γ')); [exact XΔ| |exact wfΓ].
  pose proof (sbs_subslet_well_substE (Δ := []) hs) as hw.
  rewrite subst_context_nil in hw. exact (hw wfΓ).
Qed.
Definition substitution_wf_local_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@substitution_wf_local cf H) in exact T) := @substitution_wf_local_proved cf.

(** *** Row 30: [substitution] (base [PCUICSubstitution.substitution_prop]: [type_inst] + [subslet_well_subst]) *)
Lemma substitution_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl} {t : term} {T : term}, subsletE Σ Γ s Γ' -> Σ;;; Γ,,, Γ',,, Δ |-E t : T -> Σ;;; Γ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros Σ wfΣ Γ Γ' s Δ t T hs ht.
  pose proof (substitution_wf_local_proved (wfΣ := wfΣ) hs (typingE_wf_local ht)) as wfΔ.
  rewrite !subst_inst.
  exact (typing_instE Σ _ t T _ _ wfΔ (sbs_subslet_well_substE hs wfΔ) ht).
Qed.
Definition substitution_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@substitution cf H) in exact T) := @substitution_proved cf.

(** [PCUICSubstitution.isType_subst] over E. *)
Lemma sbs_isType_subst {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ s T} :
  subsletE Σ Γ s Δ -> isTypeE Σ (Γ ,,, Δ) T -> isTypeE Σ Γ (subst0 s T).
Proof.
  intros hs (_ & u & hu & _).
  apply (has_sort_isTypeE u).
  exact (substitution_proved (Δ := []) hs hu).
Qed.

(** *** Row 14: [isType_apply] ([PCUICArities.isType_apply]: [isType_tProd] + [isType_subst]) *)
Lemma isType_apply_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term} {t : term}, isTypeE Σ Γ (tProd na A B) -> Σ;;; Γ |-E t : A -> isTypeE Σ Γ (B {0 := t}).
Proof.
  intros Σ wfΣ Γ na A B t (_ & s & hs & _) ht.
  destruct (inversion_Prod Σ wfΣ hs) as (s1 & s2 & _ & hB & _).
  apply (has_sort_isTypeE s2).
  exact (substitution_proved (Γ' := [vass na A]) (Δ := []) (subslet_ass_tip ht) hB).
Qed.
Definition isType_apply_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@isType_apply cf H) in exact T) := @isType_apply_proved cf.

(** *** Row 34: [typing_spine_strengthen] (the head cumulativity composes: [ws_cumul_pbE_trans]) *)
Lemma typing_spine_strengthen_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {args : list term} {U : term}, typing_spineE Σ Γ T args U -> forall T' : term, isTypeE Σ Γ T' -> Σ ;;; Γ ⊢E T' ≤ T -> typing_spineE Σ Γ T' args U.
Proof.
  intros Σ wfΣ Γ T args U sp.
  destruct sp as [ty ty' isty isty' c'|ty hd tl na A B B' isty isP c' hhd sp]; intros T' isT' c.
  - exact (type_spine_nilE Σ Γ T' ty' isT' isty'
      (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul Γ _ _ _ c c')).
  - exact (type_spine_consE Σ Γ T' hd tl na A B B' isT' isP
      (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul Γ _ _ _ c c') hhd sp).
Qed.
Definition typing_spine_strengthen_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@typing_spine_strengthen cf H) in exact T) := @typing_spine_strengthen_proved cf.

(** *** Row 27: [spine_subst_cumul] ([PCUICSpine.subslet_cumul] + [spine_subst_cumul]) *)
Lemma sbs_subsletE_vass_inv {cf : checker_flags} {Σ Γ args Δ na T} :
  subsletE Σ Γ args (Δ ,, vass na T) ->
  ∑ t s, (args = t :: s) × subsletE Σ Γ s Δ × (Σ ;;; Γ |-E t : subst0 s T).
Proof.
  intros h. DepElim.depelim h. eexists _, _. split; [reflexivity|split; eassumption].
Qed.

Lemma sbs_context_subst_cumul {cf : checker_flags} {Σ : global_env_ext} {pb Δ Γ Γ' args s} :
  PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' ->
  ws_cumul_ctx_pbE_rel pb Σ Δ Γ Γ' ->
  context_subst Γ args s -> context_subst Γ' args s.
Proof.
  intros ass ass' [_ hA].
  induction hA as [|d d' Γ0 Γ0' hA IH p] in args, s, ass, ass' |- *; intros ctxs.
  - exact ctxs.
  - destruct d as [na [b|] T]; [exfalso; inversion ass|].
    destruct d' as [na' [b'|] T']; [exfalso; inversion ass'|].
    have ass0 : PCUICLiftSubst.assumption_context Γ0 by inversion ass.
    have ass0' : PCUICLiftSubst.assumption_context Γ0' by inversion ass'.
    DepElim.depelim ctxs. constructor. eapply IH; eassumption.
Qed.

Lemma sbs_subsletE_cumul {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {pb Δ args Γ Γ'} :
  PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' ->
  wf_localE Σ (Δ ,,, Γ) -> wf_localE Σ (Δ ,,, Γ') ->
  ws_cumul_ctx_pbE_rel pb Σ Δ Γ Γ' ->
  subsletE Σ Δ args Γ -> subsletE Σ Δ args Γ'.
Proof.
  intros ass ass' wf wf' [cl hA].
  induction hA as [|d d' Γ0 Γ0' hA IH p] in args, ass, ass', wf, wf' |- *; intros subsl.
  - exact subsl.
  - destruct d as [na [b|] T]; [exfalso; inversion ass|].
    destruct d' as [na' [b'|] T']; [exfalso; inversion ass'|].
    have ass0 : PCUICLiftSubst.assumption_context Γ0 by inversion ass.
    have ass0' : PCUICLiftSubst.assumption_context Γ0' by inversion ass'.
    destruct (sbs_subsletE_vass_inv subsl) as (t & s & -> & subsl' & ht).
    destruct (All_local_env_tip wf) as [wf0 _].
    destruct (All_local_env_tip wf') as [wf0' hT'].
    have subsl'' : subsletE Σ Δ s Γ0'.
    { eapply IH; eassumption. }
    constructor; [exact subsl''|].
    DepElim.depelim p.
    apply (type_ws_cumul_pb (pb := pb) (subst0 s T) ht).
    + destruct hT' as (_ & u & hu & _).
      apply (has_sort_isTypeE u).
      exact (substitution_proved (Δ := []) subsl'' hu).
    + refine (untyped_substitution_ws_cumul_pbE (Γ'' := []) (M := T) (N := T')
        (sbs_subsletE_untyped subsl') (sbs_subsletE_open subsl') _).
      eassumption.
Qed.

Lemma spine_subst_cumul_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Δ : list context_decl} {args : list term} {Γ : context} {Γ' : context}, PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' -> wf_localE Σ (Δ,,, Γ) -> wf_localE Σ (Δ,,, Γ') -> ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' -> spine_substE Σ Δ args (List.rev args) Γ -> spine_substE Σ Δ args (List.rev args) Γ'.
Proof.
  intros Σ wfΣ Δ args Γ Γ' ass ass' wf wf' a2 [wfΔ _ ctxs subsl].
  split.
  - exact wfΔ.
  - exact wf'.
  - exact (sbs_context_subst_cumul ass ass' a2 ctxs).
  - exact (sbs_subsletE_cumul ass ass' wf wf' a2 subsl).
Qed.
Definition spine_subst_cumul_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@spine_subst_cumul cf H) in exact T) := @spine_subst_cumul_proved cf.

(** *** Row 6: [ctx_inst_spine_subst] ([PCUICSpine.ctx_inst_spine_subst]) *)

(** [PCUICSubstitution.subslet_def_tip] over [subsletE]. *)
Lemma sbs_subslet_def_tip {cf : checker_flags} {Σ : global_env_ext} {Γ na t T} :
  Σ ;;; Γ |-E t : T -> subsletE Σ Γ [t] [vdef na t T].
Proof.
  intros h. rewrite -{1}(subst_empty 0 t).
  apply cons_let_defE; [constructor|]. now rewrite !subst_empty.
Qed.

(** The substitution of a [ctx_instE] over a reversed context is a [subsletE]
    (the [subslet] half of [PCUICSpine.ctx_inst_spine_subst], by induction on the instance). *)
Lemma sbs_ctx_inst_subslet {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ args Δt}
  (ci : ctx_instE Σ Γ args Δt) :
  wf_localE Σ (Γ ,,, List.rev Δt) -> subsletE Σ Γ (ctx_inst_subE ci) (List.rev Δt).
Proof.
  induction ci as [|na t i inst Δt hi ci IH|na b t inst Δt ci IH]; intros wf;
    cbn [ctx_inst_subE List.rev] in *.
  - constructor.
  - have e : List.rev (subst_telescope [i] 0 Δt) = subst_context [i] 0 (List.rev Δt).
    { rewrite -{1}(List.rev_involutive Δt) subst_telescope_subst_context. apply List.rev_involutive. }
    have hs : subsletE Σ Γ [i] [vass na t] := subslet_ass_tip hi.
    have wf' : wf_localE Σ (Γ ,,, [vass na t] ,,, List.rev Δt) by rewrite -app_context_assoc.
    rewrite e in IH.
    exact (stc_subsletE_app _ _ _ _ _ _ (IH (substitution_wf_local_proved (wfΣ := wfΣ) hs wf')) hs).
  - have wfd : wf_localE Σ (Γ ,,, [vdef na b t] ,,, List.rev Δt) by rewrite -app_context_assoc.
    destruct (All_local_env_tip (wf_localE_app_l _ _ _ wfd)) as [_ hd0].
    have hb : Σ ;;; Γ |-E b : t by destruct hd0 as (hb & _).
    have hs : subsletE Σ Γ [b] [vdef na b t] := sbs_subslet_def_tip hb.
    have e : List.rev (subst_telescope [b] 0 Δt) = subst_context [b] 0 (List.rev Δt).
    { rewrite -{1}(List.rev_involutive Δt) subst_telescope_subst_context. apply List.rev_involutive. }
    rewrite e in IH.
    exact (stc_subsletE_app _ _ _ _ _ _ (IH (substitution_wf_local_proved (wfΣ := wfΣ) hs wfd)) hs).
Qed.

Lemma ctx_inst_spine_subst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {args : list term}, wf_localE Σ (Γ,,, Δ) -> forall (ci : ctx_instE Σ Γ args (List.rev Δ)), spine_substE Σ Γ args (ctx_inst_subE ci) Δ.
Proof.
  intros Σ wfΣ Γ Δ args wf ci.
  pose proof (make_context_subst_spec _ _ _ (stc_ctx_inst_subE_spec ci)) as msub.
  rewrite List.rev_involutive in msub.
  pose proof (sbs_ctx_inst_subslet (wfΣ := wfΣ) ci) as hs.
  rewrite List.rev_involutive in hs.
  split.
  - exact (wf_localE_app_l _ _ _ wf).
  - exact wf.
  - exact msub.
  - exact (hs wf).
Qed.
Definition ctx_inst_spine_subst_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@ctx_inst_spine_subst cf H) in exact T) := @ctx_inst_spine_subst_proved cf.

(** *** Row 2: [arity_typing_spine] ([PCUICSpine.arity_typing_spine]) *)

(** [PCUICArities.isType_tLetIn_red] over E: substitution (row 30), [ws_cumul_pbE_LetIn_l_inv],
    [type_ws_cumul_pb], and [typing_wf_sort_proved] (row 35) for the target sort; no
    [ws_cumul_pb_Sort_r_inv]. *)
Lemma sbs_isType_tLetIn_red {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na t A B} :
  isTypeE Σ Γ (tLetIn na t A B) -> isTypeE Σ Γ (B {0 := t}).
Proof.
  intros (_ & s & H & _).
  pose proof (typing_wf_sort_proved (Σ := Σ) wfΣ H) as ws.
  destruct (inversion_LetIn Σ wfΣ H) as (A' & hb & HB & c).
  assert (ht : Σ ;;; Γ |-E t : A) by (destruct hb as (ht & _); exact ht).
  assert (HB' : Σ ;;; Γ |-E B {0 := t} : A' {0 := t}).
  { exact (substitution_proved (wfΣ := wfΣ) (Γ' := [vdef na t A]) (Δ := []) (sbs_subslet_def_tip ht) HB). }
  apply (has_sort_isTypeE s).
  exact (type_ws_cumul_pb (pb := Cumul) (A' {0 := t}) HB' (isType_Sort ws (typingE_wf_local HB'))
    (ws_cumul_pbE_LetIn_l_inv c)).
Qed.

(** [PCUICArities.typing_spine_letin_inv] over E. *)
Lemma sbs_typing_spine_letin_inv {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na b B T args S} :
  typing_spineE Σ Γ (tLetIn na b B T) args S -> typing_spineE Σ Γ (T {0 := b}) args S.
Proof.
  intros Hsp. remember (tLetIn na b B T) as L eqn:eL. revert eL.
  destruct Hsp as [ty ty' isty isty' c|ty hd tl na' A B0 B' isty isP c hhd sp]; intros ->.
  - exact (type_spine_nilE Σ Γ _ ty' (sbs_isType_tLetIn_red isty) isty' (ws_cumul_pbE_LetIn_l_inv c)).
  - exact (type_spine_consE Σ Γ _ hd tl na' A B0 B' (sbs_isType_tLetIn_red isty) isP
      (ws_cumul_pbE_LetIn_l_inv c) hhd sp).
Qed.

Lemma sbs_context_subst_def_tip na b ty : context_subst [vdef na b ty] [] [b].
Proof. rewrite -{2}(subst_empty 0 b). exact (context_subst_def [] [] [] na b ty context_subst_nil). Qed.

Lemma sbs_context_subst_ass_tip na ty a : context_subst [vass na ty] [a] [a].
Proof. exact (context_subst_ass [] [] [] na ty a context_subst_nil). Qed.

Lemma arity_typing_spine_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : sort} {inst : list term} {s' : sort}, typing_spineE Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') -> [× #|inst| = context_assumptions Γ', leq_sort Σ s s' & ∑ instsubst : list term, spine_substE Σ Γ inst instsubst Γ'].
Proof.
  intros Σ wfΣ Γ Γ' s inst s' Hsp. revert s inst s' Hsp.
  induction Γ' as [|d l IH] using PCUICInduction.ctx_length_rev_ind; intros s inst s' Hsp.
  - have Hsp0 : typing_spineE Σ Γ (tSort s) inst (tSort s') := Hsp.
    clear Hsp.
    remember (tSort s) as S0 eqn:eS. remember (tSort s') as S1 eqn:eS'. revert eS eS'.
    destruct Hsp0 as [ty ty' isty isty' c|ty hd tl na A B B' isty isP c hhd sp]; intros -> ->.
    + split; [reflexivity|exact (ws_cumul_pb_Sort_inv Cumul c)|].
      exists []. split; [exact (isType_wf_local isty)|exact (isType_wf_local isty)|constructor|constructor].
    + exfalso. exact (ws_cumul_pb_Sort_Prod_inv Cumul c).
  - pose proof (isType_it_mkProd_or_LetIn_wf_local_proved (wfΣ := wfΣ) (typing_spine_isType_dom Hsp)) as wfΓ'.
    have wfd : wf_localE Σ (Γ ,,, [d] ,,, l) by rewrite -app_context_assoc.
    destruct (All_local_env_tip (wf_localE_app_l _ _ _ wfd)) as [_ hd0].
    rewrite it_mkProd_or_LetIn_app in Hsp.
    destruct d as [na [b|] ty].
    + have hb : Σ ;;; Γ |-E b : ty by destruct hd0 as (hb & _).
      have Hsp1 : typing_spineE Σ Γ (tLetIn na b ty (it_mkProd_or_LetIn l (tSort s))) inst (tSort s') := Hsp.
      pose proof (sbs_typing_spine_letin_inv (wfΣ := wfΣ) Hsp1) as Hsp2.
      rewrite /subst1 subst_it_mkProd_or_LetIn in Hsp2.
      have Hsp3 : typing_spineE Σ Γ (it_mkProd_or_LetIn (subst_context [b] 0 l) (tSort s)) inst (tSort s') := Hsp2.
      destruct (IH (subst_context [b] 0 l) ltac:(rewrite subst_context_length; lia) _ _ _ Hsp3)
        as [instlen leq [instsubst [wfdom _ cs subi]]].
      rewrite context_assumptions_subst in instlen.
      have hl : #|instsubst| = #|l| by rewrite -(context_subst_length cs) subst_context_length.
      split.
      * rewrite context_assumptions_app /=. lia.
      * exact leq.
      * exists (instsubst ++ [b]). split.
        -- exact wfdom.
        -- exact wfΓ'.
        -- apply context_subst_app_inv.
           rewrite -hl skipn_all_app firstn_app_left //.
           split; [exact cs|exact (sbs_context_subst_def_tip na b ty)].
        -- exact (stc_subsletE_app _ _ _ _ _ _ subi (sbs_subslet_def_tip hb)).
    + have Hsp1 : typing_spineE Σ Γ (tProd na ty (it_mkProd_or_LetIn l (tSort s))) inst (tSort s') := Hsp.
      clear Hsp.
      remember (tProd na ty (it_mkProd_or_LetIn l (tSort s))) as P0 eqn:eP.
      remember (tSort s') as S1 eqn:eS'. revert eP eS'.
      destruct Hsp1 as [ty0 ty' isty isty' c|ty0 hd tl na0 A B B' isty isP c hhd sp]; intros -> ->.
      * exfalso. exact (ws_cumul_pb_Prod_Sort_inv Cumul c).
      * destruct (ws_cumul_pb_Prod_Prod_inv c) as [eqna conva cumulB].
        assert (isty0 : isTypeE Σ Γ ty).
        { destruct isty as (_ & u & hu & _).
          destruct (inversion_Prod Σ wfΣ hu) as (s1 & s2 & hA & _ & _).
          destruct hA as (_ & u1 & hu1 & _). exact (has_sort_isTypeE u1 hu1). }
        assert (hdty : Σ ;;; Γ |-E hd : ty).
        { exact (type_ws_cumul_pb (pb := Conv) A hhd isty0 (ws_cumul_pbE_sym_pb conva)). }
        assert (cumulB' : Σ ;;; Γ ⊢E (it_mkProd_or_LetIn l (tSort s)) {0 := hd} ≤ B {0 := hd}).
        { exact (substitution0_ws_cumul_pbE (subject_is_open_termE hdty) cumulB). }
        pose proof (typing_spine_strengthen_proved (wfΣ := wfΣ) sp _
          (isType_apply_proved (wfΣ := wfΣ) isty hdty) cumulB') as sp1.
        rewrite /subst1 subst_it_mkProd_or_LetIn in sp1.
        have sp2 : typing_spineE Σ Γ (it_mkProd_or_LetIn (subst_context [hd] 0 l) (tSort s)) tl (tSort s') := sp1.
        destruct (IH (subst_context [hd] 0 l) ltac:(rewrite subst_context_length; lia) _ _ _ sp2)
          as [instlen leq [instsubst [wfdom _ cs subi]]].
        rewrite context_assumptions_subst in instlen.
        have hl : #|instsubst| = #|l| by rewrite -(context_subst_length cs) subst_context_length.
        split.
        -- rewrite context_assumptions_app /=. lia.
        -- exact leq.
        -- exists (instsubst ++ [hd]). split.
           ++ exact wfdom.
           ++ exact wfΓ'.
           ++ apply context_subst_app_inv.
              rewrite -hl skipn_all_app firstn_app_left //.
              split; [exact cs|exact (sbs_context_subst_ass_tip na ty hd)].
           ++ exact (stc_subsletE_app _ _ _ _ _ _ subi (subslet_ass_tip hdty)).
Qed.
Definition arity_typing_spine_fits {cf : checker_flags} (H : @T0_facts cf) :
  ltac:(let T := type of (@arity_typing_spine cf H) in exact T) := @arity_typing_spine_proved cf.

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

(** ** Print Assumptions of every [<field>_proved] lemma *)

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
Print Assumptions isType_lift_proved.
Print Assumptions weaken_ctx_proved.
Print Assumptions weaken_wf_local_proved.
Print Assumptions weakening_wf_local_proved.
Print Assumptions isType_weaken_proved.
Print Assumptions wf_rel_weak_proved.
Print Assumptions isType_tProd_proved.
Print Assumptions welltyped_prod_codomain_proved.
Print Assumptions isType_it_mkProd_or_LetIn_wf_local_proved.
Print Assumptions spine_subst_ctx_inst_proved.
Print Assumptions spine_subst_inst_subst_proved.
Print Assumptions ctx_inst_open_terms_proved.
Print Assumptions ctx_inst_smash_proved.
Print Assumptions sorts_local_ctx_wf_local_proved.
Print Assumptions type_local_ctx_wf_local_proved.
Print Assumptions spine_subst_app_proved.
Print Assumptions isType_prim_arg_types_proved.
Print Assumptions wf_universes_inst_proved.
Print Assumptions LSet_in_global_bounded_proved.
Print Assumptions type_local_ctx_wf_proved.
Print Assumptions typing_wf_universes_proved.
Print Assumptions typing_wf_sort_proved.
Print Assumptions isType_wf_universes_proved.
Print Assumptions ctf_wf_universes_proved.
Print Assumptions isType_it_mkProd_or_LetIn_proved.
Print Assumptions closed_red_confluence_proved.
Print Assumptions closed_red_from_empty_proved.
Print Assumptions red_expand_let_proved.
Print Assumptions red_it_mkProd_or_LetIn_smash_proved.
Print Assumptions red_mkApps_smash_witness_proved.
Print Assumptions red_rec_arg_check_one_fix_proved.
Print Assumptions ind_arity_relevant_proved.
Print Assumptions inversion_it_mkProd_or_LetIn_proved.
Print Assumptions substitution_proved.
Print Assumptions substitution_wf_local_proved.
Print Assumptions isType_apply_proved.
Print Assumptions typing_spine_strengthen_proved.
Print Assumptions spine_subst_cumul_proved.
Print Assumptions ctx_inst_spine_subst_proved.
Print Assumptions arity_typing_spine_proved.

(** Base comparison: the base twins carry the same axioms. ([depelim] here is Equations' [DepElim.depelim]:
    the import block loads [Program.Equality] after Equations, whose [depelim] would add [eq_rect_eq].) *)
Print Assumptions PCUICSpine.spine_subst_ctx_inst.
Print Assumptions PCUICSpine.spine_subst_app.
Print Assumptions PCUICSR.subject_reduction.
