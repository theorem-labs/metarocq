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
     PCUICWeakeningTypEta PCUICRenameTypEta PCUICInstTypEta PCUICCasesWfTypEta PCUICGuardClosureEta
     PCUICInversionEta.
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution PCUICSR PCUICInduction PCUICPositionEta.
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

(** [PCUICSubstitution.subslet_length] at [typingE]. *)
Lemma stc_subsletE_length {cf : checker_flags} {Σ : global_env_ext} {Γ s Δ} :
  subsletE Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; f_equal; auto.
Qed.

(** [PCUICSpine.subslet_app] at [typingE]. *)
Lemma stc_subsletE_app {cf : checker_flags} (Σ : global_env_ext) Γ s s' Δ Δ' :
  subsletE Σ Γ s (subst_context s' 0 Δ) ->
  subsletE Σ Γ s' Δ' ->
  subsletE Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
  induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
  - DepElim.depelim sub'. auto.
  - rewrite subst_context_snoc in sub' => sub''.
    move:(stc_subsletE_length sub') => /=.
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

(** Base comparison: the base twins carry the same axioms. ([depelim] here is Equations' [DepElim.depelim]:
    the import block loads [Program.Equality] after Equations, whose [depelim] would add [eq_rect_eq].) *)
Print Assumptions PCUICSpine.spine_subst_ctx_inst.
Print Assumptions PCUICSpine.spine_subst_app.
Print Assumptions PCUICSR.subject_reduction.
