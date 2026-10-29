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
