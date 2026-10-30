(* Distributed under the terms of the MIT license. *)

(** * Progress over [typingE] (row T6): the E copy of [PCUICProgress]

  The E twin of every declaration of base [PCUICProgress] whose statement mentions typing,
  conversion, [wf] or [isType]: [typing] → [typingE], [wf] → [wfE], [wf_local] → [wf_localE],
  [isType] → [isTypeE], [typing_size] → [typingE_size] ([PCUICTypingEtaInd]), [env_prop] →
  [env_propE], [on_global_env cumulSpec0] → [on_global_env cumulSpecE0], [cumulSpec]
  ([Σ ;;; Γ |- A <=s B]) → [cumulSpecE], [PCUICArities.typing_spine] →
  [PCUICAritiesEta.typing_spineE] (written qualified), [Σ ;;; Γ ⊢ A ≤ B] → [Σ ;;; Γ ⊢E A ≤ B],
  [wf_fixpoint]/[wf_cofixpoint] → [wf_fixpointE]/[wf_cofixpointE]. [eval], [value],
  [wcbv_red1] ([Σ ⊢ t ⇝ᵥ t']), [red] and [whnf] are unchanged. Each name takes the suffix [E]
  (plan [t0-plan.md] §2, D1); the inductive [typing_spine_pred] becomes [typing_spine_predE]
  with constructors [type_spine_pred_nilE], [type_spine_pred_consE].

  Imported from base, not copied (no relation in the statement, no environment premise):
  [value_stuck_fix], [value_mkApps_inv'], [wcbv_red1_mkApps_left],
  [cstr_branch_context_assumptions], [All_or_disj], the notation [¬ A], and base's global
  hints ([All_app_inv : pcuic], [atomic_value : wcbv]); base's local hint
  [value wcbv_red1 : wcbv] is restated locally.

  Names shared by two declarations, as in base: [inversion_mkAppsE] (here the twin of
  [PCUICProgress.inversion_mkApps], with sizes; [PCUICValidityEta]'s is the twin of
  [PCUICValidity.inversion_mkApps]); both are written qualified outside their sections.
  [typing_ind_envE] and [typing_ind_env_app_sizeE] are the twins of base [PCUICProgress]'s
  ([PCUICTypingEtaInd]'s [typingE_ind_env], [typingE_ind_env_app_size] are the twins of
  [PCUICTyping]'s).

  ** Proof routes that differ from base (statements do not)

  - [typing_ind_env_app_sizeE], the application spine: base turns the spine's [ws_cumul_pb]
    into the spec relation by [cumulAlgo_cumulSpec]; here [ws_cumul_pbE_forget_spec] (through
    [wfE_ClosedBodies]).
  - [progress_env_propE], the [Case] of a constructor: base takes the constructor's
    declaration from [Construct_Ind_ind_eq'] (copy 18); here from [inversion_mkAppsE] and
    [inversion_ConstructE], which give the same [declared_constructor] (the only part base
    reads), so no copy-18 forecast is needed for it.
  - [eval_tCaseE]: base [eval_closed] (premise [wf]) → [PCUICClassificationEta.eval_closed_cb]
    (premise [ClosedBodies]).

  ** No forecast class

  The class of [PCUICClassificationEta] (T1's [SRForecastCopy18]) and this file's
  [ProgForecastCopy18] (two copy-18b lemmas no other class had) were section premises until copy
  18b landed (frac/eta 3e6b422d). Both were deleted after a compiled-form identity check of each
  field against [PCUICInductiveInversionEtaB] (both-way ascription; [About] under
  [Set Printing All]: binder names and implicit status); the lemmas are written qualified. *)

From Stdlib Require Import ssreflect.
From Stdlib Require ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICViews
  PCUICWellScopedCumulativity PCUICClassification PCUICWcbvEval PCUICProgress.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningEnvTypEta
  PCUICWeakeningTypEta PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
  PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICContextConversionEta
  PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICInversionEta PCUICSREtaConv
  PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta
  PCUICWsCumulEtaInstancesGlobal PCUICValidityEta PCUICSREta PCUICClassificationEta.
From MetaRocq.PCUIC Require PCUICGenerationEta PCUICInductiveInversionEtaB.

From Equations Require Import Equations.

Section EvalCaseE.

(** Base [eval_tCase] ([PCUICProgress.v:23]). *)
Lemma eval_tCaseE {cf : checker_flags} {Σ : global_env_ext}  ci p discr brs res T :
  wfE Σ ->
  Σ ;;; [] |-E tCase ci p discr brs : T ->
  eval Σ (tCase ci p discr brs) res ->
  ∑ c u args, red Σ [] (tCase ci p discr brs) (tCase ci p ((mkApps (tConstruct ci.(ci_ind) c u) args)) brs).
Proof.
  intros wf wt H. depind H; try now (cbn in *; congruence).
  - eapply inversion_CaseE in wt as (? & ? & ? & ? & cinv & ?); eauto.
    destruct cinv.
    eexists _, _, _. eapply red_case_c. eapply wcbveval_redE; [exact scrut_ty|eassumption].
  - eapply inversion_CaseE in wt as wt'; eauto. destruct wt' as (? & ? & ? & ? & cinv & ?).
    destruct cinv.
    assert (hcl : closed (mkApps (tCoFix mfix idx) args)).
    { eapply (eval_closed_cb Σ); [|eassumption]. exact (@subject_closedE _ _ _ [] _ _ scrut_ty). }
    rewrite closedn_mkApps in hcl. apply andb_true_iff in hcl as [hclf _].
    assert (Hwcbv_red1 : Σ;;; [] |- tCase ip p discr brs ⇝* tCase ip p (mkApps fn args) brs). {
      etransitivity. { eapply red_case_c. eapply wcbveval_redE; [exact scrut_ty|eassumption]. }
      econstructor. econstructor.
      rewrite closed_unfold_cofix_cunfold_eq; eauto.
    }
    edestruct IHeval2 as (c & u & args0 & IH); eauto using subject_reductionE.
    exists c, u, args0. etransitivity; eauto.
Qed.

End EvalCaseE.

Local Existing Instance config.extraction_checker_flags.

(** Base [typing_spine_pred] ([:47]). *)
Inductive typing_spine_predE {cf : checker_flags} Σ (Γ : context) (P : forall t T (H : Σ ;;; Γ |-E t : T), Type) : term -> list term -> term -> Type :=
| type_spine_pred_nilE ty ty' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ ty' ->
    Σ ;;; Γ ⊢E ty ≤ ty' ->
    typing_spine_predE Σ Γ P ty [] ty'

| type_spine_pred_consE ty hd tl na A B B' s' :
    isTypeE Σ Γ ty ->
    forall H' : Σ ;;; Γ |-E tProd na A B : tSort s',
    P (tProd na A B) (tSort s') H' ->
    Σ ;;; Γ ⊢E ty ≤ tProd na A B ->
    forall H : Σ ;;; Γ |-E hd : A,
    P hd A H ->
    typing_spine_predE Σ Γ P (subst10 hd B) tl B' ->
    typing_spine_predE Σ Γ P ty (hd :: tl) B'.

Section WfEnvE.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** Base [typing_spine_pred_strengthen] ([:71]). *)
  Lemma typing_spine_pred_strengthenE {Γ P T args U} :
    typing_spine_predE Σ Γ P T args U ->
    isTypeE Σ Γ T ->
    forall T',
    isTypeE Σ Γ T' ->
    Σ ;;; Γ ⊢E T' ≤ T ->
    typing_spine_predE Σ Γ P T' args U.
  Proof using wfΣ.
    have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
    induction 1 in |- *; intros T' isTy redT.
    - constructor; eauto. transitivity ty; auto.
    - specialize IHX with (T' := (B {0 := hd})).
      assert (isTypeE Σ Γ (B {0 := hd})) as HH. {
        clear p.
        eapply inversion_ProdE in H' as (? & ? & ? & ? & ?); tea.
        eapply isType_substE. econstructor. econstructor. rewrite subst_empty; eauto.
        econstructor; cbn; eauto.
      }
      forward IHX by exact HH. forward IHX by exact HH.
      forward IHX by now eapply isType_ws_cumul_pbE_refl.
      intros Hsub.
      eapply type_spine_pred_consE; eauto.
      etransitivity; eauto.
  Qed.

End WfEnvE.

(** Base [inversion_mkApps] ([:96]), with sizes; the twin of [PCUICValidity.inversion_mkApps] is
    [PCUICValidityEta.inversion_mkAppsE]. *)
Lemma inversion_mkAppsE {cf : checker_flags} {Σ} {wfΣ :  wfE Σ.1} {Γ f u T} s :
  forall (H : Σ ;;; Γ |-E mkApps f u : T) (HT : Σ ;;; Γ |-E T : tSort s),
  { A : term & { Hf : Σ ;;; Γ |-E f : A & {s' & {HA : Σ ;;; Γ |-E A : tSort s' &
   typingE_size Hf <= typingE_size H ×
   typingE_size HA <= max (typingE_size H) (typingE_size HT) ×
  typing_spine_predE Σ Γ (fun x ty Hx => typingE_size Hx <= typingE_size H) A u T}}}}.
Proof.
  revert f T.
  induction u; intros f T. simpl. intros.
  { exists T, H, s, HT. split; [lia|split; [lia|]].
    econstructor. 3: eapply isType_ws_cumul_pbE_refl. all: now eapply has_sort_isTypeE. }
  intros Hf Ht. simpl in Hf.
  specialize (IHu (tApp f a) T).
  edestruct (IHu Hf) as (T' & H' & s' & H1 & H2 & H3 & H4); tea.
  edestruct @inversion_App_sizeE with (H := H') as (na' & A' & B' & s_ & Hf' & Ha & HA & Hs1 & Hs2 & Hs3 & HA'''); tea.
  exists (tProd na' A' B'). exists Hf'. exists s_. exists HA.
  split. rewrite <- H2. lia.
  split. rewrite <- Nat.le_max_l, <- H2. lia.

  unshelve econstructor.
  5: eauto. 1: eauto.
  3:eapply isType_ws_cumul_pbE_refl; now eapply has_sort_isTypeE.
  1: now eapply has_sort_isTypeE.
  1, 2: rewrite <- H2; lia.
  eapply typing_spine_pred_strengthenE; tea.
  now eapply has_sort_isTypeE. clear Hs3.
  eapply inversion_ProdE in HA as (? & ? & ? & ? & ?); tea.
  eapply isType_substE. econstructor. econstructor. rewrite subst_empty; eauto.
  econstructor;  cbn; eauto.
  Unshelve. eauto.
Qed.

(** Base [typing_ind_env_app_size] ([:128]). *)
Lemma typing_ind_env_app_sizeE `{cf : checker_flags} :
forall (P : global_env_ext -> context -> term -> term -> Type)
       (Pj : global_env_ext -> context -> judgment -> Type)
       (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
       (PΓ : global_env_ext -> context -> Type),

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (* (wfΓ : wf_localE Σ Γ) *) j,
    lift_typing_conj (typingE Σ) (P Σ) Γ j -> Pj Σ Γ j) ->

  (forall Σ (wfΣ : wfE Σ.1)  (Γ : context) (wfΓ : wf_localE Σ Γ),
    All_local_env_over (typingE Σ) (Pdecl Σ) Γ wfΓ -> All_local_env (Pj Σ) Γ -> PΓ Σ Γ) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (n : nat) decl,
      nth_error Γ n = Some decl ->
      PΓ Σ Γ ->
      P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (u : sort),
      PΓ Σ Γ ->
      wf_sort Σ u ->
      P Σ Γ (tSort u) (tSort (Sort.super u))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b : term) (s1 s2 : sort),
      PΓ Σ Γ ->
      lift_typing typingE Σ Γ (j_vass_s na t s1) ->
      Pj Σ Γ (j_vass_s na t s1) ->
      Σ ;;; Γ,, vass na t |-E b : tSort s2 ->
      P Σ (Γ,, vass na t) b (tSort s2) -> P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b bty : term),
      PΓ Σ Γ ->
      lift_typing typingE Σ Γ (j_vass na t) ->
      Pj Σ Γ (j_vass na t) ->
      Σ ;;; Γ,, vass na t |-E b : bty -> P Σ (Γ,, vass na t) b bty -> P Σ Γ (tLambda na t b) (tProd na t bty)) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (b b_ty b' b'_ty : term),
      PΓ Σ Γ ->
      lift_typing typingE Σ Γ (j_vdef na b b_ty) ->
      Pj Σ Γ (j_vdef na b b_ty) ->
      Σ ;;; Γ,, vdef na b b_ty |-E b' : b'_ty ->
      P Σ (Γ,, vdef na b b_ty) b' b'_ty -> P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t : term) T B L s,
      PΓ Σ Γ ->
      Σ ;;; Γ |-E T : tSort s -> P Σ Γ T (tSort s) ->
      forall (Ht : Σ ;;; Γ |-E t : T), P Σ Γ t T ->

      (* Give a stronger induction hypothesis allowing to crawl under applications *)
      (forall t' T' (Ht' : Σ ;;; Γ |-E t' : T'), typingE_size Ht' <= typingE_size Ht -> P Σ Γ t' T') ->
      typing_spine_predE Σ Γ (fun u ty H => Σ ;;; Γ |-E u : ty × P Σ Γ u ty) T L B ->

      P Σ Γ (mkApps t L) B) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) cst u (decl : constant_body),
      on_global_env cumulSpecE0 Pj Σ.1 ->
      PΓ Σ Γ ->
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ decl.(cst_universes) u ->
      P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) u
        mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
      on_global_env cumulSpecE0 Pj Σ.1 ->
      PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) (i : nat) u
          mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
      on_global_env cumulSpecE0 Pj Σ.1 ->
      PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (wfΓ : wf_localE Σ Γ),
     forall (ci : case_info) p c brs indices ps mdecl idecl
       (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
       on_global_env cumulSpecE0 Pj Σ.1 ->
       PΓ Σ Γ ->
       mdecl.(ind_npars) = ci.(ci_npar) ->
       eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
       let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
       wf_predicate mdecl idecl p ->
       consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
       forall pret : Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps,
       P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
       wf_localE Σ (Γ ,,, predctx) ->
       PΓ Σ (Γ ,,, predctx) ->
       is_allowed_elimination Σ idecl.(ind_kelim) ps ->
       PCUICTyping.ctx_inst (Prop_conj typingE P Σ) Γ (p.(pparams) ++ indices)
         (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
       Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
       P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
       implb (isCoFinite mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) p.(preturn)) = true ->
       let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
       wf_branches idecl brs ->
       All2i (fun i cdecl br =>
         (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
         let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
         (PΓ Σ (Γ ,,, brctxty.1) ×
         (Prop_conj typingE P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
         (Prop_conj typingE P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
       P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : projection) (c : term) u
        mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
      on_global_env cumulSpecE0 Pj Σ.1 -> PΓ Σ Γ ->
      Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
      P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
      #|args| = ind_npars mdecl ->
      P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (pdecl.(proj_type)@[u]))) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
      All (on_def_type (Pj Σ) Γ) mfix ->
      All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
      All (on_def_body (Pj Σ) types Γ) mfix ->
      wf_fixpointE Σ Γ mfix ->
      P Σ Γ (tFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
      All (on_def_type (Pj Σ) Γ) mfix ->
      All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
      All (on_def_body (Pj Σ) types Γ) mfix ->
      wf_cofixpointE Σ Γ mfix ->
      P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

  (forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : prim_val) prim_ty cdecl,
      PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps (typingE Σ) Σ Γ p ->
      primitive_typing_hyps (P Σ) Σ Γ p ->
      P Σ Γ (tPrim p) (prim_type p prim_ty)) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t A B : term) s,
      PΓ Σ Γ ->
      Σ ;;; Γ |-E t : A ->
      P Σ Γ t A ->
      Σ ;;; Γ |-E B : tSort s ->
      P Σ Γ B (tSort s) ->
      cumulSpecE Σ Γ A B ->
      P Σ Γ t B) ->

     env_propE P Pj PΓ.
Proof.
 intros P Pj Pdecl PΓ.
 intros Xj XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ t T H.
 eapply typingE_ind_env_app_size; eauto. clear Σ wfΣ Γ t T H.
 intros Σ wfΣ Γ wfΓ t na A B u s HΓ Hprod IHprod Ht IHt IH Hu IHu.
 have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
 pose proof (mkApps_decompose_app t).
 destruct (decompose_app t) as [t1 L].
 subst. rename t1 into t. cbn in *.
 replace (tApp (mkApps t L) u) with (mkApps t (L ++ [u])) by now rewrite mkApps_app.

 pose proof (@PCUICProgressEta.inversion_mkAppsE cf) as Happs. specialize Happs with (H := Ht).
 forward Happs; eauto.
 destruct (Happs _ Hprod) as (A' & Hf & s' & HA & sz_f & sz_A & HL).
 destruct @inversion_Prod_sizeE with (H := Hprod) as (s1 & s2 & H1 & H2 & Hs1 & Hs2 & Hsub); [ eauto | ].
 eapply X4. 6:eauto. 4: exact HA. all: eauto.
 - intros. eapply (IH _ _ Hf). lia.
 - Unshelve. 2:exact Hf. intros. eapply (IH _ _ Ht'). lia.
 - clear sz_A. induction L in A', Hf, (* HA, sz_A, *) Ht, HL, t, Hf, IH (*, s' *) |- *.
   + inversion HL; subst. inversion X13. econstructor. econstructor; eauto. eauto. eauto. eauto. eauto. eauto.
     econstructor. 1,2: eapply isType_applyE; eauto. eapply ws_cumul_pbE_refl.
     eapply typing_closed_contextE; eauto. eapply type_is_open_termE.
     eapply typeE_App; eauto.
   + cbn. inversion HL. subst. clear HL.
     eapply inversion_ProdE in H' as Hx; eauto. destruct Hx as (? & ? & ? & ? & ?).
     econstructor.
     7: unshelve eapply IHL.
     now eauto. now eauto. split. now eauto. unshelve eapply IH. eauto. lia.
     now eauto. now eauto. split. now eauto. unshelve eapply IH. eauto. lia.
     2: now eauto. eauto.
     econstructor; eauto. econstructor; eauto. now eapply ws_cumul_pbE_forget_spec in X14.
     eauto.
Qed.

(** Base [typing_ind_env] ([:316]). *)
Lemma typing_ind_envE `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pj : global_env_ext -> context -> judgment -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : global_env_ext -> context -> Type),

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (* (wfΓ : wf_localE Σ Γ) *) j,
        lift_typing_conj (typingE Σ) (P Σ) Γ j -> Pj Σ Γ j) ->

    (forall Σ (wfΣ : wfE Σ.1)  (Γ : context) (wfΓ : wf_localE Σ Γ),
        All_local_env_over (typingE Σ) (Pdecl Σ) Γ wfΓ -> All_local_env (Pj Σ) Γ -> PΓ Σ Γ) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (u : sort),
        PΓ Σ Γ ->
        wf_sort Σ u ->
        P Σ Γ (tSort u) (tSort (Sort.super u))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b : term) (s1 s2 : sort),
        PΓ Σ Γ ->
        lift_typing typingE Σ Γ (j_vass_s na t s1) ->
        Pj Σ Γ (j_vass_s na t s1) ->
        Σ ;;; Γ,, vass na t |-E b : tSort s2 ->
        P Σ (Γ,, vass na t) b (tSort s2) -> P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b bty : term),
        PΓ Σ Γ ->
        lift_typing typingE Σ Γ (j_vass na t) ->
        Pj Σ Γ (j_vass na t) ->
        Σ ;;; Γ,, vass na t |-E b : bty -> P Σ (Γ,, vass na t) b bty -> P Σ Γ (tLambda na t b) (tProd na t bty)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (b b_ty b' b'_ty : term),
        PΓ Σ Γ ->
        lift_typing typingE Σ Γ (j_vdef na b b_ty) ->
        Pj Σ Γ (j_vdef na b b_ty) ->
        Σ ;;; Γ,, vdef na b b_ty |-E b' : b'_ty ->
        P Σ (Γ,, vdef na b b_ty) b' b'_ty -> P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t : term) T B L s,
        PΓ Σ Γ ->
        Σ ;;; Γ |-E T : tSort s -> P Σ Γ T (tSort s) ->
        forall (Ht : Σ ;;; Γ |-E t : T), P Σ Γ t T ->

        (* Give a stronger induction hypothesis allowing to crawl under applications *)
        typing_spine_predE Σ Γ (fun u ty H => Σ ;;; Γ |-E u : ty × P Σ Γ u ty) T L B ->

        P Σ Γ (mkApps t L) B) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) cst u (decl : constant_body),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (wfΓ : wf_localE Σ Γ),
    forall (ci : case_info) p c brs indices ps mdecl idecl
      (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
      on_global_env cumulSpecE0 Pj Σ.1 ->
      PΓ Σ Γ ->
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
      forall pret : Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps,
      P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      wf_localE Σ (Γ ,,, predctx) ->
      PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ idecl.(ind_kelim) ps ->
      PCUICTyping.ctx_inst (Prop_conj typingE P Σ) Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
      Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
      P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
      implb (isCoFinite mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) p.(preturn)) = true ->
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        (PΓ Σ (Γ ,,, brctxty.1) ×
          (Prop_conj typingE P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Prop_conj typingE P) Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))) 0 idecl.(ind_ctors) brs ->
      P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        on_global_env cumulSpecE0 Pj Σ.1 -> PΓ Σ Γ ->
        Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
        All (on_def_type (Pj Σ) Γ) mfix ->
        All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
        All (on_def_body (Pj Σ) types Γ) mfix ->
        wf_fixpointE Σ Γ mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
        All (on_def_type (Pj Σ) Γ) mfix ->
        All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
        All (on_def_body (Pj Σ) types Γ) mfix ->
        wf_cofixpointE Σ Γ mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->


    (forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : prim_val) prim_ty cdecl,
      PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps (typingE Σ) Σ Γ p ->
      primitive_typing_hyps (P Σ) Σ Γ p ->
      P Σ Γ (tPrim p) (prim_type p prim_ty)) ->


    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t A B : term) s,
        PΓ Σ Γ ->
        Σ ;;; Γ |-E t : A ->
        P Σ Γ t A ->
        Σ ;;; Γ |-E B : tSort s ->
        P Σ Γ B (tSort s) ->
        cumulSpecE Σ Γ A B ->
        P Σ Γ t B) ->

       env_propE P Pj PΓ.
Proof.
  intros P Pdecl PΓ; unfold env_propE.
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  apply typing_ind_env_app_sizeE; eauto.
Qed.

Local Hint Constructors PCUICWcbvEval.value PCUICWcbvEval.wcbv_red1 : wcbv.

Import PCUICGlobalEnv.

Section ProgressE.

(** Base [typing_spine_length] ([:488]). *)
Lemma typing_spine_lengthE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ ind u args args' T' :
  PCUICAritiesEta.typing_spineE Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  #|args'| <= context_assumptions Δ.
Proof.
  intros hsp.
  pose proof (typing_spine_more_invE _ _ _ _ _ _ _ _ hsp).
  destruct (Compare_dec.le_dec #|args'| (context_assumptions Δ)). lia. lia.
Qed.

(** Base [declared_constructor_ind_decl] ([:497]). *)
Lemma declared_constructor_ind_declE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind c} {mdecl idecl cdecl} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  inductive_ind ind < #|ind_bodies mdecl|.
Proof.
  intros [[hm hi] hc]. now eapply nth_error_Some_length in hi.
Qed.

(** Base [typing_constructor_arity_exact] ([:506]). *)
Lemma typing_constructor_arity_exactE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind c u u' args}
  {mdecl idecl cdecl indices} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  Σ ;;; [] |-E mkApps (tConstruct ind c u) args : mkApps (tInd ind u') indices ->
  #|args| = cstr_arity mdecl cdecl.
Proof.
  intros declc hc.
  eapply PCUICInductiveInversionEtaB.Construct_Ind_ind_eqE in hc; tea.
  intuition auto.
Qed.

(** Base [typing_constructor_arity] ([:517]). *)
Lemma typing_constructor_arityE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind c u args T} {mdecl idecl cdecl} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  Σ ;;; [] |-E mkApps (tConstruct ind c u) args : T ->
  #|args| <= cstr_arity mdecl cdecl.
Proof.
  intros declc hc.
  pose proof (validityE hc).
  eapply inversion_mkApps_directE in hc as [A' [u' [s' [hs hsp]]]]; eauto.
  eapply inversion_ConstructE in s' as [mdecl' [idecl' [cdecl' [wf [declc' [cu cum]]]]]]; tea.
  unshelve epose proof (declc_ := declared_constructor_to_gen declc); eauto.
  unshelve epose proof (declc'_ := declared_constructor_to_gen declc'); eauto.
  destruct (PCUICGlobalEnv.declared_constructor_inj declc_ declc'_) as [? []]. subst mdecl' idecl' cdecl'.
  clear declc'.
  eapply typing_spine_strengthenE in hsp. 3:exact cum.
  2:{ eapply validityE. econstructor; tea. }
  unfold type_of_constructor in hsp.
  destruct (on_declared_constructorE declc) as [[] [cunivs [_ onc]]].
  rewrite onc.(cstr_eq) in hsp.
  rewrite <-it_mkProd_or_LetIn_app in hsp.
  rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn in hsp.
  epose proof (subst_cstr_concl_head ind u mdecl (cstr_args cdecl) (cstr_indices cdecl)). cbn in H.
  unfold cstr_concl in hsp. cbn in hsp. len in hsp. rewrite H in hsp. clear H.
  eapply (declared_constructor_ind_declE declc). clear H.
  eapply typing_spine_lengthE in hsp. len in hsp. unfold cstr_arity.
  now rewrite (declared_minductive_ind_nparsE declc).
Qed.

(** Base [typing_spine_sort] ([:564]). *)
Lemma typing_spine_sortE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ s args T :
  PCUICAritiesEta.typing_spineE Σ Γ (tSort s) args T -> args = [].
Proof.
  induction args => //.
  intros sp. depelim sp.
  now eapply ws_cumul_pbE_Sort_Prod_inv in w.
Qed.

(** Base [typing_spine_axiom] ([:572]). *)
Lemma typing_spine_axiomE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ cst u cdecl args args' T :
  declared_constant Σ cst cdecl ->
  cdecl.(cst_body) = None ->
  prim_op_of Σ cst = None ->
  PCUICAritiesEta.typing_spineE Σ Γ (mkApps (tConst cst u) args) args' T -> args' = [].
Proof.
  intros hdecl hb hnop.
  induction args' => //.
  intros sp. depelim sp.
  now eapply invert_cumul_axiom_prodE in w.
Qed.

(** Base [typing_spine_prim_type] ([:587]). *)
Lemma typing_spine_prim_typeE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ prim prim_ty cdecl args T :
  primitive_constant Σ (prim_val_tag prim) = Some prim_ty ->
  declared_constant Σ prim_ty cdecl ->
  primitive_invariants (prim_val_tag prim) cdecl ->
  PCUICAritiesEta.typing_spineE Σ Γ (prim_type prim prim_ty) args T -> args = [].
Proof.
  intros hp hdecl hb.
  assert (hnop : prim_op_of Σ prim_ty = None).
  { pose proof wfΣ as [_ [wfr _]]. eapply prim_op_of_primitive_constant; tea. }
  induction args => //.
  destruct prim as [? []]; cbn in *; intros sp; destruct hb; simp prim_type in *.
  1-3:eapply (typing_spine_axiomE _ _ _ _ []) in sp; tea.
  eapply (typing_spine_axiomE _ _ _ _ [array_type a0]) in sp; tea.
Qed.

(** Base [typing_value_head_napp] ([:602]). *)
Lemma typing_value_head_nappE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} fn args hd T :
  negb (isApp fn) ->
  Σ ;;; [] |-E mkApps fn (args ++ [hd]) : T ->
  PCUICWcbvEval.value Σ hd -> closed hd ->
  PCUICWcbvEval.value Σ (mkApps fn args) ->
  (∑ t' : term, Σ ⊢ mkApps fn (args ++ [hd]) ⇝ᵥ t') +
  PCUICWcbvEval.value Σ (mkApps fn (args ++ [hd])).
Proof.
  intros napp ht vhd clhd vapp.
  pose proof ht as ht'.
  destruct (value_mkApps_inv' _ _ _ napp vapp).
  eapply inversion_mkApps_directE in ht' as [A' [u [hfn [hhd hcum]]]]; tea.
  2:{ now eapply validityE. }
  destruct fn => //; try depelim a; cbn in * => //.
  * eapply inversion_SortE in hfn as [? [? cu]]; tea.
    eapply typing_spine_strengthenE in hcum. 3:tea. 2:{ eapply validityE; econstructor; eauto. }
    now eapply typing_spine_sortE, app_tip_nil in hcum.
  * eapply inversion_ProdE in hfn as [? [? [? [? cu]]]]; tea.
    eapply typing_spine_strengthenE in hcum. 3:tea. 2:{ eapply validityE. econstructor; eauto. }
    now eapply typing_spine_sortE, app_tip_nil in hcum.
  * (* Lambda *) left. destruct args.
    - cbn. eexists. now eapply wcbv_red_beta.
    - eexists. rewrite mkApps_app. rewrite (mkApps_app _ [t] args). do 2 eapply wcbv_red1_mkApps_left.
      cbn. eapply wcbv_red_beta. now depelim a0.
  * (* Inductive *)
    eapply inversion_IndE in hfn as [? [? [? [? [? cu]]]]]; tea.
    eapply typing_spine_strengthenE in hcum. 3:tea. 2:{ eapply validityE. econstructor; eauto. }
    right. eapply value_app. constructor. eauto with pcuic.
  * (* constructor *)
    right. eapply value_app; auto. 2:{ eapply All_app_inv; eauto. }
    pose proof hfn as hfn'.
    eapply inversion_ConstructE in hfn' as [mdecl [idecl [cdecl [wf [declc _]]]]]; tea.
    eapply (typing_constructor_arityE declc) in ht.
    econstructor; tea. unshelve eapply declared_constructor_to_gen; eauto.
  * (* fix *)
    destruct (isStuckFix (tFix mfix idx) (args ++ [hd])) eqn:E.
    + right. eapply value_stuck_fix; eauto with pcuic.
    + cbn in E.
      eapply inversion_FixE in hfn as ([] & ? & Efix & ? & ? & ?); eauto.
      unfold cunfold_fix in E. rewrite Efix in E. cbn in E.
      len in E. cbn in E. assert (rarg = #|args|).
      eapply stuck_fix_value_args in vapp; tea. 2:{ unfold cunfold_fix. now rewrite Efix. }
      cbn in vapp. apply Nat.leb_gt in E. lia. subst rarg.
      left. eexists. rewrite mkApps_app /=. eapply wcbv_red_fix. eauto. eauto.
      unfold unfold_fix. now rewrite Efix.
      eapply fix_app_is_constructorE in ht.
      2:{ unfold unfold_fix. now rewrite Efix. }
      cbn in ht. rewrite nth_error_app_ge // /= in ht.
      replace (#|args| - #|args|) with 0 in ht by lia. cbn in ht. apply ht.
      eapply value_axiom_free; eauto.
      eapply value_whnfE; eauto.
  * (* cofix *)
    right. eapply value_app; eauto with pcuic.
    now constructor.
  * (* primitive *)
    cbn.
    eapply inversion_PrimE in hfn as [prim_ty [cdecl [hwf hp hdecl hinv hty hcum']]]; tea.
    eapply typing_spine_strengthenE in hcum. 3:tea. 2:{ eapply validityE; econstructor; eauto. }
    now eapply typing_spine_prim_typeE, app_tip_nil in hcum.
Qed.

(** Base [typing_value_head] ([:663]). *)
Lemma typing_value_headE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} fn args hd T :
  Σ ;;; [] |-E mkApps fn (args ++ [hd]) : T ->
  PCUICWcbvEval.value Σ hd -> closed hd ->
  PCUICWcbvEval.value Σ (mkApps fn args) ->
  (∑ t' : term, Σ ⊢ mkApps fn (args ++ [hd]) ⇝ᵥ t') +
  PCUICWcbvEval.value Σ (mkApps fn (args ++ [hd])).
Proof.
  destruct (decompose_app fn) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  rewrite (decompose_app_inv da).
  rewrite -mkApps_app app_assoc.
  intros; eapply typing_value_head_nappE; tea. now rewrite H.
  rewrite mkApps_app //.
Qed.

(** Base [progress_env_prop] ([:704]). *)
Lemma progress_env_propE `{cf : checker_flags}:
  env_propE (fun Σ Γ t T => axiom_free Σ -> Γ = [] -> Σ ;;; Γ |-E t : T -> {t' & Σ ⊢ t ⇝ᵥ t'} + (PCUICWcbvEval.value Σ t))
           (fun Σ Γ j => axiom_free Σ -> Γ = [] -> lift_typing0 (fun t T => Σ ;;; Γ |-E t : T -> {t' & Σ ⊢ t ⇝ᵥ t'} + (PCUICWcbvEval.value Σ t)) j)
           (fun _ _ => True).
Proof with eauto with wcbv; try congruence.
  eapply typing_ind_envE...
  - intros Σ wfΣ Γ j Hj Hax eq.
    apply lift_typing_impl with (1 := Hj) => ?? [] // H IH //. now apply IH.
  - intros Σ wfΣ Γ wfΓ n decl Hdecl _ Hax -> Hty.
    destruct n; inv Hdecl.
  - intros Σ wfΣ Γ _ n b b_ty b' b'_ty _ Hb IHb Hb' IHb' Hax -> H.
    specialize (IHb Hax eq_refl).
    apply unlift_TermTyp in Hb, IHb as [ [t' IH] | IH]; eauto with wcbv.
  - intros Σ wfΣ Γ _ t T B L s _ HT IHT Ht IHt HL Hax -> H.
    have cbΣ : ClosedBodies Σ.1 := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ).
    clear HT IHT.
    induction HL in H, t, Ht, IHt |- *.
    + cbn. eauto.
    + cbn. eapply IHHL.
      2:{ do 2 (econstructor; eauto). now eapply ws_cumul_pbE_forget_spec in w. }
      intros _ Happ.
      destruct (IHt Hax eq_refl Ht) as [[t' IH] | IH]; eauto with wcbv.
      assert (Ht' : Σ ;;; [] |-E t : tProd na A B) by (econstructor; eauto; now eapply ws_cumul_pbE_forget_spec in w).
      destruct p0 as [_ [[t' Hstep] | Hval]]; eauto using PCUICWcbvEval.wcbv_red1.
      intros htapp.
      pose proof (typing_value_headE t [] hd _ htapp Hval).
      forward X. now eapply subject_closedE in H0. cbn in X.
      specialize (X IH). exact X.
      now cbn in H.
  - intros Σ wf Γ _ cst u decl Hdecls _ Hdecl Hcons Hax -> H.
    destruct (decl.(cst_body)) as [body | ] eqn:E.
    + eauto with wcbv.
    + red in Hax. eapply Hax in E; eauto.
  - intros Σ wfΣ Γ _ ci p c brs indices ps mdecl idecl Hidecl Hforall _ Heq Heq_context predctx Hwfpred Hcon Hreturn IHreturn Hwfl _.
    intros Helim Hctxinst Hc IHc Hcof ptm Hwfbranches Hall Hax -> H.
    specialize (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv.
    pose proof IH as IHv.
    eapply value_classificationE in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc, IHv |- *.
    destruct (decompose_app c) as [h l].
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply PCUICInductiveInversionEtaB.invert_Case_ConstructE in H as H_; sq; eauto. destruct H_ as (Eq & H_); subst.
      left.
      destruct (nth_error brs n) as [br | ] eqn:E.
      2:{ exfalso. destruct H_ as [? []]; congruence. }
      assert (#|l| = ci_npar ci + context_assumptions (bcontext br)) as Hl.
      { destruct H_ as [? []]; auto. now noconf H0. }
      clear H_.
      (* Base takes the constructor's declaration from [Construct_Ind_ind_eq']; the
         inversions give the same [declared_constructor]. *)
      eapply PCUICValidityEta.inversion_mkAppsE in Hc as (Ahd & Hc' & _); eauto.
      eapply inversion_ConstructE in Hc' as (mdecl' & idecl' & cdecl' & ? & d & ? & ?); eauto.
      eexists.
      unshelve epose proof (d_ := declared_constructor_to_gen d); eauto.
      unshelve epose proof (Hidecl_ := declared_inductive_to_gen Hidecl); eauto.
      destruct (declared_inductive_inj d_ Hidecl_); subst mdecl' idecl'.
      eapply All2i_nth_error in Hall as [eqctx _]; tea; [|eapply d].
      eapply PCUICCasesContexts.alpha_eq_context_assumptions in eqctx.
      rewrite cstr_branch_context_assumptions in eqctx.
      eapply wcbv_red_iota; eauto.
      { rewrite /cstr_arity Hl. rewrite -Heq. lia. }
      eapply value_mkApps_inv in IHv as [[-> ]|[]]; eauto.

    + eapply inversion_CaseE in H as (? & ? & ? & ? & [] & ?); eauto.
      eapply PCUICValidityEta.inversion_mkAppsE in scrut_ty as (? & ? & ?); eauto.
      eapply inversion_CoFixE in t as (? & ? & ? & ? & ? & ? & ?); eauto.
      left. eexists. eapply wcbv_red_cofix_case. unfold cunfold_cofix. rewrite e. reflexivity.
      eapply value_mkApps_inv in IHv as [[-> ]|[]]; eauto.
  - intros Σ wfΣ Γ _ p c u mdecl idecl cdecl pdecl Hcon args Hargs _ Hc IHc
           Hlen Hax -> H.
    destruct (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv; clear IHc.
    pose proof IH as Hval.
    eapply value_classificationE in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc, Hval |- *.
    destruct (decompose_app c) as [h l].
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply PCUICInductiveInversionEtaB.invert_Proj_ConstructE in H as H_; sq; eauto. destruct H_ as (<- & -> & Hl).
      left. eapply nth_error_Some' in Hl as [x Hx].
      eexists.
      eapply wcbv_red_proj; eauto.
      unshelve eapply declared_projection_to_gen; eauto.
      now eapply (typing_constructor_arity_exactE Hcon) in Hc.
      eapply value_mkApps_inv in Hval as [[-> Hval] | [? ? Hval]]; eauto.
    + left. eapply inversion_ProjE in H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      eapply PCUICValidityEta.inversion_mkAppsE in t as (? & ? & ?); eauto.
      eapply inversion_CoFixE in t as (? & ? & ? & ? & ? & ? & ?); eauto.
      eexists. eapply wcbv_red_cofix_proj. unfold cunfold_cofix. rewrite e0. reflexivity.
      eapply value_mkApps_inv in Hval as [[-> ]|[]]; eauto.
  - intros Σ wfΣ Γ _ p c u mdecl idecl cdecl pdecl Hcon args Hargs -> hp.
    depelim args... 1-2:right; constructor; constructor 2; constructor.
    right. constructor. constructor 2. constructor.
    depelim Hcon.
    destruct hdef; eauto.
    + left. destruct s as [t' hred]. exists (tPrim (prim_array (set_array_default a t'))). now constructor.
    + destruct a as []; cbn in *.
      clear hty.
      solve_all. clear -hvalue0 Hargs v.
      set (a := {| array_level := _ |}).
      assert (All (fun x : term => ((∑ t' : term, Σ ⊢ x ⇝ᵥ t') + PCUICWcbvEval.value Σ x))%type array_value).
      { solve_all. } clear hvalue0 Hargs.
      eapply All_or_disj in X as [].
      * destruct s as [n [v' [? []]]]. destruct s as [t' ht'].
        left. exists (tPrim (prim_array (set_array_value a (firstn n array_value ++ t' :: skipn (S n) array_value)))).
        econstructor; eauto.
      * right. constructor. constructor 2. constructor; eauto.
Qed.

(** Base [progress] ([:810]). *)
Lemma progressE `{cf : checker_flags}:
  forall (Σ:global_env_ext) t T,
    axiom_free Σ -> wfE Σ ->
    Σ ;;; [] |-E t : T ->
    {t' & Σ ⊢ t ⇝ᵥ t'} + (PCUICWcbvEval.value Σ t).
Proof.
  intros.
  edestruct progress_env_propE as [_ [_ [[t' Ht'] | Hval]]]; eauto.
Defined.

(** Base [whnf_progress] ([:822]). *)
Lemma whnf_progressE `{cf : checker_flags}:
  forall (Σ:global_env_ext) t T,
    axiom_free Σ -> wfE Σ ->
    Σ ;;; [] |-E t : T ->
    ¬ { t' & Σ ;;; [] |- t ⇝ t' } ->
    whnf RedFlags.default Σ [] t.
Proof.
  intros.
  edestruct progress_env_propE as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  eapply wcbv_red1_red1 in Ht'.
  exfalso; apply H0. eexists; eauto.
  eapply subject_closedE in X0; eauto.
  eapply value_whnfE in Hval. eauto.
  eapply subject_closedE in X0; eauto.
Qed.

(** Base [classification] ([:838]). *)
Lemma classificationE : forall (Σ:global_env_ext) t i u args,
  axiom_free Σ -> wfE Σ ->
  ¬ { t' & Σ ;;; [] |- t ⇝ t'} ->
  Σ ;;; [] |-E t : mkApps (tInd i u) args ->
  construct_cofix_discr (head t).
Proof.
  intros; eapply whnf_classificationE; eauto.
  eapply whnf_progressE; eauto.
Qed.

End ProgressE.
