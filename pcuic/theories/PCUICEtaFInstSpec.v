(* Distributed under the terms of the MIT license. *)

(** * A4: the F-inst comparison is included in the η specification

    [finst_cumulSpecE] : ClosedBodies Σ -> is_closed_context Γ ->
      is_open_term Γ (mkApps M args) -> is_open_term Γ (mkApps N args') ->
      M ≈F[pb, #|args|] N -> All2 (≤sE[Conv]) args args' ->
      Σ ;;; Γ ⊢ mkApps M args ≤sE[pb] mkApps N args'
    [compare_term_eta_cumulSpecE] : the [args = []] form.

  Base's [eq_term_upto_univ_napp_cumulSpec] ([PCUICConversion]) ported to U1' and
  the η specification. Every congruence is base's. The new case is the head
  ([tInd]/[tConstruct]), split by U1''s mode:
  - **fully applied** ([head_arity <= #|args|]): the glue's full half gives
    [cumul_*_univ Σ pb _ #|args|], and [cumulE_Ind]/[cumulE_Construct] apply;
  - **under-applied**: the glue's under half gives [cumul_*_univ Σ Conv _ n] at
    [n := head_arity], and [cumulSpecE_*_underapplied_gen]
    ([PCUICCumulativitySpecEtaClosure]) applies. The [_gen] form is generic in
    [n], so neither [declared_*] nor [cstr_args_length] is needed.

  **Scoping, threaded on both sides, no premise weakened.** The under-applied
  lemmas need the arguments scoped and [Γ] closed, so the induction carries
  scoping for both terms. Binder cases extend [Γ] with the left side's context;
  the right side's subterms are open there because the two contexts have the same
  length ([All2_length] of [eq_context_upto_names] / [eq_mfixpoint]). Closedness
  of the [tCase]/[tFix] extensions: base's
  [on_free_vars_ctx_inst_case_context_weak] and
  [on_free_vars_ctx_fix_context_weak].

  The constructor rule is read only through the glue.

  **The hypotheses are satisfiable:** [ClosedBodies Σ], which every well-formed environment satisfies
  ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); scoping by any scoped pair,
  for example closed terms in [[]]; the comparison premise by any F-inst-related
  pair, for example a term with itself (reflexivity at [compare_universe Σ]).

  Dependencies: [PCUICEtaFInst], [PCUICEtaFInstGlue],
  [PCUICCumulativitySpecEtaClosure]. No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICCases PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec
     PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure
     PCUICEtaFInst PCUICEtaFInstGlue PCUICEtaJoinSpec PCUICClosedBodies.

Section FInstSpec.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ.1).

  Local Notation RF pb n :=
    (eq_term_upto_univ_eta_napp Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).

  Lemma cumul_mkAppsE Γ pb M N args args' :
    Σ ;;; Γ ⊢ M ≤sE[pb] N ->
    All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
    Σ ;;; Γ ⊢ mkApps M args ≤sE[pb] mkApps N args'.
  Proof.
    intros HMN Hargs. revert M N HMN; induction Hargs; intros; cbn; [assumption|].
    apply IHHargs. apply cumulE_App; assumption.
  Qed.

  Lemma open_app_ctx' (Γ Δ : context) n t :
    #|Δ| = n -> on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)) t -> is_open_term (Γ ,,, Δ) t.
  Proof. intros <- h. rewrite /app_context length_app -shiftnP_add. exact h. Qed.

  Definition finst_spec_P (M : term) : Type :=
    forall Γ pb N args args',
      is_closed_context Γ ->
      is_open_term Γ (mkApps M args) -> is_open_term Γ (mkApps N args') ->
      RF pb #|args| M N ->
      All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
      Σ ;;; Γ ⊢ mkApps M args ≤sE[pb] mkApps N args'.

  Lemma finst_nil (M : term) Γ pb N :
    finst_spec_P M -> is_closed_context Γ -> is_open_term Γ M -> is_open_term Γ N ->
    RF pb 0 M N -> Σ ;;; Γ ⊢ M ≤sE[pb] N.
  Proof. intros IH hΓ hM hN h. exact (IH Γ pb N [] [] hΓ hM hN h All2_nil). Qed.

  Lemma finst_spec_list Γ (l l' : list term) :
    All finst_spec_P l -> is_closed_context Γ ->
    forallb (is_open_term Γ) l -> forallb (is_open_term Γ) l' ->
    All2 (RF Conv 0) l l' ->
    All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') l l'.
  Proof.
    intros X hΓ hl hl' h. induction h in X, hl, hl' |- *; constructor; depelim X;
      cbn in hl, hl'; move/andP: hl => [h1 hl]; move/andP: hl' => [h1' hl'].
    - exact (finst_nil _ Γ Conv _ f hΓ h1 h1' r).
    - exact (IHh X hl hl').
  Qed.

  Lemma finst_spec_brs Γ (p p' : predicate term) (brs brs' : list (branch term)) :
    All (fun br => onctx finst_spec_P (bcontext br) × finst_spec_P (bbody br)) brs ->
    is_closed_context Γ ->
    forallb (on_free_vars (shiftnP #|Γ| xpred0)) (pparams p) ->
    forallb (fun br =>
      test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| (bcontext br) &&
      on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br)) brs ->
    forallb (fun br =>
      test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p'| (bcontext br) &&
      on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br)) brs' ->
    eq_branches (RF Conv 0) brs brs' ->
    cumul_branches (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) Γ p brs brs'.
  Proof.
    intros X hΓ hp hl hl' h. unfold eq_branches in h.
    induction h in X, hl, hl' |- *; constructor; depelim X;
      cbn in hl, hl'; move/andP: hl => [/andP [hc hb] hl]; move/andP: hl' => [/andP [_ hb'] hl'].
    - destruct p0 as [_ IH]. destruct r as [hctx hbody]. split; [exact hctx|].
      apply (finst_nil _ _ Conv _ IH).
      + exact (on_free_vars_ctx_inst_case_context_weak xpred0 Γ (pparams p) (puinst p)
                 (bcontext x) hp hc hΓ).
      + eapply open_app_ctx'; [apply inst_case_branch_context_length|exact hb].
      + eapply open_app_ctx'; [apply inst_case_branch_context_length|].
        rewrite (All2_length hctx). exact hb'.
      + exact hbody.
    - exact (IHh X hl hl').
  Qed.

  Lemma finst_spec_mfix Γ (Ξ : context) n (mfix mfix' : mfixpoint term) :
    All (fun d => finst_spec_P (dtype d) × finst_spec_P (dbody d)) mfix ->
    is_closed_context Γ -> is_closed_context (Γ ,,, Ξ) -> #|Ξ| = n ->
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0))
                      (on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)))) mfix ->
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0))
                      (on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)))) mfix' ->
    eq_mfixpoint (RF Conv 0) mfix mfix' ->
    All2 (fun d d' =>
      Σ ;;; Γ ⊢ d.(dtype) ≤sE[Conv] d'.(dtype) ×
      Σ ;;; Γ ,,, Ξ ⊢ d.(dbody) ≤sE[Conv] d'.(dbody) ×
      d.(rarg) = d'.(rarg) × eq_binder_annot d.(dname) d'.(dname)) mfix mfix'.
  Proof.
    intros X hΓ hΞ hn hl hl' h. unfold eq_mfixpoint in h.
    induction h in X, hl, hl' |- *; constructor; depelim X;
      cbn in hl, hl'; move/andP: hl => [/andP [hty hbo] hl]; move/andP: hl' => [/andP [hty' hbo'] hl'].
    - destruct p as [IHty IHbo]. destruct r as (ety & ebo & er & en).
      refine (_, (_, (er, en))).
      + exact (finst_nil _ Γ Conv _ IHty hΓ hty hty' ety).
      + apply (finst_nil _ _ Conv _ IHbo hΞ).
        * eapply open_app_ctx'; [exact hn|exact hbo].
        * eapply open_app_ctx'; [exact hn|exact hbo'].
        * exact ebo.
    - exact (IHh X hl hl').
  Qed.

  (** The comparison hypothesis whose LEFT term is [t]. Picked by type, because
      [depelim] gives premises names that are not stable. *)
  Ltac rfh t :=
    match goal with h : eq_term_upto_univ_eta_napp _ _ _ _ _ t _ |- _ => exact h end.

  Theorem finst_cumulSpecE M : finst_spec_P M.
  Proof.
    (* [revert hN] first: [depelim] substitutes [N], and would otherwise revert
       [hN], which depends on it. *)
    induction M using term_forall_list_ind;
      intros Γ pb N args args' hΓ hM hN H Hargs;
      move: hM; rewrite on_free_vars_mkApps => /andP [hM hargs];
      move: hN; rewrite on_free_vars_mkApps => /andP [hN hargs'];
      revert hN; depelim H; intros hN.
    - (* tRel *) apply cumul_mkAppsE; [reflexivity|exact Hargs].
    - (* tVar *) apply cumul_mkAppsE; [reflexivity|exact Hargs].
    - (* tEvar *)
      apply cumul_mkAppsE; [|exact Hargs]. apply cumulE_Evar.
      exact (finst_spec_list Γ _ _ X hΓ hM hN ltac:(match goal with h : All2 _ l _ |- _ => exact h end)).
    - (* tSort *) apply cumul_mkAppsE; [now apply cumulE_Sort|exact Hargs].
    - (* tProd *)
      apply cumul_mkAppsE; [|exact Hargs].
      cbn in hM, hN. move/andP: hM => [hA hB]. move/andP: hN => [hA' hB'].
      have hΓA : is_closed_context (Γ ,, vass n M1) by (rewrite on_free_vars_ctx_snoc hΓ /=; exact hA).
      apply cumulE_Prod; [assumption|exact (finst_nil _ Γ Conv _ IHM1 hΓ hA hA' ltac:(rfh M1))|].
      apply (finst_nil _ _ pb _ IHM2 hΓA).
      + replace #|Γ ,, vass n M1| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hB.
      + replace #|Γ ,, vass n M1| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hB'.
      + rfh M2.
    - (* tLambda *)
      apply cumul_mkAppsE; [|exact Hargs].
      cbn in hM, hN. move/andP: hM => [hA hb]. move/andP: hN => [hA' hb'].
      have hΓA : is_closed_context (Γ ,, vass n M1) by (rewrite on_free_vars_ctx_snoc hΓ /=; exact hA).
      apply cumulE_Lambda; [assumption|exact (finst_nil _ Γ Conv _ IHM1 hΓ hA hA' ltac:(rfh M1))|].
      apply (finst_nil _ _ Conv _ IHM2 hΓA).
      + replace #|Γ ,, vass n M1| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hb.
      + replace #|Γ ,, vass n M1| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hb'.
      + rfh M2.
    - (* tLetIn *)
      apply cumul_mkAppsE; [|exact Hargs].
      cbn in hM, hN. move/and3P: hM => [hb hty hc]. move/and3P: hN => [hb' hty' hc'].
      have hΓd : is_closed_context (Γ ,, vdef n M1 M2)
        by rewrite on_free_vars_ctx_snoc hΓ /= /on_free_vars_decl /test_decl /= hb hty.
      apply cumulE_LetIn;
        [assumption|exact (finst_nil _ Γ Conv _ IHM1 hΓ hb hb' ltac:(rfh M1))
        |exact (finst_nil _ Γ Conv _ IHM2 hΓ hty hty' ltac:(rfh M2))|].
      apply (finst_nil _ _ Conv _ IHM3 hΓd).
      + replace #|Γ ,, vdef n M1 M2| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hc.
      + replace #|Γ ,, vdef n M1 M2| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hc'.
      + rfh M3.
    - (* tApp: push the argument onto the spine, as base does *)
      cbn in hM, hN. move/andP: hM => [hM1 hM2]. move/andP: hN => [hN1 hN2].
      match goal with h2 : eq_term_upto_univ_eta_napp _ _ _ _ _ M2 ?u2 |- _ =>
        apply (IHM1 Γ pb _ (M2 :: args) (u2 :: args')) end.
      + exact hΓ.
      + cbn. rewrite on_free_vars_mkApps /= hM1 hM2 hargs //.
      + cbn. rewrite on_free_vars_mkApps /= hN1 hN2 hargs' //.
      + rfh M1.
      + constructor; [exact (finst_nil _ Γ Conv _ IHM2 hΓ hM2 hN2 ltac:(rfh M2))|exact Hargs].
    - (* tConst *) apply cumul_mkAppsE; [now apply cumulE_Const|exact Hargs].
    - (* tInd: the F-inst head, split by mode *)
      have hlen : #|args| = #|args'| := All2_length Hargs.
      match goal with c : cmp_global_instance_finst _ _ _ _ _ _ _ |- _ => rename c into hc end.
      destruct (le_lt_dec (head_arity Σ.1 (IndRef i)) #|args|) as [hle|hlt].
      + apply cumulE_Ind; [exact (finst_ind_glue_full Σ.1 _ pb i #|args| u u' hle hc)|exact Hargs].
      + apply convSpecE_cumulSpecE.
        apply (cumulSpecE_ind_underapplied_gen Σ i u u' (head_arity Σ.1 (IndRef i)) wfΣ
                 (finst_ind_glue_under Σ.1 _ pb i #|args| u u' hlt hc)
                 (head_arity Σ.1 (IndRef i) - #|args|) Γ args args' hlen);
          [lia|exact hΓ|exact hargs|exact hargs'|exact Hargs].
    - (* tConstruct: the F-inst head, split by mode *)
      have hlen : #|args| = #|args'| := All2_length Hargs.
      match goal with c : cmp_global_instance_finst _ _ _ _ _ _ _ |- _ => rename c into hc end.
      destruct (le_lt_dec (head_arity Σ.1 (ConstructRef i n)) #|args|) as [hle|hlt].
      + apply cumulE_Construct;
          [exact (finst_construct_glue_full Σ.1 _ pb i n #|args| u u' hle hc)|exact Hargs].
      + apply convSpecE_cumulSpecE.
        apply (cumulSpecE_construct_underapplied_gen Σ i n u u' (head_arity Σ.1 (ConstructRef i n)) wfΣ
                 (finst_construct_glue_under Σ.1 _ pb i n #|args| u u' hlt hc)
                 (head_arity Σ.1 (ConstructRef i n) - #|args|) Γ args args' hlen);
          [lia|exact hΓ|exact hargs|exact hargs'|exact Hargs].
    - (* tCase *)
      apply cumul_mkAppsE; [|exact Hargs].
      destruct X as (Hpar & _ & Hret).
      cbn in hM, hN. move/and5P: hM => [hp hr hc hd hbrs]. move/and5P: hN => [hp' hr' hc' hd' hbrs'].
      match goal with e : eq_predicate _ _ p _ |- _ => destruct e as (epar & euinst & ectx & eret) end.
      apply cumulE_Case.
      + unfold cumul_predicate. refine (_, (euinst, (ectx, _))).
        * exact (finst_spec_list Γ _ _ Hpar hΓ hp hp' epar).
        * apply (finst_nil _ _ Conv _ Hret).
          -- exact (on_free_vars_ctx_inst_case_context_weak xpred0 Γ (pparams p) (puinst p)
                      (pcontext p) hp hc hΓ).
          -- eapply open_app_ctx'; [apply inst_case_predicate_context_length|exact hr].
          -- eapply open_app_ctx'; [apply inst_case_predicate_context_length|].
             rewrite (All2_length ectx). exact hr'.
          -- exact eret.
      + exact (finst_nil _ Γ Conv _ IHM hΓ hd hd' ltac:(rfh M)).
      + exact (finst_spec_brs Γ p _ l _ X0 hΓ hp hbrs hbrs'
                 ltac:(match goal with h : eq_branches _ l _ |- _ => exact h end)).
    - (* tProj *)
      apply cumul_mkAppsE; [|exact Hargs]. apply cumulE_Proj.
      cbn in hM, hN. exact (finst_nil _ Γ Conv _ IHM hΓ hM hN ltac:(rfh M)).
    - (* tFix *)
      apply cumul_mkAppsE; [|exact Hargs]. apply cumulE_Fix. unfold cumul_mfixpoint.
      cbn in hM, hN.
      match goal with e : eq_mfixpoint _ m ?m' |- _ => rename e into hm end.
      rewrite -(All2_length hm) in hN.
      have hctx : is_closed_context (Γ ,,, fix_context m)
        := on_free_vars_ctx_fix_context_weak xpred0 Γ m (forallb_All _ _ hM) hΓ.
      exact (finst_spec_mfix Γ (fix_context m) #|m| m _ X hΓ hctx (fix_context_length m) hM hN hm).
    - (* tCoFix *)
      apply cumul_mkAppsE; [|exact Hargs]. apply cumulE_CoFix. unfold cumul_mfixpoint.
      cbn in hM, hN.
      match goal with e : eq_mfixpoint _ m ?m' |- _ => rename e into hm end.
      rewrite -(All2_length hm) in hN.
      have hctx : is_closed_context (Γ ,,, fix_context m)
        := on_free_vars_ctx_fix_context_weak xpred0 Γ m (forallb_All _ _ hM) hΓ.
      exact (finst_spec_mfix Γ (fix_context m) #|m| m _ X hΓ hctx (fix_context_length m) hM hN hm).
    - (* tPrim *)
      apply cumul_mkAppsE; [|exact Hargs]. apply cumulE_Prim.
      match goal with o : onPrims _ _ _ _ |- _ => depelim o end; try solve [constructor].
      destruct X as (Hty & Hdef & Hval).
      cbn in hM, hN. simp test_prim in hM, hN. cbn in hM, hN.
      move/andP: hM => [/andP [hv hd] hty]. move/andP: hN => [/andP [hv' hd'] hty'].
      constructor.
      + assumption.
      + exact (finst_nil _ Γ Conv _ Hdef hΓ hd hd' ltac:(rfh (array_default a))).
      + exact (finst_nil _ Γ Conv _ Hty hΓ hty hty' ltac:(rfh (array_type a))).
      + exact (finst_spec_list Γ _ _ Hval hΓ hv hv'
                 ltac:(match goal with h : All2 _ (array_value a) _ |- _ => exact h end)).
  Qed.

  Corollary compare_term_eta_cumulSpecE Γ pb M N :
    is_closed_context Γ -> is_open_term Γ M -> is_open_term Γ N ->
    RF pb 0 M N -> Σ ;;; Γ ⊢ M ≤sE[pb] N.
  Proof. intros hΓ hM hN h. exact (finst_nil M Γ pb N (finst_cumulSpecE M) hΓ hM hN h). Qed.

End FInstSpec.
