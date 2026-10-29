(* Distributed under the terms of the MIT license. *)

(** * A4: [canon] is invisible to the specification

    [canon_cumulSpecE] : is_closed_context Γ -> is_open_term Γ t ->
                         Σ ;;; Γ ⊢ t ≤sE[Conv] canon t

  With [cumulE_Sym], also [canon t ≤sE t]. A4 (join ⇒ spec, [I5_join_to_spec])
  uses this to step from [t] to the join's starting point [canon t], and back from
  [canon u] to [u].

  **Why it holds.** [canon] changes only what the specification does not compare:
  - a λ-domain and annotation: [cumulSpecE_lambda_domain]
    ([PCUICCumulativitySpecEta]), the one non-congruence case;
  - a [tProd]/[tLetIn]/fix binder name, keeping its relevance: the congruence
    rules need only [eq_binder_annot], i.e. relevance;
  - case-context names: [cumul_predicate]/[cumul_branch] compare contexts with
    [eq_context_upto_names] ([PCUICCumulativitySpec]).

  **Scoping, threaded, no premise weakened.** [cumulSpecE_lambda_domain] needs
  both λs scoped, so the induction carries [is_closed_context Γ] and
  [is_open_term Γ t]. The binder cases extend [Γ] with the left side's context
  (all three specification comparisons use it). Closedness of the [tCase] and
  [tFix] extensions comes from base's confluence-free
  [on_free_vars_ctx_inst_case_context_weak] and
  [on_free_vars_ctx_fix_context_weak] ([PCUICOnFreeVars]), whose hypotheses are
  exactly the conjuncts [on_free_vars] gives.

  **The hypotheses are satisfiable** by any scoped term in a closed context, for
  example every closed term in [[]].

  Dependencies: [PCUICCumulativitySpecEta], [PCUICEtaCanon]. No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From Equations Require Import Equations.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICCases PCUICOnFreeVars PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICEtaCanon.

Section CanonSpec.

  Context {cf : checker_flags} (Σ : global_env_ext).

  (** The motive. *)
  Definition canon_spec_P (t : term) : Type :=
    forall Γ, is_closed_context Γ -> is_open_term Γ t -> Σ ;;; Γ ⊢ t ≤sE[Conv] canon t.

  Lemma open_app_ctx (Γ Δ : context) n t :
    #|Δ| = n -> on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)) t -> is_open_term (Γ ,,, Δ) t.
  Proof. intros <- h. rewrite /app_context length_app -shiftnP_add. exact h. Qed.

  Lemma canon_spec_list Γ l :
    All canon_spec_P l -> is_closed_context Γ -> forallb (is_open_term Γ) l ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) l (map canon l).
  Proof.
    induction 1 as [|t l IH _ IHl]; cbn; intros hΓ h; constructor.
    - move/andP: h => [h _]. exact (IH Γ hΓ h).
    - move/andP: h => [_ h]. exact (IHl hΓ h).
  Qed.

  Lemma canon_spec_brs Γ p brs :
    All (fun br => onctx canon_spec_P (bcontext br) × canon_spec_P (bbody br)) brs ->
    is_closed_context Γ ->
    forallb (on_free_vars (shiftnP #|Γ| xpred0)) (pparams p) ->
    forallb (fun br =>
      test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| (bcontext br) &&
      on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br)) brs ->
    cumul_branches (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) Γ p brs (map (canon_branch canon) brs).
  Proof.
    intros X hΓ hp. induction X as [|br brs [_ IH] _ IHX]; cbn; intros h; constructor.
    - move/andP: h => [/andP [hc hb] _]. unfold cumul_branch, canon_branch; cbn. split.
      + apply eq_context_upto_names_canon_decl.
      + apply IH.
        * exact (on_free_vars_ctx_inst_case_context_weak xpred0 Γ (pparams p) (puinst p)
                   (bcontext br) hp hc hΓ).
        * eapply open_app_ctx; [apply inst_case_branch_context_length|exact hb].
    - move/andP: h => [_ h]. exact (IHX h).
  Qed.

  Lemma canon_spec_mfix Γ (Ξ : context) n mfix0 :
    All (fun d => canon_spec_P (dtype d) × canon_spec_P (dbody d)) mfix0 ->
    is_closed_context Γ -> is_closed_context (Γ ,,, Ξ) -> #|Ξ| = n ->
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0))
                      (on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)))) mfix0 ->
    All2 (fun d d' =>
      Σ ;;; Γ ⊢ d.(dtype) ≤sE[Conv] d'.(dtype) ×
      Σ ;;; Γ ,,, Ξ ⊢ d.(dbody) ≤sE[Conv] d'.(dbody) ×
      d.(rarg) = d'.(rarg) × eq_binder_annot d.(dname) d'.(dname))
      mfix0 (map (canon_def canon) mfix0).
  Proof.
    intros X hΓ hΞ hn. induction X as [|d mfix0 [Hty Hbo] _ IHX]; cbn; intros h; constructor.
    - move/andP: h => [/andP [hty hbo] _]. unfold canon_def; cbn.
      (* [split] also closes the two [=]-goals ([eq] has one constructor), so the
         number of remaining goals is not fixed: build the tuple explicitly. *)
      refine (_, (_, (eq_refl, eq_binder_annot_canon_na _))).
      + exact (Hty Γ hΓ hty).
      + apply Hbo; [exact hΞ|]. eapply open_app_ctx; [exact hn|exact hbo].
    - move/andP: h => [_ h]. exact (IHX h).
  Qed.

  Theorem canon_cumulSpecE t : canon_spec_P t.
  Proof.
    induction t using term_forall_list_ind; intros Γ hΓ ht; cbn [canon].
    - (* tRel *) reflexivity.
    - (* tVar *) reflexivity.
    - (* tEvar *) apply cumulE_Evar. exact (canon_spec_list Γ _ X hΓ ht).
    - (* tSort *) reflexivity.
    - (* tProd *)
      cbn in ht. move/andP: ht => [hA hB].
      apply cumulE_Prod; [apply eq_binder_annot_canon_na|exact (IHt1 Γ hΓ hA)|].
      apply IHt2.
      + rewrite on_free_vars_ctx_snoc hΓ /=. exact hA.
      + replace #|Γ ,, vass n t1| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hB.
    - (* tLambda *)
      have hc : is_open_term Γ (canon (tLambda n t1 t2)) := canon_is_open_term Γ _ ht.
      cbn [canon] in hc.
      apply cumulSpecE_lambda_domain; [exact hΓ|exact ht|exact hc|].
      cbn in ht. move/andP: ht => [hA hb]. apply IHt2.
      + rewrite on_free_vars_ctx_snoc hΓ /=. exact hA.
      + replace #|Γ ,, vass n t1| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hb.
    - (* tLetIn *)
      cbn in ht. move/and3P: ht => [hb hty hc].
      apply cumulE_LetIn;
        [apply eq_binder_annot_canon_na|exact (IHt1 Γ hΓ hb)|exact (IHt2 Γ hΓ hty)|].
      apply IHt3.
      + rewrite on_free_vars_ctx_snoc hΓ /= /on_free_vars_decl /test_decl /= hb hty //.
      + replace #|Γ ,, vdef n t1 t2| with (S #|Γ|) by reflexivity. rewrite shiftnP_S. exact hc.
    - (* tApp *)
      cbn in ht. move/andP: ht => [h1 h2].
      apply cumulE_App; [exact (IHt1 Γ hΓ h1)|exact (IHt2 Γ hΓ h2)].
    - (* tConst *) reflexivity.
    - (* tInd *) reflexivity.
    - (* tConstruct *) reflexivity.
    - (* tCase *)
      destruct X as (Hpar & _ & Hret).
      cbn in ht. move/and5P: ht => [hp hr hc hd hbrs].
      apply cumulE_Case.
      + unfold cumul_predicate, canon_predicate; cbn. repeat split.
        * exact (canon_spec_list Γ _ Hpar hΓ hp).
        * apply cmp_universe_instance_refl. tc.
        * apply eq_context_upto_names_canon_decl.
        * apply Hret.
          -- exact (on_free_vars_ctx_inst_case_context_weak xpred0 Γ (pparams p) (puinst p)
                      (pcontext p) hp hc hΓ).
          -- eapply open_app_ctx; [apply inst_case_predicate_context_length|exact hr].
      + exact (IHt Γ hΓ hd).
      + exact (canon_spec_brs Γ p l X0 hΓ hp hbrs).
    - (* tProj *) apply cumulE_Proj. cbn in ht. exact (IHt Γ hΓ ht).
    - (* tFix *)
      apply cumulE_Fix. unfold cumul_mfixpoint.
      cbn in ht.
      have hctx : is_closed_context (Γ ,,, fix_context m)
        := on_free_vars_ctx_fix_context_weak xpred0 Γ m (forallb_All _ _ ht) hΓ.
      exact (canon_spec_mfix Γ (fix_context m) #|m| m X hΓ hctx (fix_context_length m) ht).
    - (* tCoFix *)
      apply cumulE_CoFix. unfold cumul_mfixpoint.
      cbn in ht.
      have hctx : is_closed_context (Γ ,,, fix_context m)
        := on_free_vars_ctx_fix_context_weak xpred0 Γ m (forallb_All _ _ ht) hΓ.
      exact (canon_spec_mfix Γ (fix_context m) #|m| m X hΓ hctx (fix_context_length m) ht).
    - (* tPrim *)
      apply cumulE_Prim. destruct p as [? m]; destruct m; cbn in X |- *; try solve [constructor].
      destruct X as (Hty & Hdef & Hval).
      cbn in ht. simp test_prim in ht. cbn in ht.
      move/andP: ht => [/andP [hv hd] hty].
      unfold mapu_array_model; cbn. apply onPrimsArray; cbn.
      + reflexivity.
      + exact (Hdef Γ hΓ hd).
      + exact (Hty Γ hΓ hty).
      + exact (canon_spec_list Γ _ Hval hΓ hv).
  Qed.

End CanonSpec.
