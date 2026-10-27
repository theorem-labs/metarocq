(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed
     PCUICGuardChecker PCUICGuardClosure PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICClosedConv PCUICClosedTyp PCUICInstDef.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * Case well-formedness from typing

  The premises the closure [guard_cl] ([PCUICGuardClosure]) adds to
  [guard_red1] and [guard_inst] are syntactic.  This file discharges them
  from typing, at the six call sites of [PCUICSR] and [PCUICInstTyp]:

  - [type_Case_wf_cases] / [type_Proj_wf_cases]: a [type_Case]/[type_Proj]
    derivation gives the corresponding node of [wf_cases], by projecting
    named premises.  If typing gains a syntactic premise later, the premise
    to add to [wf_cases] is the one this proof does not use.
  - [subject_wf_cases]: a well-typed term is case-well-formed.
  - [wf_local_wf_cases_ctx], [wf_wf_cases_env]: the same for contexts and for
    a well-formed global environment.
  - [well_subst_wf_cases], [typing_closedn_mfix]: the two premises of
    [guard_inst].
  - [wf_cases_case_ctxs_closed]: capture freedom.  In a case-well-formed
    environment, every predicate and branch context of a case-well-formed
    term is closed at [#|pparams|], so [ι] substitutes exactly the
    parameters into it and reads nothing from the case's site. *)

Implicit Types (cf : checker_flags).

(** ** Syntactic helpers *)

Lemma wf_cases_mkApps_inv Σ f args :
  wf_cases Σ (mkApps f args) -> wf_cases Σ f /\ forallb (wf_cases Σ) args.
Proof.
  induction args in f |- *; cbn.
  - intros h. split => //.
  - intros h. apply IHargs in h as [h1 h2].
    cbn in h1. move/andP: h1 => [] hf ha.
    split => //. now apply/andP.
Qed.

Lemma wf_cases_it_mkProd_or_LetIn_inv Σ Δ t :
  wf_cases Σ (it_mkProd_or_LetIn Δ t) -> wf_cases_ctx Σ Δ /\ wf_cases Σ t.
Proof.
  induction Δ in t |- *; cbn.
  - intros h. split => //.
  - rewrite /it_mkProd_or_LetIn /=. intros h.
    apply IHΔ in h as [h1 h2].
    destruct a as [na [b|] ty]; cbn in h2; rewrite /wf_cases_ctx /=;
      rewrite /test_decl /=.
    + move/andP: h2 => [] /andP [] hb hty ht.
      split => //. apply/andP; split => //. now apply/andP.
    + move/andP: h2 => [] hty ht. split => //. now apply/andP.
Qed.

Lemma wf_cases_ctx_app Σ Γ Δ :
  wf_cases_ctx Σ (Γ ,,, Δ) -> wf_cases_ctx Σ Γ /\ wf_cases_ctx Σ Δ.
Proof.
  rewrite /wf_cases_ctx /app_context forallb_app.
  move/andP => [] h1 h2. split => //.
Qed.

(** ** [type_Case]'s and [type_Proj]'s syntactic premises are exactly
       [wf_cases]'s node conditions *)

Lemma type_Case_wf_cases {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1}
  {wf_local_funΣ : context -> Type} {typingΣ : context -> term -> term -> Type}
  {Γ ci p ps mdecl idecl indices predctx ptm brs} :
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  case_side_conditions wf_local_funΣ typingΣ Σ Γ ci p ps mdecl idecl indices predctx ->
  case_branch_typing wf_local_funΣ typingΣ Γ ci p ps mdecl idecl ptm brs ->
  wf_case_node Σ.1 ci p brs.
Proof.
  intros isdecl
    [eq_npars wf_pred cons wf_pctx conv_pctx allowed_elim elim_relevance ind_inst nondep_cofinite]
    [wf_brs brs_ty].
  eapply (wf_case_node_intro (mdecl := mdecl) (idecl := idecl)).
  - unshelve eapply declared_inductive_to_gen; tea.
  - exact eq_npars.
  - exact wf_pred.
  - exact conv_pctx.
  - exact wf_brs.
  - eapply All2i_All2; [exact brs_ty|]. cbn. intros i x y hh. exact hh.1.
  - exact nondep_cofinite.
Qed.

Lemma type_Proj_wf_cases {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1}
  {p mdecl idecl cdecl pdecl} :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl -> wf_proj_node Σ.1 p.
Proof.
  intros isdecl. eapply wf_proj_node_intro.
  unshelve eapply declared_projection_to_gen; tea.
Qed.

(** ** Every well-typed term is case-well-formed *)

Lemma ctx_inst_All_subject {ty : context -> term -> term -> Type} {Q : term -> bool}
  {Γ args Δ} :
  (forall Γ t T, ty Γ t T -> Q t) ->
  ctx_inst ty Γ args Δ -> All Q args.
Proof.
  intros h hc. induction hc.
  - constructor.
  - constructor; eauto.
  - assumption.
Qed.

Lemma typing_wf_cases {cf : checker_flags} :
  env_prop (fun Σ Γ t T => wf_cases Σ.1 t)
           (fun Σ => lift_wfb_term1 (fun Γ t => wf_cases Σ.1 t))
           (fun Σ Γ => wf_cases_ctx Σ.1 Γ).
Proof.
  apply typing_ind_env.

  - (* judgments *)
    intros Σ wfΣ Γ j X.
    destruct X as (Htm & s & (_ & Hty) & _).
    rewrite /lift_wfb_term. apply/andP. split => //.
    destruct (j_term j) as [tm|] => //=. exact Htm.2.

  - (* contexts *)
    intros Σ wfΣ Γ wfΓ hover hall.
    clear hover wfΓ.
    rewrite /wf_cases_ctx. apply All_forallb.
    induction hall.
    + constructor.
    + constructor; [|assumption]. cbn in *. rtoProp. intuition auto.
    + constructor; [|assumption]. cbn in *. rtoProp. intuition auto.

  - (* tRel *) intros Σ wfΣ Γ wfΓ n decl hnth hΓ. reflexivity.
  - (* tSort *) intros Σ wfΣ Γ wfΓ u hΓ hu. reflexivity.

  - (* tProd *)
    intros Σ wfΣ Γ wfΓ na t b s1 s2 hΓ hj hPj hb hPb.
    cbn. rewrite /lift_wfb_term /= in hPj. rtoProp; intuition auto.

  - (* tLambda *)
    intros Σ wfΣ Γ wfΓ na t b bty hΓ hj hPj hb hPb.
    cbn. rewrite /lift_wfb_term /= in hPj. rtoProp; intuition auto.

  - (* tLetIn *)
    intros Σ wfΣ Γ wfΓ na b b_ty b' b'_ty hΓ hj hPj hb' hPb'.
    cbn. rewrite /lift_wfb_term /= in hPj. rtoProp; intuition auto.

  - (* tApp *)
    intros Σ wfΣ Γ wfΓ t na A B u s hΓ hprod hPprod ht hPt hu hPu.
    cbn. rtoProp; intuition auto.

  - (* tConst *) intros Σ wfΣ Γ wfΓ cst u decl hglob hΓ hdecl hcons. reflexivity.
  - (* tInd *) intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl hglob hΓ hcons. reflexivity.
  - (* tConstruct *)
    intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl hglob hΓ hcons. reflexivity.

  - (* tCase *)
    intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl hglob hΓ
      hnpars hpctx predctx hpred hcons hwfpredctx pret hPret hΓpred helim hrel
      hctxinst hc hPc hcofin ptm hbrs hbrsty.
    cbn. rtoProp. repeat split.
    + eapply (type_Case_wf_cases
                (wf_local_funΣ := fun Δ => is_true (wf_cases_ctx Σ.1 Δ))
                (typingΣ := fun Δ t T => (Σ ;;; Δ |- t : T) × wf_cases Σ.1 t)
                (ps := ps) (indices := indices) (predctx := predctx) (ptm := ptm)
                isdecl).
      * econstructor; tea.
      * econstructor; tea.
    + apply All_forallb.
      eapply ctx_inst_All_subject in hctxinst; [|intros ? ? ? hh; exact hh.2].
      now eapply All_app in hctxinst as [].
    + exact hPret.
    + exact hPc.
    + apply All_forallb.
      eapply All2_All_right;
        [eapply All2i_All2; [exact hbrsty|]|intros x y hh; exact hh].
      cbn. intros i x y hh. exact hh.2.2.1.2.

  - (* tProj *)
    intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args hglob hΓ hc hPc hargs.
    cbn. apply/andP. split => //.
    now eapply type_Proj_wf_cases.

  - (* tFix *)
    intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth hΓtypes htypes hPtypes
      hbodies hPbodies hwffix.
    cbn. apply All_forallb.
    eapply (All_impl (All_mix hPtypes hPbodies)).
    intros d [ht hb].
    rewrite /on_def_type /on_def_body /lift_wfb_term /= in ht, hb.
    rewrite /test_def. rtoProp; intuition auto.

  - (* tCoFix *)
    intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth hΓtypes htypes hPtypes
      hbodies hPbodies hwfcofix.
    cbn. apply All_forallb.
    eapply (All_impl (All_mix hPtypes hPbodies)).
    intros d [ht hb].
    rewrite /on_def_type /on_def_body /lift_wfb_term /= in ht, hb.
    rewrite /test_def. rtoProp; intuition auto.

  - (* tPrim *)
    intros Σ wfΣ Γ wfΓ p prim_ty cdecl hΓ hprim hdecl hinv htyp hP.
    destruct p as [[] pv]; cbn in * => //.
    depelim pv. depelim hP. cbn in *.
    rtoProp; repeat split => //.
    now apply All_forallb.

  - (* Cumul *)
    intros Σ wfΣ Γ wfΓ t A B s hΓ ht hPt hB hPB hcum. exact hPt.
Qed.

Lemma subject_wf_cases {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ t T} :
  Σ ;;; Γ |- t : T -> wf_cases Σ.1 t.
Proof. intros h. exact (env_prop_typing typing_wf_cases Σ wfΣ Γ t T h). Qed.

Lemma wf_local_wf_cases_ctx {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ} :
  wf_local Σ Γ -> wf_cases_ctx Σ.1 Γ.
Proof. intros h. exact (env_prop_wf_local typing_wf_cases Σ wfΣ Γ h). Qed.

(** ** A well-formed global environment is case-well-formed *)

Lemma on_type_rel_wf_cases {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T r} :
  on_type_rel (lift_typing typing) Σ Γ T r -> wf_cases Σ.1 T.
Proof.
  intros (_ & s & Hs & _). exact (subject_wf_cases Hs).
Qed.

Lemma wf_wf_cases_env {cf} {Σ : global_env} {wfΣ : wf Σ} : wf_cases_env Σ.
Proof.
  rewrite /wf_cases_env.
  apply (proj2 (forallb_forall _ _)). intros [kn d] hin. cbn.
  destruct d as [cb|mdecl].
  - (* constants *)
    assert (hd : declared_constant Σ kn cb) by exact hin.
    pose proof (on_declared_constant wfΣ hd) as oc.
    destruct oc as (Htm & s & Hs & _).
    apply/andP; split.
    + exact (subject_wf_cases (Σ := (Σ, cst_universes cb)) Hs).
    + destruct cb.(cst_body) as [b|]; cbn in * => //.
      exact (subject_wf_cases (Σ := (Σ, cst_universes cb)) Htm).
  - (* inductives *)
    assert (hd : declared_minductive Σ kn mdecl) by exact hin.
    pose proof (on_declared_minductive wfΣ hd) as oi.
    pose proof (declared_minductive_closed (Σ := Σ) hd) as hcl.
    rewrite /wf_cases_decl.
    apply/andP; split; [apply/andP; split; [apply/andP; split|]|].
    + exact hcl.
    + apply eqb_eq_true. symmetry. exact oi.(onNpars).
    + exact (wf_local_wf_cases_ctx (Σ := (Σ, ind_universes mdecl)) oi.(onParams)).
    + apply All_forallb.
      eapply (Alli_All oi.(onInductives)). intros i idecl oib.
      pose proof (on_type_rel_wf_cases (Σ := (Σ, ind_universes mdecl)) oib.(onArity)) as harity.
      pose proof harity as harity'.
      rewrite oib.(ind_arity_eq) in harity'.
      apply wf_cases_it_mkProd_or_LetIn_inv in harity' as [_ harity'].
      apply wf_cases_it_mkProd_or_LetIn_inv in harity' as [hindices _].
      apply/andP; split; [apply/andP; split|].
      * exact harity.
      * exact hindices.
      * apply All_forallb.
        eapply (All2_All_left oib.(onConstructors)).
        intros cdecl cunivs onc.
        pose proof (on_type_rel_wf_cases (Σ := (Σ, ind_universes mdecl)) onc.(on_ctype)) as hct.
        rewrite onc.(cstr_eq) in hct.
        apply wf_cases_it_mkProd_or_LetIn_inv in hct as [_ hct].
        apply wf_cases_it_mkProd_or_LetIn_inv in hct as [hargs hconcl].
        rewrite /cstr_concl in hconcl.
        apply wf_cases_mkApps_inv in hconcl as [_ hconcl].
        rewrite forallb_app in hconcl.
        move/andP: hconcl => [] _ hind.
        now apply/andP.
Qed.

(** ** The two premises of [guard_inst] *)

Lemma well_subst_wf_cases {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ Δ σ} :
  Σ ;;; Δ ⊢ σ : Γ -> forall x, x < #|Γ| -> wf_cases Σ.1 (σ x).
Proof.
  intros [hσ _] x hx.
  destruct (nth_error Γ x) as [decl|] eqn:hnth.
  - exact (subject_wf_cases (hσ x decl hnth)).
  - apply nth_error_None in hnth. lia.
Qed.

Lemma typing_closedn_mfix {cf} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ mfix} :
  All (on_def_type (lift_typing typing Σ) Γ) mfix ->
  All (on_def_body (lift_typing typing Σ) (fix_context mfix) Γ) mfix ->
  closedn_mfix #|Γ| mfix.
Proof.
  intros htypes hbodies.
  rewrite /closedn_mfix. apply All_forallb.
  eapply (All_impl (All_mix htypes hbodies)).
  intros d [ht hb].
  rewrite /on_def_type in ht. rewrite /on_def_body in hb.
  destruct ht as (_ & s & hty & _).
  destruct hb as (hbody & _).
  rewrite /test_def. apply/andP; split.
  - exact (subject_closed hty).
  - pose proof (subject_closed hbody) as h.
    rewrite app_context_length fix_context_length in h.
    exact h.
Qed.

(** ** Capture freedom *)

Definition case_ctxs_closed (ci : case_info) (p : predicate term)
  (brs : list (branch term)) : bool :=
  closedn_ctx #|p.(pparams)| p.(pcontext) &&
  forallb (fun br => closedn_ctx #|p.(pparams)| br.(bcontext)) brs.

Lemma closed_cstr_branch_context_syn {ind mdecl cdecl} :
  closed_inductive_decl mdecl ->
  closed_constructor_body mdecl cdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (cstr_branch_context ind mdecl cdecl).
Proof.
  intros cl clc.
  move/andP: cl => [] clpars _.
  move/andP: clc => [] /andP [] clargs clinds cltype.
  rewrite /cstr_branch_context /=.
  eapply (closedn_ctx_expand_lets 0) => // /=.
  eapply (closedn_ctx_subst 0). { len. now rewrite Nat.add_comm. }
  eapply closed_inds.
Qed.

Lemma wf_cases_case_ctxs_closed {Σ : global_env} {ci p brs} :
  wf_cases_env Σ -> wf_case_node Σ ci p brs -> case_ctxs_closed ci p brs.
Proof.
  intros henv hnode.
  apply wf_case_node_elim in hnode
    as (mdecl & idecl & hd & hnpars & hpred & [hpctx] & hbrs & [hbrsctx] & _).
  assert (hlook : lookup_env Σ (inductive_mind ci.(ci_ind)) = Some (InductiveDecl mdecl))
    by exact (proj1 hd).
  pose proof (wf_cases_env_lookup henv hlook) as hdecl. cbn in hdecl.
  move/andP: hdecl => [] /andP [] /andP [] hcl hnp _ _.
  apply eqb_eq in hnp.
  assert (hpars : #|p.(pparams)| = context_assumptions mdecl.(ind_params)).
  { rewrite (proj1 hpred). exact hnp. }
  assert (hdi : declared_inductive Σ ci.(ci_ind) mdecl idecl)
    by now apply declared_inductive_from_gen.
  rewrite /case_ctxs_closed. apply/andP; split.
  - rewrite (closedn_ctx_alpha hpctx) hpars.
    now eapply (closed_ind_predicate_context hdi hcl).
  - apply All_forallb.
    eapply (All2_All_right (All2_All_mix_left (closed_ind_closed_cstrs hcl hdi) hbrsctx)).
    cbn. intros cdecl br [hclc heq].
    rewrite (closedn_ctx_alpha heq) hpars.
    now eapply closed_cstr_branch_context_syn.
Qed.

Lemma wf_cases_closed_case_ctxs {Σ : global_env} {t} :
  wf_cases_env Σ -> wf_cases Σ t ->
  test_cases case_ctxs_closed (fun _ => true) t.
Proof.
  intros henv. apply test_cases_impl => //.
  intros ci p brs. now apply wf_cases_case_ctxs_closed.
Qed.
