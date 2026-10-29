(* Distributed under the terms of the MIT license. *)
(** * The typing half of [Typing/PCUICCasesWfTyp] over [typingE]

  The premises the guard closure adds to [guard_red1] and [guard_inst] are
  syntactic; this file discharges them from [typingE] as the base file does from
  [typing]:

  - [type_Case_wf_casesE] / [type_Proj_wf_casesE]: a [typeE_Case]/[typeE_Proj]
    derivation gives the corresponding node of [wf_cases].
  - [typing_wf_casesE], [subject_wf_casesE]: a term well typed in [typingE] is
    case-well-formed.
  - [wf_local_wf_cases_ctxE], [wfE_wf_cases_env]: the same for contexts and for a
    [wfE] global environment.
  - [well_substE_wf_cases], [typingE_closedn_mfix]: the two syntactic premises of
    [guard_inst] and [guard_instE].

  Each lemma states its base twin with [wf] replaced by [wfE], [typing] by [typingE]
  and [well_subst] by [well_substE]. The syntactic lemmas of the base file are used as
  they are; its capture-freedom section mentions no typing and is not copied. The
  proofs are base's. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed
     PCUICGuardChecker PCUICGuardClosure PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICClosedConv PCUICClosedTyp PCUICInstDef PCUICCasesWfTyp
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICInstDefEta PCUICWeakeningEnvTypEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

(** ** [typeE_Case]'s and [typeE_Proj]'s syntactic premises are exactly
       [wf_cases]'s node conditions *)

Lemma type_Case_wf_casesE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1}
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

Lemma type_Proj_wf_casesE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1}
  {p mdecl idecl cdecl pdecl} :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl -> wf_proj_node Σ.1 p.
Proof.
  intros isdecl. eapply wf_proj_node_intro.
  unshelve eapply declared_projection_to_gen; tea.
Qed.

(** ** Every term well typed in [typingE] is case-well-formed *)

Lemma typing_wf_casesE {cf : checker_flags} :
  env_propE (fun Σ Γ t T => wf_cases Σ.1 t)
           (fun Σ => lift_wfb_term1 (fun Γ t => wf_cases Σ.1 t))
           (fun Σ Γ => wf_cases_ctx Σ.1 Γ).
Proof.
  apply typingE_ind_env.

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
    + eapply (type_Case_wf_casesE
                (wf_local_funΣ := fun Δ => is_true (wf_cases_ctx Σ.1 Δ))
                (typingΣ := fun Δ t T => (Σ ;;; Δ |-E t : T) × wf_cases Σ.1 t)
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
    now eapply type_Proj_wf_casesE.

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

Lemma subject_wf_casesE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ t T} :
  Σ ;;; Γ |-E t : T -> wf_cases Σ.1 t.
Proof. intros h. exact (env_propE_typing typing_wf_casesE Σ wfΣ Γ t T h). Qed.

Lemma wf_local_wf_cases_ctxE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ} :
  wf_localE Σ Γ -> wf_cases_ctx Σ.1 Γ.
Proof. intros h. exact (env_propE_wf_local typing_wf_casesE Σ wfΣ Γ h). Qed.

(** ** A [wfE] global environment is case-well-formed *)

Lemma on_type_rel_wf_casesE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ T r} :
  on_type_rel (lift_typing typingE) Σ Γ T r -> wf_cases Σ.1 T.
Proof.
  intros (_ & s & Hs & _). exact (subject_wf_casesE Hs).
Qed.

Lemma wfE_wf_cases_env {cf} {Σ : global_env} {wfΣ : wfE Σ} : wf_cases_env Σ.
Proof.
  rewrite /wf_cases_env.
  apply (proj2 (forallb_forall _ _)). intros [kn d] hin. cbn.
  destruct d as [cb|mdecl].
  - (* constants *)
    assert (hd : declared_constant Σ kn cb) by exact hin.
    pose proof (on_declared_constantE wfΣ hd) as oc.
    destruct oc as (Htm & s & Hs & _).
    apply/andP; split.
    + exact (subject_wf_casesE (Σ := (Σ, cst_universes cb)) Hs).
    + destruct cb.(cst_body) as [b|]; cbn in * => //.
      exact (subject_wf_casesE (Σ := (Σ, cst_universes cb)) Htm).
  - (* inductives *)
    assert (hd : declared_minductive Σ kn mdecl) by exact hin.
    pose proof (on_declared_minductiveE wfΣ hd) as oi.
    pose proof (declared_minductive_closedE (Σ := Σ) hd) as hcl.
    rewrite /wf_cases_decl.
    apply/andP; split; [apply/andP; split; [apply/andP; split|]|].
    + exact hcl.
    + apply eqb_eq_true. symmetry. exact oi.(onNpars).
    + exact (wf_local_wf_cases_ctxE (Σ := (Σ, ind_universes mdecl)) oi.(onParams)).
    + apply All_forallb.
      eapply (Alli_All oi.(onInductives)). intros i idecl oib.
      pose proof (on_type_rel_wf_casesE (Σ := (Σ, ind_universes mdecl)) oib.(onArity)) as harity.
      pose proof (on_type_rel_wf_casesE (Σ := (Σ, ind_universes mdecl)) oib.(onArityRed)) as harity'.
      apply wf_cases_it_mkProd_or_LetIn_inv in harity' as [_ harity'].
      apply wf_cases_it_mkProd_or_LetIn_inv in harity' as [hindices _].
      apply/andP; split; [apply/andP; split|].
      * exact harity.
      * exact hindices.
      * apply All_forallb.
        eapply (All2_All_left oib.(onConstructors)).
        intros cdecl cunivs onc.
        pose proof (on_type_rel_wf_casesE (Σ := (Σ, ind_universes mdecl)) onc.(on_ctype)) as hct.
        rewrite onc.(cstr_eq) in hct.
        apply wf_cases_it_mkProd_or_LetIn_inv in hct as [_ hct].
        apply wf_cases_it_mkProd_or_LetIn_inv in hct as [hargs hconcl].
        rewrite /cstr_concl in hconcl.
        apply wf_cases_mkApps_inv in hconcl as [_ hconcl].
        rewrite forallb_app in hconcl.
        move/andP: hconcl => [] _ hind.
        now apply/andP.
Qed.

(** ** The two syntactic premises of [guard_inst] and [guard_instE] *)

Lemma well_substE_wf_cases {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ Δ σ} :
  well_substE Σ Γ σ Δ -> forall x, x < #|Γ| -> wf_cases Σ.1 (σ x).
Proof.
  intros [hσ _] x hx.
  destruct (nth_error Γ x) as [decl|] eqn:hnth.
  - exact (subject_wf_casesE (hσ x decl hnth)).
  - apply nth_error_None in hnth. lia.
Qed.

Lemma typingE_closedn_mfix {cf} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ mfix} :
  All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
  All (on_def_body (lift_typing typingE Σ) (fix_context mfix) Γ) mfix ->
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
  - exact (subject_closedE hty).
  - pose proof (subject_closedE hbody) as h.
    rewrite app_context_length fix_context_length in h.
    exact h.
Qed.
