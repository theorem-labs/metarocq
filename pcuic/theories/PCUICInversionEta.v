(* Distributed under the terms of the MIT license. *)
(** * Inversion of [typingE] (E copy of [PCUICInversion])

  The E twin of every lemma of base [PCUICInversion] whose statement mentions typing or
  conversion: [typing] → [typingE], [wf] → [wfE], [wf_local] → [wf_localE],
  [lift_typing typing] → [lift_typing typingE], [wf_fixpoint]/[wf_cofixpoint] →
  [wf_fixpointE]/[wf_cofixpointE] (the guard premises of [typingE]), the well-scoped
  cumulativity [Σ ;;; Γ ⊢ A ≤ T] → [ws_cumul_pbE Cumul Σ Γ A T] (notation [Σ ;;; Γ ⊢E A ≤ T],
  the checker's, [PCUICTypingEtaDefs]), and base's algorithmic premise
  [Σ ;;; Γ |- T <= U] ([cumulAlgo]) of [into_ws_cumul] → the canonical join
  [JoinE Σ Γ Cumul T U] ([PCUICEtaI5]), as in [wt_cumul_pbE]. Nothing else changes; each
  name takes the suffix [E] (plan [t0-plan.md] §2, D1).

  Not copied: [nth_error_closed_context] mentions neither typing nor conversion; it stays
  base's.

  Routes: closedness from [PCUICClosedTypEta] in place of [PCUICClosedTyp]; the conversion
  premise of [typeE_Cumul] ([cumulSpecE]) enters [ws_cumul_pbE] through I5's
  [into_ws_cumul_pbE_spec] in place of base [cumulSpec_cumulAlgo_curry]; transitivity is
  [ws_cumul_pbE_trans] (A3); the codomain congruence of [inversion_it_mkLambda_or_LetInE]
  is [ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb] (A7) in place of base
  [ws_cumul_pb_it_mkProd_or_LetIn_codom].

  The five fields [inversion_Const], [inversion_LetIn], [inversion_Prod], [inversion_Rel]
  and [inversion_Sort] of the checker's [T6_facts] ([safechecker/theories/
  PCUICTypingEtaHyps.v], branch [wip/etak-k7-2026-10-29]) are [inversion_ConstE],
  [inversion_LetInE], [inversion_ProdE], [inversion_RelE] and [inversion_SortE]:
  [PCUICInversionEtaInstances] type-checks each lemma against the field's text.

**The hypotheses are satisfiable:** [wfE Σ] by any well-formed environment ([wf_incl_E]);
  each typing premise by a concrete derivation of the term form. Instances:
  [PCUICInversionEtaInstances]. [inversion_VarE] and [inversion_EvarE] conclude [False]:
  their premise is unsatisfiable, as in base. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICCases PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICOnFreeVars PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICWsCumulEtaSubst.

From Equations.Prop Require Import DepElim.

Local Notation " Σ ;;; Γ ⊢E t ≤[ pb ] u " := (ws_cumul_pbE pb Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤[ pb ]  u") : type_scope.
Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.

Section InversionE.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wfE Σ).

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Lemma into_ws_cumulE {Γ t T U s} :
    Σ ;;; Γ |-E t : T ->
    Σ ;;; Γ |-E U : tSort s ->
    JoinE Σ Γ Cumul T U ->
    Σ ;;; Γ ⊢E T ≤ U.
  Proof using wfΣ.
    intros hT hU hj.
    exact (into_ws_cumul_pbE hj (typing_closed_contextE hT) (type_is_open_termE hT)
             (subject_is_open_termE hU)).
  Qed.

  Lemma typing_closed_ctxE Γ t T :
    Σ ;;; Γ |-E t : T ->
    is_closed_context Γ.
  Proof using wfΣ.
    intros h. exact (typing_closed_contextE h).
  Qed.
  Hint Immediate typing_closed_ctxE : fvs.

  Lemma typing_ws_cumul_pbE le Γ t T :
    Σ ;;; Γ |-E t : T ->
    Σ ;;; Γ ⊢E T ≤[le] T.
  Proof using wfΣ.
    intros ht. exact (ws_cumul_pbE_refl (typing_closed_contextE ht) (type_is_open_termE ht)).
  Qed.

  (** The conversion premise of [typeE_Cumul], scoped by the two typing premises (I5). *)
  Ltac spec_wsE :=
    match goal with
    | c : cumulSpecE _ _ ?A ?B, hA : typingE _ _ _ ?A, hB : typingE _ _ ?B (tSort _)
      |- ws_cumul_pbE _ _ _ ?A ?B =>
      exact (into_ws_cumul_pbE_spec c (typing_closed_contextE hA) (type_is_open_termE hA)
               (subject_is_open_termE hB))
    end.

  Ltac invtac h :=
    dependent induction h ; [
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | try reflexivity ] .. | try solve [eapply typing_ws_cumul_pbE; econstructor; eauto] ]
    | repeat outsum ;
      repeat outtimes ;
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | reflexivity ] ..
      | try etransitivity ; try eassumption;
        try solve [spec_wsE] ]
    ].

  Derive Signature for typingE.

  Lemma inversion_RelE :
    forall {Γ n T},
      Σ ;;; Γ |-E tRel n : T ->
      ∑ decl,
        wf_localE Σ Γ ×
        (nth_error Γ n = Some decl) ×
        Σ ;;; Γ ⊢E lift0 (S n) (decl_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ n T h. invtac h.
  Qed.

  Lemma inversion_VarE :
    forall {Γ i T},
      Σ ;;; Γ |-E tVar i : T -> False.
  Proof using Type.
    intros Γ i T h. dependent induction h. assumption.
  Qed.

  Lemma inversion_EvarE :
    forall {Γ n l T},
      Σ ;;; Γ |-E tEvar n l : T -> False.
  Proof using Type.
    intros Γ n l T h. dependent induction h. assumption.
  Qed.

  Lemma inversion_SortE :
    forall {Γ s T},
      Σ ;;; Γ |-E tSort s : T ->
      wf_localE Σ Γ ×
      wf_sort Σ s ×
      Σ ;;; Γ ⊢E tSort (Sort.super s) ≤ T.
  Proof using wfΣ.
    intros Γ s T h. invtac h.
  Qed.

  Lemma inversion_ProdE :
    forall {Γ na A B T},
      Σ ;;; Γ |-E tProd na A B : T ->
      ∑ s1 s2,
        lift_typing typingE Σ Γ (j_vass_s na A s1) ×
        Σ ;;; Γ ,, vass na A |-E B : tSort s2 ×
        Σ ;;; Γ ⊢E tSort (Sort.sort_of_product s1 s2) ≤ T.
  Proof using wfΣ.
    intros Γ na A B T h. invtac h.
  Qed.

  Lemma inversion_Prod_sizeE :
    forall {Γ na A B T},
      forall H : Σ ;;; Γ |-E tProd na A B : T,
      ∑ s1 s2 (H1 : lift_typing typingE Σ Γ (j_vass_s na A s1)) (H2 : Σ ;;; Γ ,, vass na A |-E B : tSort s2),
        lift_typing_size (@typingE_size _ _ _) _ H1 < typingE_size H × typingE_size H2 < typingE_size H ×
        Σ ;;; Γ ⊢E tSort (Sort.sort_of_product s1 s2) ≤ T.
  Proof using wfΣ.
    intros Γ na A B T h. unshelve invtac h; eauto.
    all: try revert l; try revert l0; simpl; cbn; lia.
  Qed.

  Lemma inversion_LambdaE :
    forall {Γ na A t T},
      Σ ;;; Γ |-E tLambda na A t : T ->
      ∑ B,
        lift_typing typingE Σ Γ (j_vass na A) ×
        Σ ;;; Γ ,, vass na A |-E t : B ×
        Σ ;;; Γ ⊢E tProd na A B ≤ T.
  Proof using wfΣ.
    intros Γ na A t T h. invtac h.
  Qed.

  Lemma inversion_LetInE :
    forall {Γ na b B t T},
      Σ ;;; Γ |-E tLetIn na b B t : T ->
      ∑ A,
        lift_typing typingE Σ Γ (j_vdef na b B) ×
        Σ ;;; Γ ,, vdef na b B |-E t : A ×
        Σ ;;; Γ ⊢E tLetIn na b B A ≤ T.
  Proof using wfΣ.
    intros Γ na b B t T h. invtac h.
  Qed.

  Lemma inversion_AppE :
    forall {Γ u v T},
      Σ ;;; Γ |-E tApp u v : T ->
      ∑ na A B,
        Σ ;;; Γ |-E u : tProd na A B ×
        Σ ;;; Γ |-E v : A ×
        Σ ;;; Γ ⊢E B{ 0 := v } ≤ T.
  Proof using wfΣ.
    intros Γ u v T h. invtac h.
  Qed.

  Lemma inversion_App_sizeE :
  forall {Γ u v T}
      (H : Σ ;;; Γ |-E tApp u v : T),
      ∑ na A B s  (H1 : Σ ;;; Γ |-E u : tProd na A B) (H2 : Σ ;;; Γ |-E v : A) (H3 : Σ ;;; Γ |-E tProd na A B : tSort s),
      typingE_size H1 < typingE_size H × typingE_size H2 < typingE_size H × typingE_size H3 < typingE_size H ×
        Σ ;;; Γ ⊢E B{ 0 := v } ≤ T.
  Proof using wfΣ.
    intros Γ u v T h. unshelve invtac h.
    4,5,6,10,11,12: eauto.
    all: unfold typingE_size at 2; fold (typingE_size h1); fold (typingE_size h2); try fold (typingE_size h3); lia.
  Qed.

  Lemma inversion_ConstE :
    forall {Γ c u T},
      Σ ;;; Γ |-E tConst c u : T ->
      ∑ decl,
        wf_localE Σ Γ ×
        declared_constant Σ c decl ×
        (consistent_instance_ext Σ decl.(cst_universes) u) ×
        Σ ;;; Γ ⊢E subst_instance u (cst_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ c u T h. invtac h.
  Qed.

  Lemma inversion_IndE :
    forall {Γ ind u T},
      Σ ;;; Γ |-E tInd ind u : T ->
      ∑ mdecl idecl,
        wf_localE Σ Γ ×
        declared_inductive Σ ind mdecl idecl ×
        consistent_instance_ext Σ (ind_universes mdecl) u ×
        Σ ;;; Γ ⊢E subst_instance u idecl.(ind_type) ≤ T.
  Proof using wfΣ.
    intros Γ ind u T h. invtac h.
  Qed.

  Lemma inversion_ConstructE :
    forall {Γ ind i u T},
      Σ ;;; Γ |-E tConstruct ind i u : T ->
      ∑ mdecl idecl cdecl,
        wf_localE Σ Γ ×
        declared_constructor (fst Σ) (ind, i) mdecl idecl cdecl ×
        consistent_instance_ext Σ (ind_universes mdecl) u ×
        Σ;;; Γ ⊢E type_of_constructor mdecl cdecl (ind, i) u ≤ T.
  Proof using wfΣ.
    intros Γ ind i u T h. invtac h.
  Qed.
  Import PCUICEquality.
  Variant case_inversion_dataE Γ ci p c brs mdecl idecl indices :=
   | case_invE
       (ps : sort)
       (eq_npars : mdecl.(ind_npars) = ci.(ci_npar))
       (predctx := case_predicate_context ci.(ci_ind) mdecl idecl p)
       (wf_pred : wf_predicate mdecl idecl p)
       (cons : consistent_instance_ext Σ (ind_universes mdecl) p.(puinst))
       (wf_pctx : wf_localE Σ (Γ ,,, predctx))
       (conv_pctx : eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl))
       (pret_ty : Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps)
       (allowed_elim : is_allowed_elimination Σ idecl.(ind_kelim) ps)
       (elim_relevance : isSortRel ps ci.(ci_relevance))
       (ind_inst : ctx_inst (typingE Σ) Γ (p.(pparams) ++ indices)
                            (List.rev (subst_instance p.(puinst)
                                                      (ind_params mdecl ,,, ind_indices idecl : context))))
       (scrut_ty : Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices))
       (* FORECAST-ONLY (fc/etak-forecast1): base PCUICInversion's BET-339 side condition,
          mirrored; reconciled when F0 lands BET-339 on frac/eta. *)
       (nondep_cofinite : (isCoFinite mdecl.(ind_finite) ==>
                           (ci.(ci_cofix_nondep) ==>
                            on_free_vars (strengthenP 0 1 xpredT) p.(preturn))) = true)
       (ptm := it_mkLambda_or_LetIn predctx p.(preturn))
       (wf_brs : wf_branches idecl brs)
       (brs_ty :
          All2i (fun i cdecl br =>
                   eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
                   let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
                   (wf_localE Σ (Γ ,,, brctxty.1) ×
                   ((Σ ;;; Γ ,,, brctxty.1 |-E br.(bbody) : brctxty.2) ×
                    (Σ ;;; Γ ,,, brctxty.1 |-E brctxty.2 : tSort ps))))
                0 idecl.(ind_ctors) brs).

  Lemma inversion_CaseE :
    forall {Γ ci p c brs T},
      Σ ;;; Γ |-E tCase ci p c brs : T ->
      ∑ mdecl idecl (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl) indices,
        let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
        let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
        case_inversion_dataE Γ ci p c brs mdecl idecl indices ×
        Σ ;;; Γ ⊢E mkApps ptm (indices ++ [c]) ≤ T.
  Proof using wfΣ.
    intros Γ ci p c brs T h.
    dependent induction h.
    {  remember c0; remember c1. destruct c0, c1. repeat insum; repeat intimes; try eapply case_invE ;
	    [ try first [ eassumption | reflexivity ].. | try eapply typing_ws_cumul_pbE; econstructor; eauto ]. }
    repeat outsum; repeat outtimes; repeat insum; repeat intimes ; tea;
      [ try first
      [ eassumption | reflexivity ]..
      | try etransitivity; try eassumption; spec_wsE ].
  Qed.

  Lemma inversion_ProjE :
    forall {Γ p c T},
      Σ ;;; Γ |-E tProj p c : T ->
      ∑ u mdecl idecl cdecl pdecl args,
        declared_projection Σ p mdecl idecl cdecl pdecl ×
        Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ×
        #|args| = ind_npars mdecl ×
        Σ ;;; Γ ⊢E (subst0 (c :: List.rev args)) pdecl.(proj_type)@[u] ≤ T.
  Proof using wfΣ.
    intros Γ p c T h. invtac h.
  Qed.

  Lemma inversion_FixE :
    forall {Γ mfix n T},
      Σ ;;; Γ |-E tFix mfix n : T ->
      ∑ decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ×
        nth_error mfix n = Some decl ×
        All (on_def_type (lift_typing typingE Σ) Γ) mfix ×
        All (on_def_body (lift_typing typingE Σ) (fix_context mfix) Γ) mfix ×
        wf_fixpointE Σ Γ mfix ×
        Σ ;;; Γ ⊢E dtype decl ≤ T.
  Proof using wfΣ.
    intros Γ mfix n T h. invtac h.
  Qed.

  Lemma inversion_CoFixE :
    forall {Γ mfix idx T},
      Σ ;;; Γ |-E tCoFix mfix idx : T ->
      ∑ decl,
        cofix_guard Σ Γ mfix ×
        let types := fix_context mfix in
        nth_error mfix idx = Some decl ×
        All (on_def_type (lift_typing typingE Σ) Γ) mfix ×
        All (on_def_body (lift_typing typingE Σ) (fix_context mfix) Γ) mfix ×
        wf_cofixpointE Σ Γ mfix ×
        Σ ;;; Γ ⊢E decl.(dtype) ≤ T.
  Proof using wfΣ.
    intros Γ mfix idx T h. invtac h.
  Qed.

  Lemma inversion_PrimE :
    forall {Γ p T},
    Σ ;;; Γ |-E tPrim p : T ->
    ∑ prim_ty cdecl,
      [× wf_localE Σ Γ,
        primitive_constant Σ (prim_val_tag p) = Some prim_ty,
        declared_constant Σ prim_ty cdecl,
        primitive_invariants (prim_val_tag p) cdecl,
        primitive_typing_hyps (typingE Σ) Σ Γ p &
        Σ ;;; Γ ⊢E prim_type p prim_ty ≤ T].
  Proof.
    intros Γ p T h. depind h.
    - exists prim_ty, cdecl; split => //.
      eapply typing_ws_cumul_pbE. eapply typeE_Prim; eassumption.
    - destruct IHh1 as [prim_ty [cdecl []]].
      exists prim_ty, cdecl. split => //.
      transitivity A; tea. spec_wsE.
  Qed.

  Lemma inversion_it_mkLambda_or_LetInE :
    forall {Γ Δ t T},
      Σ ;;; Γ |-E it_mkLambda_or_LetIn Δ t : T ->
      ∑ A,
        Σ ;;; Γ ,,, Δ |-E t : A ×
        Σ ;;; Γ ⊢E it_mkProd_or_LetIn Δ A ≤ T.
  Proof using wfΣ.
    intros Γ Δ t T h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - eexists. split ; [exact h|]. cbn.
      exact (typing_ws_cumul_pbE Cumul Γ t T h).
    - simpl. apply ih in h. cbn in h.
      destruct h as [B [h c]].
      apply inversion_LetInE in h as hh.
      destruct hh as (A' & wfA' & Ht & hlt).
      exists A'. split ; eauto.
      cbn. etransitivity; tea.
      eapply ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb.
      assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [B [h c]].
      apply inversion_LambdaE in h as hh.
      pose proof hh as (B' & wfB' & Ht & hlt).
      exists B'. split ; eauto.
      cbn. etransitivity; tea.
      eapply ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb.
      assumption.
  Qed.

End InversionE.
