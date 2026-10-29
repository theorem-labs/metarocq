(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICConfluence
     PCUICCumulativity PCUICSR PCUICPosition PCUICCasesContexts PCUICEquality
     PCUICGlobalEnv PCUICNamelessDef
     PCUICAlpha PCUICNormal PCUICInversion PCUICReduction PCUICSubstitution
     PCUICConversion PCUICContextConversion PCUICContextConversionTyp PCUICValidity
     PCUICArities PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICGeneration
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICParallelReductionConfluence PCUICWellScopedCumulativity
     PCUICOnFreeVars  PCUICSpine PCUICInductives
     PCUICWeakeningConv PCUICWeakeningTyp PCUICContexts PCUICInductiveInversion.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma wf_inst_case_context {cf Σ} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {uinst params} ctx :
  declared_inductive Σ ci mdecl idecl ->
  wf_local Σ Γ ->
  consistent_instance_ext Σ (ind_universes mdecl) uinst ->
  spine_subst Σ Γ params (List.rev params) (smash_context [] (subst_instance uinst (ind_params mdecl))) ->
  wf_local_rel Σ (Γ,,, smash_context [] (ind_params mdecl)@[uinst]) ctx@[uinst] ->
  wf_local Σ (Γ ,,, inst_case_context params uinst ctx).
Proof.
  move=> isdecl wfΓ cu sp wfr.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  eapply PCUICSubstitution.substitution_wf_local.
  * eapply sp.
  * unshelve epose proof (on_minductive_wf_params_indices_inst isdecl _ cu).
  rewrite PCUICUnivSubstitutionConv.subst_instance_app_ctx in X.
  eapply All_local_env_app_inv in X as [].
  eapply All_local_env_app => //.
  eapply wf_local_smash_end.
  now eapply weaken_wf_local; tea.
Qed.


Lemma alpha_eq_context_closed {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  is_closed_context Γ ->
  is_closed_context Δ.
Proof.
  induction 1 => //.
  rewrite !on_free_vars_ctx_snoc=> /andP[] clx cll.
  apply /andP; split; auto.
  destruct r; unfold ws_decl, test_decl in *; cbn in *; subst; auto; now rewrite -(All2_length X).
Qed.

Lemma alpha_eq_context_ws_cumul_ctx_pb {cf Σ Γ Δ} {wfΣ : wf Σ} :
  eq_context_upto_names Γ Δ ->
  is_closed_context Γ ->
  Σ ⊢ Γ = Δ.
Proof.
  move=> eq cl.
  assert (cl' := alpha_eq_context_closed eq cl).
  eapply eq_context_upto_ws_cumul_ctx_pb => //.
  eapply All2_fold_All2. eapply All2_impl; tea.
  intros x y []; constructor; subst; auto; try reflexivity.
Qed.

Lemma wf_case_inst_case_context {cf Σ} {wfΣ : wf Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) :
  declared_inductive Σ ci mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  forall i cdecl br,
    declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
    wf_branch cdecl br ->
    eq_context_upto_names (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
    wf_local Σ (Γ ,,, inst_case_context (pparams p) (puinst p) br.(bcontext)) ×
     Σ ⊢ Γ ,,, inst_case_context (pparams p) (puinst p) br.(bcontext) =
         Γ ,,, case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl.
Proof.
  intros isdecl Hc wfp bc Hp ptm wfpctx.
  intros i cdecl br declc wfbr onctx.
  destruct (wf_case_branch_type ps args isdecl Hc wfp Hp wfpctx _ _ _ declc wfbr) as []; auto.
  have wfΓ : wf_local Σ Γ by pcuic.
  eapply isType_mkApps_Ind_smash in Hc as [? []]; tea.
  2:{ now rewrite (wf_predicate_length_pars wfp). }
  have wfctx : wf_local Σ (Γ,,, inst_case_branch_context p br).
  { erewrite <- inst_case_branch_context_eq; tea. apply a1. }
  split => //.
  rewrite inst_case_branch_context_eq //.
  eapply ws_cumul_ctx_pb_refl. fvs.
Qed.

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored (Σ : global_env) Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Derive Signature for cored.

  Hint Resolve eq_term_upto_univ_refl : core.

  Context (Σ : global_env_ext).

  Lemma ws_cumul_pb_zippx :
    forall {wfΣ : wf Σ} le Γ u v ρ,
      closedn_stack #|Γ| ρ ->
      Σ ;;; (Γ ,,, stack_context ρ) ⊢ u = v ->
      Σ ;;; Γ ⊢ zippx u ρ ≤[le] zippx v ρ.
  Proof using Type.
    intros wfΣ le Γ u v ρ cl h.
    apply ws_cumul_eq_pb.
    induction ρ in u, v, cl, h |- *; auto.
    destruct a.
    all: try solve [
      unfold zippx ; simpl ;
      eapply ws_cumul_pb_it_mkLambda_or_LetIn_codom ;
      assumption
    ].
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      move: cl => /= /andP[] cl cl'. apply IHρ => //.
      eapply ws_cumul_pb_App_l; tas.
      eapply closedn_on_free_vars; len.
      now rewrite Nat.add_comm.
    - unfold zippx. simpl.
      eapply ws_cumul_pb_it_mkLambda_or_LetIn_codom. cbn.
      eapply ws_cumul_pb_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply ws_cumul_pb_it_mkLambda_or_LetIn_codom. cbn.
      eapply ws_cumul_pb_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply ws_cumul_pb_it_mkLambda_or_LetIn_codom. cbn.
      eapply ws_cumul_pb_LetIn_bo. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall {wfΣ : wf Σ} Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) ⊢ u = v ->
      Σ ;;; Δ ⊢ it_mkLambda_or_LetIn Γ u = it_mkLambda_or_LetIn Γ v.
  Proof using Type.
    intros wfΣ Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply ws_cumul_pb_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply ws_cumul_pb_Lambda_r. assumption.
  Qed.

  Lemma conv_alt_it_mkProd_or_LetIn :
    forall {wfΣ : wf Σ} Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) ⊢ B = B' ->
      Σ ;;; Δ ⊢ it_mkProd_or_LetIn Γ B = it_mkProd_or_LetIn Γ B'.
  Proof using Type.
    intros wfΣ Δ Γ B B' h.
    have cl : is_closed_context (Δ ,,, Γ).
    { now apply ws_cumul_pb_is_closed_context in h. }
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h, cl |- *.
    - assumption.
    - simpl. cbn. eapply ih => //.
      * eapply ws_cumul_pb_LetIn_bo. assumption.
      * rewrite snoc_app_context on_free_vars_ctx_app /= in cl.
        now move/andP: cl.
    - simpl. cbn.
      rewrite snoc_app_context on_free_vars_ctx_app /= in cl.
      move/andP: cl => [cl cld]. cbn in cld.
      rewrite andb_true_r in cld. setoid_rewrite shiftnP_add in cld.
      eapply ih => //.
      eapply ws_cumul_pb_Prod; auto. apply ws_cumul_pb_refl => //.
  Qed.

  Context (hΣ : wf Σ).

  Lemma validity_wf {Γ t T} :
    ∥ Σ ;;; Γ |- t : T ∥ -> welltyped Σ Γ T.
  Proof.
    intros [X].
    eapply validity in X; tas.
    now apply isType_welltyped.
  Defined.

  Lemma wat_welltyped {Γ T} :
    ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
  Proof.
    intros [X].
    now apply isType_welltyped.
  Defined.

  Lemma welltyped_alpha Γ u v :
    welltyped Σ Γ u ->
    u ≡α v ->
    welltyped Σ Γ v.
  Proof using hΣ.
    intros [A h] e.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof using Type.
    intros Γ u v h.
    induction h using red_rect'.
    - right. reflexivity.
    - destruct IHh.
      + left. eapply cored_trans ; eassumption.
      + subst. left. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof using Type.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      cored Σ Γ v u ->
      welltyped Σ Γ v.
  Proof using hΣ.
    intros Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply subject_reduction1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma cored_trans' :
    forall {Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof using Type.
    intros Γ u v w h1 h2.
    revert w h2. induction h1 using red_rect'; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma cored_case :
    forall Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof using Type.
    intros Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma cored_proj :
    forall Γ p c c',
      cored Σ Γ c c' ->
      cored Σ Γ (tProj p c) (tProj p c').
  Proof using Type.
    intros Γ p c c' h.
    induction h in p |- *.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Arguments zip /.

  Lemma welltyped_fill_context_hole Γ π pcontext t :
    wf_local Σ (Γ,,, stack_context π,,, fill_context_hole pcontext t) ->
    welltyped Σ (Γ,,, stack_context π,,, context_hole_context pcontext) t.
  Proof using Type.
    intros wfl.
    destruct pcontext as ((?&h)&?); simpl in *.
    apply All_local_env_app_inv in wfl as (_&wf).
    apply All_local_rel_app_inv in wf as (wf&_).
    destruct h; depelim wf; simpl in *.
    all: destruct l as (Hb & s & Hs & _); cbn in *; econstructor; eauto.
  Qed.

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof using hΣ.
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    1: { econstructor; eauto. }
    destruct a; simpl in *.
    all: apply IHπ in h as (?&typ).
    all: try apply inversion_App in typ as (?&?&?&?&?&?); auto.
    all: try apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    all: try apply inversion_Prod in typ as (?&?&?&?&?); auto.
    all: try apply inversion_Lambda in typ as (?&?&?&?); auto.
    all: try apply inversion_LetIn in typ as (?&?&?&?); auto.
    all: try solve [econstructor; eauto].
    - apply inversion_Fix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isTypeRel_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0. destruct o as (t0 & _); cbn in t0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_CoFix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isTypeRel_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0. destruct o as (t0 & _); cbn in t0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      rewrite app_context_assoc.
      destruct p.
      + apply validity in scrut_ty as (_ & ? & typ & _).
        clear brs_ty.
        apply inversion_mkApps in typ as (?&_&spine); auto; simpl in *.
        clear -spine.
        rewrite -app_assoc -app_comm_cons in spine.
        revert spine; generalize (tSort x3); intros t' spine.
        induction params1 in spine, x4, t' |- *; cbn in *.
        * depelim spine.
          econstructor; eauto.
        * depelim spine; eauto.
      + cbn. exists (tSort ps).
        cbn. move: pret_ty. cbn [fill_predicate_hole preturn].
        move=> Ht.
        cbn [fill_predicate_hole preturn] in predctx.
        eapply context_conversion; tea.
        * unfold predctx in Ht.
          eapply typing_wf_local in scrut_ty.
          eapply wf_inst_case_context; tea.
          ** cbn in ind_inst.
             unshelve epose proof (ctx_inst_spine_subst _ ind_inst).
             { eapply weaken_wf_local; tea.
               eapply (on_minductive_wf_params_indices_inst x1); tas. }
              move: X. generalize (ctx_inst_sub ind_inst).
              intros l.
              rewrite subst_instance_app => X.
              unshelve epose proof (spine_subst_app_inv _ X) as [sp _].
              { rewrite (wf_predicate_length_pars wf_pred). len.
                eapply (declared_minductive_ind_npars x1). }
              now eapply spine_subst_smash in sp.
          ** cbn in conv_pctx.
             eapply All_local_env_app_inv. eapply wf_local_alpha.
             ++ instantiate (1 := (Γ,,, stack_context π,,, smash_context [] (ind_params x)@[puinst],,, (ind_predicate_context ci x x0)@[puinst])).
                eapply All2_app => //.
                { eapply alpha_eq_subst_instance. now symmetry. }
                reflexivity.
             ++ eapply wf_ind_predicate; tea.

        * rewrite /predctx.
          cbn in conv_pctx.
          rewrite /case_predicate_context /= /case_predicate_context_gen.
          rewrite /pre_case_predicate_context_gen.
          rewrite /inst_case_context.
          apply eq_context_upto_names_conv_context.
          eapply All2_app. 2:{ reflexivity. }
          apply (PCUICAlpha.inst_case_predicate_context_eq (ind:=ci) wf_pred).
          cbn. now symmetry.

    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      econstructor; eauto.
    - apply inversion_Case in typ as (mdecl&idecl&decli&args&[]&?); auto.
      destruct brs as ((?&?)&?).
      simpl fill_branches_hole in brs_ty.
      destruct b; cbn in *.
      set (br := {| bcontext := bcontext; bbody := t |}) in *.
      apply All2i_app_inv_r in brs_ty as (?&?&?&?&a).
      eapply All2i_length in a0.
      depelim a. clear a.
      destruct p0 as (wfl&(cc&typ&r)). clear r.
      rewrite -app_assoc.
      eexists.
      pose proof (typing_wf_local scrut_ty).
      eapply validity in scrut_ty.
      have declc : declared_constructor Σ (ci, #|x|) mdecl idecl x1.
      { split; auto. rewrite e /= nth_error_app_ge // Nat.sub_diag //. }
      have wf_branch : wf_branch x1 {| bcontext := bcontext; bbody := t |}.
      { eapply Forall2_All2 in wf_brs. eapply All2_nth_error with (n := #|x|) in wf_brs; tea.
        * rewrite e /= nth_error_app_ge // Nat.sub_diag //.
        * rewrite a0 /= nth_error_app_ge // Nat.sub_diag //. }
      destruct (wf_case_inst_case_context ps args decli scrut_ty wf_pred pret_ty conv_pctx
        _ _ _ declc wf_branch wfl).
      cbn in *.
      eapply closed_context_conversion; tea.
      now symmetry.
    - apply unlift_TypUniv in l. now econstructor.
    - now eapply isTypeRel_welltyped.
    - apply unlift_TermTyp in l. now econstructor.
    - apply lift_sorting_forget_body in l. now eapply isTypeRel_welltyped.
    - eapply inversion_Prim in typ as (?&?&[]); eauto.
      depelim p0. now eexists.
    - eapply inversion_Prim in typ as (?&?&[]); eauto.
      depelim p0. now eexists.
    - eapply inversion_Prim in typ as (?&?&[]); eauto.
      depelim p0. cbn in *.
      eapply All_app in hvalue as [_ hvalue]. depelim hvalue.
      now eexists.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof using Type.
    intros Γ u v h.
    induction h.
    - constructor. now constructor.
    - destruct IHh as [r].
      constructor. etransitivity; eauto.
  Qed.

  Lemma cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof using Type.
    intros Γ t u π h. induction h.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma decompose_stack_closed n ρ l s :
    closedn_stack n ρ -> decompose_stack ρ = (l, s) ->
    forallb (closedn (n + #|stack_context ρ|)) l.
  Proof using Type.
    induction ρ in l, s |- *; cbn.
    - now intros _ [= <- <-].
    - move/andP=> [cla clρ].
      destruct a ; [idtac|intros [= <- <-]..] => //.
      destruct decompose_stack eqn:ds.
      intros [= <- <-].
      specialize (IHρ _ _ clρ eq_refl).
      cbn in cla |- *.
      now rewrite IHρ cla.
  Qed.

  (* Ill-scoped, if the stack has a context *)
  (*Lemma conv_zipp :
    forall Γ u v ρ,
      closedn_stack #|Γ| ρ ->
      Σ ;;; Γ ⊢ u = v ->
      Σ ;;; Γ ⊢ zipp u ρ = zipp v ρ.
  Proof.
    intros Γ u v ρ cl h.
    unfold zipp.
    destruct decompose_stack eqn:da.
    induction l in u, v, cl, h, da |- *.
    - assumption.
    - simpl. eapply IHl => //.
      * eapply ws_cumul_pb_App_l; tas.
        eapply decompose_stack_closed in da; tea.
        move: da => /= /andP[].
  Qed.*)

  (* Lemma cumul_zipp :
    forall Γ u v π,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipp u π <= zipp v π.
  Proof.
    intros Γ u v π h.
    unfold zipp.
    destruct decompose_stack as [l ρ].
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply cumul_App_l. assumption.
  Qed. *)

  Derive Signature for Acc.

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof using Type.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof using Type.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  (* TODO Put more general lemma in Inversion *)
  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof using hΣ.
    intros Γ Δ t (T & h).
    apply inversion_it_mkLambda_or_LetIn in h as (T' & h & hle); tas.
    now econstructor.
  Qed.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof using Type.
    intros Γ Δ t [T h].
    eexists. eapply PCUICGeneration.type_it_mkLambda_or_LetIn.
    eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn_iff :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) <->
      welltyped Σ (Γ ,,, Δ) t.
  Proof using hΣ.
    intros. split.
    - apply welltyped_it_mkLambda_or_LetIn.
    - apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma welltyped_zipx :
    forall {Γ t π},
      welltyped Σ [] (zipx Γ t π) ->
      welltyped Σ Γ (zipc t π).
  Proof using hΣ.
    intros Γ t π h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma welltyped_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> welltyped Σ Γ (zipc t π)
      -> welltyped Σ (Γ ,,, stack_context π) (zipc t (appstack args [])).
  Proof using hΣ.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (welltyped_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  Lemma red_const :
    forall {Γ c u cty cb cu rel},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu;
        cst_relevance := rel |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance u cb).
  Proof using Type.
    intros Γ c u cty cb cu rel e.
    econstructor. econstructor.
    - apply declared_constant_from_gen. symmetry in e. exact e.
    - reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ c u cty cb cu rel},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu;
        cst_relevance := rel |})
      = lookup_env Σ c ->
      cored Σ Γ (subst_instance u cb) (tConst c u).
  Proof using Type.
    intros Γ c u cty cb cu rel e.
    symmetry in e.
    econstructor.
    econstructor.
    - apply declared_constant_from_gen. exact e.
    - reflexivity.
  Qed.

  Lemma app_cored_r :
    forall Γ u v1 v2,
      cored Σ Γ v1 v2 ->
      cored Σ Γ (tApp u v1) (tApp u v2).
  Proof using Type.
    intros Γ u v1 v2 h.
    induction h.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof using Type.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof using Type.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isSortmkApps :
    forall t l,
      isSort (mkApps t l) ->
      l = [].
  Proof using Type.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. exfalso. discriminate.
  Qed.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof using hΣ.
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prod in hP as [s1 [s2 [? [? bot]]]] ; auto.
      apply ws_cumul_pb_Sort_Prod_inv in bot ; auto.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof using hΣ.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.

  Fixpoint isAppPrim (t : term) : bool :=
    match t with
    | tApp t l => isAppPrim t
    | tPrim p => true
    | _ => false
    end.

  Lemma isAppPrim_mkApps :
    forall t l, isAppPrim (mkApps t l) = isAppPrim t.
  Proof using Type.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Definition isPrim t :=
    match t with
    | tPrim _ => true
    | _ => false
    end.

  Lemma isPrimmkApps :
    forall t l,
      isPrim (mkApps t l) ->
      l = [].
  Proof using Type.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isAppPrim_isPrim :
    forall Γ t,
      isAppPrim t ->
      welltyped Σ Γ t ->
      isPrim t.
  Proof using hΣ.
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    2:reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prim in hP as [s1 [s2 [? htyp ? ? ? bot]]] ; auto.
      (* The guard on the axiom inversions: [s1] is the registered primitive
         TYPE constant, which §4.2(a)1 keeps out of the operation table. *)
      assert (hnop : prim_op_of Σ s1 = None).
      { pose proof hΣ as [_ [wfr _]]. eapply prim_op_of_primitive_constant; tea. }
      now eapply invert_cumul_prim_type_prod in bot.
  Qed.

  Lemma mkApps_Prim_nil :
    forall Γ p l,
      welltyped Σ Γ (mkApps (tPrim p) l) ->
      l = [].
  Proof using hΣ.
    intros Γ p l h.
    pose proof (isAppPrim_isPrim) as hh.
    specialize hh with (2 := h).
    rewrite isAppPrim_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isPrimmkApps in hh. assumption.
  Qed.

  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof using Type.
    intros π l ρ e.
    destruct ρ; auto.
    destruct s.
    all: auto.
    exfalso. eapply decompose_stack_not_app. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma stack_context_decompose :
    forall π,
      stack_context (snd (decompose_stack π)) = stack_context π.
  Proof using Type.
    intros π.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack. reflexivity.
  Qed.

  Lemma decompose_stack_stack_cat π π' :
    decompose_stack (π ++ π') =
    ((decompose_stack π).1 ++
     match (decompose_stack π).2 with
     | [] => (decompose_stack π').1
     | _ => []
     end,
     (decompose_stack π).2 ++
     match (decompose_stack π).2 with
     | [] => (decompose_stack π').2
     | _ => π'
     end).
  Proof using Type.
    induction π in π' |- *; cbn in *; auto.
    - now destruct decompose_stack.
    - destruct a; auto.
      rewrite !IHπ.
      now destruct (decompose_stack π).
  Qed.

  Lemma zipp_stack_cat π π' t :
    isStackApp π = false ->
    zipp t (π' ++ π) = zipp t π'.
  Proof using Type.
    intros no_stack_app.
    unfold zipp.
    rewrite decompose_stack_stack_cat.
    destruct (decompose_stack π') eqn:decomp.
    cbn.
    destruct s; try now rewrite app_nil_r.
    now destruct π as [|[] ?]; cbn in *; rewrite ?app_nil_r.
  Qed.

  Lemma zipp_appstack t args π :
    zipp t (appstack args π) = zipp (mkApps t args) π.
  Proof using Type.
    unfold zipp.
    rewrite decompose_stack_appstack.
    rewrite mkApps_app.
    now destruct decompose_stack.
  Qed.

  Lemma fst_decompose_stack_nil π :
    isStackApp π = false ->
    (decompose_stack π).1 = [].
  Proof using Type. now destruct π as [|[] ?]. Qed.

  Lemma zipp_as_mkApps t π :
    zipp t π = mkApps t (decompose_stack π).1.
  Proof using Type.
    unfold zipp.
    now destruct decompose_stack.
  Qed.

  Lemma zipp_noStackApp t π :
    isStackApp π = false ->
    zipp t π = t.
  Proof using Type.
    intros.
    now rewrite zipp_as_mkApps fst_decompose_stack_nil.
  Qed.

  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof using Type.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Hint Resolve cumul_refl cumul_alt : core.
  Hint Resolve cumul_refl : core.

  Lemma cored_red_cored :
    forall Γ u v w,
      cored Σ Γ w v ->
      red Σ Γ u v ->
      cored Σ Γ w u.
  Proof using Type.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - eapply cored_red_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
  Proof using Type.
    intros Γ u v r n.
    destruct r using red_rect'.
    - exfalso. apply n. reflexivity.
    - eapply cored_red_cored ; try eassumption.
      constructor. assumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof using hΣ.
    intros Γ u v h [r].
    revert h. induction r using red_rect' ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof using Type.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 using red_rect' ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma Proj_red_cond :
    forall Γ p i' c u l,
      welltyped Σ Γ (tProj p (mkApps (tConstruct i' c u) l)) ->
      nth_error l (p.(proj_npars) + p.(proj_arg)) <> None.
  Proof using hΣ.
    intros Γ p i' c u l [T h].
    apply PCUICInductiveInversion.invert_Proj_Construct in h as (<-&->&?).
    2: now sq.
    now apply nth_error_Some.
  Qed.

  Lemma cored_zipc :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zipc t π) (zipc u π).
  Proof using Type.
    intros Γ t u π h.
    do 2 zip fold. eapply cored_context. assumption.
  Qed.

  Lemma red_zipc :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zipc t π) (zipc u π).
  Proof using Type.
    intros Γ t u π h.
    do 2 zip fold. eapply red_context_zip. assumption.
  Qed.

  Lemma welltyped_zipc_zipp :
    forall Γ t π,
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ (Γ ,,, stack_context π) (zipp t π).
  Proof using hΣ.
    intros Γ t π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    zip fold in h.
    apply welltyped_context in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.

  Lemma conv_cum_zipp leq Γ t t' π π' :
    ∥ Σ ;;; Γ ⊢ t ≤[leq] t' ∥ ->
    ∥ws_cumul_pb_terms Σ Γ (decompose_stack π).1 (decompose_stack π').1∥ ->
    ∥Σ ;;; Γ ⊢ zipp t π ≤[leq] zipp t' π'∥.
  Proof using hΣ.
    intros conv conv_args.
    rewrite !zipp_as_mkApps.
    sq; eapply ws_cumul_pb_mkApps; auto.
  Qed.

  Lemma whne_All2_fold f rel Γ Γ' t :
    (forall Γ Γ' c c', rel Γ Γ' c c' -> (decl_body c = None <-> decl_body c' = None)) ->
    whne f Σ Γ t ->
    All2_fold rel Γ Γ' ->
    whne f Σ Γ' t.
  Proof using Type.
    intros behaves wh conv.
    induction wh; eauto using whne.
    destruct nth_error eqn:nth; [|easy].
    cbn in *.
    eapply All2_fold_nth in nth; eauto.
    destruct nth as (?&eq&?&?).
    constructor.
    rewrite eq.
    cbn.
    specialize (behaves _ _ _ _ r).
    f_equal.
    apply behaves.
    congruence.
  Qed.

  Lemma whnf_All2_fold f rel Γ Γ' t :
    (forall Γ Γ' c c', rel Γ Γ' c c' -> (decl_body c = None <-> decl_body c' = None)) ->
    whnf f Σ Γ t ->
    All2_fold rel Γ Γ' ->
    whnf f Σ Γ' t.
  Proof using Type.
    intros behaves wh conv.
    induction wh; eauto using whnf.
    - apply whnf_ne. eapply whne_All2_fold; eauto.
  Qed.

  Lemma whne_conv_context f Γ Γ' t :
    whne f Σ Γ t ->
    conv_context cumulAlgo_gen Σ Γ Γ' ->
    whne f Σ Γ' t.
  Proof using Type.
    apply whne_All2_fold.
    intros ? ? ? ? r.
    now depelim r.
  Qed.

  Lemma whnf_conv_context f Γ Γ' t :
    whnf f Σ Γ t ->
    conv_context cumulAlgo_gen Σ Γ Γ' ->
    whnf f Σ Γ' t.
  Proof using Type.
    apply whnf_All2_fold.
    intros ? ? ? ? r.
    now depelim r.
  Qed.

  Lemma Case_Construct_ind_eq :
    forall {Γ ci ind' pred i u brs args},
      welltyped Σ Γ (tCase ci pred (mkApps (tConstruct ind' i u) args) brs) ->
      ci.(ci_ind) = ind'.
  Proof using hΣ.
    intros Γ ci ind' pred i u brs args [A h].
    apply PCUICInductiveInversion.invert_Case_Construct in h; intuition auto using sq.
  Qed.

  Lemma Proj_Construct_ind_eq :
    forall Γ p i' c u l,
      welltyped Σ Γ (tProj p (mkApps (tConstruct i' c u) l)) ->
      p.(proj_ind) = i'.
  Proof using hΣ.
    intros Γ p i' c u l [T h].
    now apply PCUICInductiveInversion.invert_Proj_Construct in h.
  Qed.
End Lemmata.

Lemma weakening_env_cored {cf : checker_flags} (Σ Σ' : global_env) (Hext : extends Σ Σ') (HΣ' : wf Σ') Γ :
  forall x y, cored Σ Γ x y -> cored Σ' Γ x y.
Proof.
  induction 1; econstructor; now eauto using weakening_env_red1.
Qed.

Lemma welltyped_brs {cf} (Σ : global_env_ext) (HΣ :∥ wf_ext Σ ∥)  Γ ci p t2 brs T : Σ ;;; Γ |- tCase ci p t2 brs : T ->
    ∥ All (fun br => welltyped Σ (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ∥.
Proof.
  intros Ht. destruct HΣ. constructor.
  eapply inversion_Case in Ht as (mdecl & idecl & decli & indices & data & hty); auto.
  destruct data.
  eapply validity in scrut_ty.
  eapply forall_nth_error_All => i br hnth.
  eapply All2i_nth_error_r in brs_ty; tea.
  destruct brs_ty as [cdecl [hnthc [eqctx [wfbctxty [tyb _]]]]].
  have declc: declared_constructor Σ (ci, i) mdecl idecl cdecl.
  { split; auto. }
  have wfbr : wf_branch cdecl br.
  { eapply Forall2_All2 in wf_brs. eapply All2_nth_error in wf_brs; tea. }
  have wfΓ : wf_local Σ Γ.
  { eapply typing_wf_local in pret_ty. now eapply All_local_env_app_inv in pret_ty as []. }
  epose proof (wf_case_inst_case_context ps indices decli scrut_ty wf_pred pret_ty conv_pctx
    _ _ _ declc wfbr eqctx) as [wfictx eqictx].
  eexists.
  eapply closed_context_conversion; tea.
  now symmetry.
Qed.

#[global] Hint Resolve isType_welltyped : pcuic.

From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion PCUICViews
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICFixWitness
  PCUICInductiveInversion PCUICNormal
  PCUICParallelReductionConfluence
  PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity.

Local Set Default Goal Selector "1".
Local Unset Equations With UIP.
Local Unset Keyed Unification.

Lemma isArity_subst:
  forall x2 : term, forall s n, isArity x2 -> isArity (subst s n x2).
Proof.
  induction x2; cbn in *; try tauto; intros; eauto.
Qed.

Lemma isArity_typing_spine {cf:checker_flags} {Σ : global_env_ext} {Γ L T T'} {wfΣ : wf Σ} :
  wf_local Σ Γ ->
  typing_spine Σ Γ T' L T ->
  Is_conv_to_Arity Σ Γ T' ->
  Is_conv_to_Arity Σ Γ T.
Proof.
  intros wfΓ sp isc.
  depind sp.
  - destruct isc as (? & ? & ?). sq.
    eapply red_ws_cumul_pb_inv in H.
    eapply (ws_cumul_pb_trans _ _ _ H) in w; tea.
    eapply PCUICConversion.invert_cumul_arity_l in w; eauto.
  - eapply IHsp.
    destruct isc as (? & ? & ?). sq.
    eapply red_ws_cumul_pb_inv in H.
    eapply (ws_cumul_pb_trans _ _ _ H) in w; tea.
    eapply invert_cumul_arity_l in w; eauto.
    destruct w as (? & H1 & H2). sq.
    eapply invert_red_prod in H1 as (? & ? & []); eauto; subst.
    exists (x2 {0 := hd}). split; sq.
    eapply (closed_red_untyped_substitution0 (Δ := [_])); eauto. econstructor. econstructor.
    cbn; fvs.
    now eapply isArity_subst.
Qed.

Section Arities.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Lemma invert_cumul_arity_l_gen (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ ;;; Γ ⊢ C ≤ T -> Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [ar [red isA]]. sq.
    intros cum.
    have: Σ ;;; Γ ⊢ ar ≤ T.
    { eapply ws_cumul_pb_red_l_inv; tea. exact red. }
    now eapply invert_cumul_arity_l.
  Qed.

  Lemma invert_cumul_arity_r_gen (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ;;; Γ ⊢ T ≤ C -> Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [ar [red isA]]. sq.
    intros cum.
    have: Σ ;;; Γ ⊢ T ≤ ar.
    { eapply ws_cumul_pb_red_r_inv; tea. exact red. }
    now eapply invert_cumul_arity_r.
  Qed.

  Lemma isArity_ind ind i args : isArity (mkApps (tInd ind i) args) -> False.
  Proof. destruct args using rev_case; rewrite ?mkApps_app; auto. Qed.

  Lemma Is_conv_to_Arity_ind Γ ind i args : Is_conv_to_Arity Σ Γ (mkApps (tInd ind i) args) -> False.
  Proof.
    intros [ar [red eq]]. sq.
    eapply invert_red_mkApps_tInd in red as (? & []); auto. subst ar.
    now eapply isArity_ind in eq.
  Qed.

  Lemma typing_spine_arity_mkApps_Ind Γ T l i u args :
    wf_local Σ Γ ->
    PCUICArities.typing_spine Σ Γ T l (mkApps (tInd i u) args) ->
    Is_conv_to_Arity Σ Γ T -> False.
  Proof.
    intros wf sp isc.
    eapply (isArity_typing_spine wf sp) in isc.
    now eapply Is_conv_to_Arity_ind.
  Qed.

End Arities.

Section Spines.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.
  Context (wfΣ : wf Σ.1).

  (** The start of the spine lemmas: the spine also applies the reduct of the
      declared type that the check accepts. *)
  Lemma mfix_on_ind_spine_witness {check} `{ShapeCheck check} {ok} Γ mfix idx decl args ty :
    mfix_on_ind check (conv_witness Σ Γ) ok mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    typing_spine Σ Γ (dtype decl) args ty ->
    ∑ mind tw,
      [× Σ ;;; Γ ⊢ dtype decl ⇝ tw, check (def_with_type decl tw) = Some mind, ok mind,
         isType Σ Γ tw & typing_spine Σ Γ tw args ty].
  Proof.
    move=> hm nthe isty sp.
    have clΓ : is_closed_context Γ.
    { eapply wf_local_closed_context. now eapply isType_wf_local. }
    have opd : is_open_term Γ (dtype decl) by eapply isType_is_open_term.
    eapply mfix_on_ind_inv in nthe as [mind [tw [r cfix ck]]]; tea.
    have istw : isType Σ Γ tw by eapply isType_red; [exact isty|exact (clrel_rel r)].
    exists mind, tw; split => //.
    eapply typing_spine_strengthen; [exact sp|exact istw|now eapply red_ws_cumul_pb_inv].
  Qed.


  Lemma cumul_it_mkProd_or_LetIn_smash Γ Δ T :
    is_closed_context Γ ->
    is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
    Σ ;;; Γ ⊢ it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T) = it_mkProd_or_LetIn Δ T.
  Proof.
    intros clΓ clp. symmetry. eapply red_ws_cumul_pb.
    now apply red_it_mkProd_or_LetIn_to_smash.
  Qed.

  Lemma typing_spine_smash Γ Δ T args T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    typing_spine Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'.
  Proof.
    intros sp.
    have ty := (typing_spine_isType_dom sp).
    have r := (red_it_mkProd_or_LetIn_to_smash (wfΣ := wfΣ) Γ Δ T).
    specialize (r (wf_local_closed_context (isType_wf_local ty)) (isType_is_open_term ty)).
    eapply typing_spine_strengthen; tea.
    eapply isType_red; tea. eapply r.
    eapply ws_cumul_pb_eq_le; symmetry.
    now eapply red_ws_cumul_pb.
  Qed.

Lemma assumption_context_assumptions {Γ} :
  assumption_context Γ ->
  context_assumptions Γ = #|Γ|.
Proof.
  induction 1; cbn; auto. congruence.
Qed.


  Lemma typing_spine_nth_error Γ Δ T args T' n arg decl :
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = Some arg ->
    nth_error (List.rev Δ) n = Some decl ->
    Σ ;;; Γ |- arg : subst (List.rev (firstn n args)) 0 decl.(decl_type).
  Proof.
    intros ass wf sp hnth hdecl.
    eapply typing_spine_nth_error in sp; tea.
    2:{ eapply nth_error_Some_length in hdecl. len in hdecl.
        move: (context_assumptions_bound Δ).
        pose proof (assumption_context_assumptions ass). lia. }
    destruct sp as [decl' [hdecl' harg]].
    pose proof (nth_error_Some_length hdecl).
    rewrite (smash_assumption_context _ ass) in hdecl'.
    rewrite nth_error_rev // List.rev_involutive in hdecl.
    len in hdecl. rewrite (assumption_context_assumptions ass) in hdecl'.
    rewrite hdecl in hdecl'. noconf hdecl'. exact harg.
  Qed.

  Lemma typing_spine_all_inv Γ Δ T args T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    #|args| = context_assumptions Δ ->
    (Σ ;;; Γ ⊢ subst (List.rev args) 0 (expand_lets Δ T) ≤ T') * (isType Σ Γ T').
  Proof.
    induction Δ in args, T |- * using ctx_length_rev_ind.
    - simpl. destruct args => // sp _ /=; rewrite subst_empty expand_lets_nil.
      now depelim sp.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_inv in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp).
        forward X by now len.
        now rewrite expand_lets_vdef.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => hargs. simpl in hargs.
        rewrite Nat.add_1_r in hargs. destruct args => //.
        depelim sp. noconf hargs.
        eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna dom codom].
        rewrite expand_lets_vass. simpl.
        eapply (substitution0_ws_cumul_pb (t:=t)) in codom; eauto.
        eapply typing_spine_strengthen in sp. 3:tea.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [t] 0 Γ0) ltac:(len; reflexivity) (subst [t] #|Γ0| T) _ sp).
        forward X by now len.
        rewrite subst_app_simpl /=; len; rewrite H.
        now rewrite -(expand_lets_subst_comm _ _ _).
        eapply isType_apply in i; tea.
        eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
        eapply isTypeRel_isType.
        now eapply isType_tProd in i as [].
  Qed.

  Lemma typing_spine_more_inv Γ Δ ind u args args' T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
    #|args'| > context_assumptions Δ -> False.
  Proof.
    induction Δ in args, args' |- * using ctx_length_rev_ind.
    - simpl. destruct args' using rev_case => /= // sp hargs // /=; try lia.
      depelim sp. eapply (f_equal (@length _)) in H; simpl in H; len in H; simpl in H.
      now eapply invert_cumul_ind_prod in w.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_inv in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp). now len.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => /= hargs.
        rewrite Nat.add_1_r in hargs. destruct args'; simpl in * => //. lia.
        depelim sp.
        eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna dom codom]; pcuic.
        eapply (substitution0_ws_cumul_pb (t:=t)) in codom; eauto.
        eapply typing_spine_strengthen in sp. 3:tea.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [t] 0 Γ0) ltac:(len; reflexivity) _ _ sp).
        now len.
        eapply isType_apply in i; tea.
        eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
        eapply isTypeRel_isType.
        now eapply isType_tProd in i as [].
  Qed.

  Lemma firstn_subst_context (Γ : context) n k s :
    assumption_context Γ ->
    firstn (#|Γ| - n) (subst_context s k Γ) =
    subst_context s (k + n) (firstn (#|Γ| - n) Γ).
  Proof.
    induction Γ in n, k |-  * using ctx_length_rev_ind; simpl; auto.
    destruct d as [na [b|] ty]; simpl; len; simpl; auto;
    rewrite subst_context_app /=.
    intros ass. eapply assumption_context_app in ass as [_ ass]. depelim ass.
    intros ass. eapply assumption_context_app in ass as [ass _].
    destruct n.
    rewrite Nat.sub_0_r.
    rewrite !firstn_all2;
     rewrite ?length_app ?app_context_length ?subst_context_length ?Nat.add_0_r /=; simpl; try lia.
    now rewrite subst_context_app.
    replace (#|Γ| + 1 - S n) with (#|Γ| - n) by lia.
    rewrite /app_context !firstn_app ?subst_context_length /= Nat.sub_0_r.
    replace (#|Γ| - n - #|Γ|) with 0 by lia. simpl.
    rewrite Nat.add_succ_r !app_nil_r. apply H; now try lia.
  Qed.

  Lemma typing_spine_nth_error_None Γ Δ T args T' :
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args #|Δ| = None ->
    Σ ;;; Γ ⊢ (subst0 (List.rev args) (it_mkProd_or_LetIn (firstn (#|Δ| - #|args|) Δ) T)) ≤ T'.
  Proof.
    induction Δ in args, T |- * using ctx_length_rev_ind.
    { intros. eapply nth_error_None in H0. simpl in H0 |- *. destruct args => //; simpl in H0; try lia.
      rewrite subst_empty. simpl in X0. now depelim X0. }
    destruct d as [na [b|] ty]; intros ass; eapply assumption_context_app in ass as [assΓ ass].
    * exfalso; depelim ass.
    * simpl. rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= //.
      intros wf sp.
      pose proof (All_local_env_app_inv wf) as [_ wfty].
      eapply All_local_env_app_inv in wfty as [wfty _]. depelim wfty.
      intros Hargs. eapply nth_error_None in Hargs.
      len in Hargs. len; simpl.
      depelim sp.
      + eapply ws_cumul_pb_Prod_l_inv in w as [na' [dom [codom [eqna eqd eqc]]]].
        simpl. rewrite subst_empty. simpl; len.
        simpl. rewrite Nat.sub_0_r firstn_app_2. simpl.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        etransitivity.
        2:{ eapply ws_cumul_pb_eq_le. symmetry. now eapply red_ws_cumul_pb. }
        eapply ws_cumul_pb_Prod; eauto.
      + eapply ws_cumul_pb_Prod_Prod_inv in w as [eqna dom codom].
        assert (Σ ;;; Γ |- hd : ty).
        { eapply type_ws_cumul_pb; pcuic. eapply ws_cumul_pb_eq_le. now symmetry. }
        eapply (substitution0_ws_cumul_pb (t:=hd)) in codom; eauto.
        eapply typing_spine_strengthen in sp. 3:eauto.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        simpl. replace (#|Γ0| + 1 - S #|tl|) with (#|Γ0| - #|tl|) by lia.
        rewrite firstn_app. rewrite (firstn_0 _ (_ - _ - _)); try lia; rewrite app_nil_r.
        move: Hargs; simpl; rewrite Nat.add_1_r => hlen.
        specialize (X (subst_context [hd] 0 Γ0) ltac:(len; reflexivity) (subst [hd] #|Γ0| T) tl).
        forward X by now eapply assumption_context_fold.
        forward X.
        { eapply substitution_wf_local; eauto. constructor. constructor. now rewrite subst_empty.
          now rewrite app_context_assoc in wf. }
        specialize (X sp).
        forward X. len. apply nth_error_None. lia.
        rewrite subst_app_simpl.
        simpl. rewrite subst_it_mkProd_or_LetIn.
        simpl. len.
        len in X.
        rewrite firstn_length_le. lia.
        replace (#|Γ0| - #|tl| + #|tl|)%nat with #|Γ0| by lia.
        rewrite firstn_subst_context in X => //.
        eapply isType_apply; tea.
  Qed.

  Lemma assumption_context_firstn n Γ :
    assumption_context Γ ->
    assumption_context (firstn n Γ).
  Proof.
    induction n in Γ |- *; simpl; try constructor; auto.
    intros. destruct Γ; simpl; try constructor.
    depelim H. constructor. auto.
  Qed.

  Lemma typing_spine_nth_error_None_prod Γ Δ T args T' n decl :
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = None ->
    nth_error (List.rev Δ) n = Some decl ->
    ∑ na dom codom, Σ ;;; Γ ⊢ tProd na dom codom ≤ T'.
  Proof.
    intros ass wf sp nth nth'.
    eapply typing_spine_nth_error_None in sp; eauto;
    eapply nth_error_None in nth;
    eapply nth_error_Some_length in nth'; len in nth'.
    rewrite subst_it_mkProd_or_LetIn in sp.
    2:{ eapply nth_error_None. lia. }
    set (ctx := subst_context (List.rev args) 0 (firstn (#|Δ| - #|args|) Δ)) in *.
    assert (#|ctx| > 0).
    { rewrite /ctx; len. rewrite firstn_length_le; lia. }
    assert (assumption_context ctx).
    { rewrite /ctx. apply assumption_context_fold. now apply assumption_context_firstn. }
    destruct ctx using rev_case; simpl in *. lia.
    rewrite it_mkProd_or_LetIn_app in sp.
    move/assumption_context_app: H0 => [ass' assx].
    destruct x as [na [b|] ty]. exfalso. depelim assx.
    rewrite /mkProd_or_LetIn in sp.
    eexists _, _, _; eauto. eapply sp.
  Qed.

  Lemma wf_fixpoint_spine Γ mfix idx decl args ty :
    wf_fixpoint Σ Γ mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    typing_spine Σ Γ (dtype decl) args ty ->
    match nth_error args decl.(rarg) with
    | Some arg =>
      ∑ ind u indargs,
      (Σ ;;; Γ |- arg : mkApps (tInd ind u) indargs) *
      check_recursivity_kind (lookup_env Σ) (inductive_mind ind) Finite
    | None => ∑ na dom codom, Σ ;;; Γ ⊢ tProd na dom codom ≤ ty
    end.
  Proof.
    move=> [_ [_ hm]] nthe isty sp.
    destruct (mfix_on_ind_spine_witness _ _ _ _ _ _ hm nthe isty sp)
      as [mind' [tw [r cfix ck istw sp']]].
    clear sp isty. rename sp' into sp.
    destruct decl as [dna dty dbod rarg]; cbn in *.
    rewrite /check_one_fix /def_with_type /= in cfix.
    case E: (decompose_prod_assum [] tw) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst tw.
    destruct (nth_error _ rarg) eqn:Hnth => //.
    pose proof (nth_error_Some_length Hnth).
    len in H. simpl in H.
    eapply typing_spine_smash in sp.
    destruct (nth_error args rarg) eqn:hargs.
    - eapply typing_spine_nth_error in sp; eauto; cycle 1.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct istw as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * destruct (decompose_app (decl_type c)) as [hd tl] eqn:da.
        destruct (destInd hd) as [[i u]|] eqn:di => //.
        destruct i as [mind i]. noconf cfix.
        eapply decompose_app_inv in da. rewrite da in sp.
        rewrite subst_mkApps in sp.
        destruct hd => //; noconf di. simpl in sp.
        eexists _, ui, _; intuition eauto.
    - eapply typing_spine_nth_error_None_prod in sp; eauto.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct istw as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
  Qed.

  (** The declared type reduces to a telescope over an applied coinductive of the
      block. *)
  Lemma wf_cofixpoint_spine Γ mfix idx decl args ty :
    wf_cofixpoint Σ Γ mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    typing_spine Σ Γ (dtype decl) args ty ->
    ∑ Γ' T, (Σ ;;; Γ ⊢ dtype decl ⇝ it_mkProd_or_LetIn Γ' T) *
    ∑ ind u indargs, (T = mkApps (tInd ind u) indargs) *
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite *
    if #|args| <? context_assumptions Γ' then
      (Σ ;;; Γ ⊢ subst0 (List.rev args)
      (it_mkProd_or_LetIn (firstn (context_assumptions Γ' - #|args|) (smash_context [] Γ'))
        (expand_lets Γ' T)) ≤ ty)
    else
      (#|args| = context_assumptions Γ') *
      (Σ ;;; Γ ⊢ subst (List.rev args) 0 (expand_lets Γ' T) ≤ ty).
  Proof.
    move=> hm nthe isty sp.
    destruct (mfix_on_ind_spine_witness _ _ _ _ _ _ hm nthe isty sp)
      as [mind' [tw [r cfix ck istw sp']]].
    clear sp isty. rename sp' into sp. cbn in ck.
    rewrite /check_one_cofix /def_with_type /= in cfix.
    case E: (decompose_prod_assum [] tw) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst tw. exists Γ', concl. split; auto.
    destruct (decompose_app concl) as [hd tl] eqn:da.
    destruct (destInd hd) as [[mind i]|] eqn:di => //.
    destruct mind => //. destruct hd => //.
    noconf di. noconf cfix.
    eapply decompose_app_inv in da.
    eexists _, _, _; intuition eauto.
    destruct (Nat.ltb #|args| (context_assumptions Γ')) eqn:lt; [
      eapply Nat.ltb_lt in lt|eapply Nat.ltb_nlt in lt; destruct (Nat.eqb #|args| (context_assumptions Γ')) eqn:eq;
      [eapply Nat.eqb_eq in eq|eapply Nat.eqb_neq in eq]].
    - eapply typing_spine_smash in sp.
      destruct (nth_error args #|args|) eqn:hargs.
      { rewrite (proj2 (nth_error_None _ _)) // in hargs. }
      destruct (nth_error (List.rev (smash_context [] Γ')) #|args|) as [decl'|] eqn:hnth.
      eapply typing_spine_nth_error_None in sp; eauto.
      * len in sp.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct istw as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * len; simpl. eapply nth_error_None in hargs => //.
        eapply nth_error_None. lia.
      * eapply nth_error_None in hnth => //. len in hnth.
    - eapply typing_spine_all_inv in sp => //.
      subst concl.
      rewrite expand_lets_mkApps subst_mkApps /= in sp.
      destruct sp. split; auto.
      now rewrite expand_lets_mkApps subst_mkApps /=.
    - subst concl; eapply typing_spine_more_inv in sp; try lia.
  Qed.

End Spines.

Section CoFixCoind.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Lemma check_recursivity_kind_inj {mind rk rk'} :
    check_recursivity_kind (lookup_env Σ) mind rk ->
    check_recursivity_kind (lookup_env Σ) mind rk' -> rk = rk'.
  Proof.
    rewrite /check_recursivity_kind.
    case: lookup_env => //; case => // m.
    elim: ReflectEq.eqb_spec;
    elim: ReflectEq.eqb_spec; congruence.
  Qed.

  Lemma wt_closed_red_refl {Γ t T} : Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ t ⇝ t.
  Proof.
    intros Hs.
    eapply closed_red_refl.
    now eapply typing_wf_local, wf_local_closed_context in Hs.
    now eapply subject_is_open_term.
  Qed.

  Lemma invert_ind_ind Γ ind u args ind' u' args' :
    Σ;;; Γ |- mkApps (tInd ind u) args : mkApps (tInd ind' u') args' -> False.
  Proof.
    intros typ.
    eapply inversion_mkApps in typ as (?&?&?); auto.
    eapply inversion_Ind in t as (?&?&wfΓ&decl&cu&?); auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    eapply (typing_spine_ind_type_inv decl) in t0; tea.
    rewrite it_mkProd_or_LetIn_app !subst_instance_it_mkProd_or_LetIn in t0.
    eapply typing_spine_arity_mkApps_Ind in t0; eauto.
    eapply typing_spine_isType_dom in t0 as (_ & s & Hs & _).
    eexists; split; [sq|]. now eapply wt_closed_red_refl.
    now do 2 eapply isArity_it_mkProd_or_LetIn.
    now eapply isTypeRel_isType, (declared_inductive_valid_type decl).
  Qed.

  Lemma invert_fix_ind Γ mfix i args ind u args' :
    match unfold_fix mfix i with
    | Some (rarg, _) => nth_error args rarg = None
    | _ => True
    end ->
    Σ;;; Γ |- mkApps (tFix mfix i) args : mkApps (tInd ind u) args' -> False.
  Proof.
    intros no_arg typ.
    eapply inversion_mkApps in typ as (?&?&?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    unfold unfold_fix in no_arg.
    rewrite e in no_arg.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite no_arg in t0. destruct t0 as [na [dom [codom cum]]].
    eapply ws_cumul_pb_Prod_l_inv in cum as (? & ? & ? & []).
    eapply invert_red_mkApps_tInd in c as [? [eq _]]; auto.
    solve_discr.
  Qed.

  Lemma typing_cofix_coind {Γ mfix idx args ind u indargs} :
    Σ ;;; Γ |- mkApps (tCoFix mfix idx) args : mkApps (tInd ind u) indargs ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.
  Proof.
    intros tyarg.
    eapply inversion_mkApps in tyarg as [A [Hcof sp]]; auto.
    eapply inversion_CoFix in Hcof as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto.
    simpl in a.
    apply isTypeRel_isType in a.
    eapply typing_spine_strengthen in sp; eauto.
    eapply wf_cofixpoint_spine in sp as (Γ' & concl & _ & ?); eauto.
    move: s => [ind' [u' [indargs' [[ceq ccum] ck]]]].
    subst concl.  move: ck.
    elim: Nat.ltb_spec => Hargs.
    - rewrite subst_it_mkProd_or_LetIn; len.
      set (ctx := subst_context _ _ _).
      assert(assumption_context ctx).
      eapply assumption_context_fold, assumption_context_firstn, smash_context_assumption_context; constructor.
      assert (#|ctx| > 0).
      { rewrite /ctx; len; rewrite firstn_length_le. len; lia. lia. }
      destruct ctx as [|ctx [na [b|] ty]] using rev_case. simpl in H0; lia.
      exfalso; move/assumption_context_app: H => [ass assd]; depelim assd.
      move/assumption_context_app: H => [ass assd]; depelim assd.
      rewrite it_mkProd_or_LetIn_app /mkProd_or_LetIn /= => cum.
      now eapply invert_cumul_prod_ind in cum.
    - move=> [hargs ccum'].
      rewrite expand_lets_mkApps subst_mkApps /= in ccum'.
      eapply invert_cumul_ind_ind in ccum' as ((hind & r) & _).
      len in r. eapply ReflectEq.eqb_eq in hind. now subst ind'.
  Qed.

End CoFixCoind.
