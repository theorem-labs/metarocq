(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion PCUICViews
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICFixWitness PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity.

Local Existing Instance config.extraction_checker_flags.

From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation_Properties.

Set Default Proof Using "Type*".

Lemma negb_False (p : bool) : negb p -> p -> False.
Proof.
intros n pos. rewrite pos in n => //.
Qed.

(* Arities*)


Ltac destruct_sigma H :=
  repeat match type of H with
  | @sigT _ (fun x => _) => let v := fresh x in
    destruct H as (v & H); simpl in H
  | (_ × _)%type => destruct H as (? & H); simpl in H
  end.

Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args using rev_ind; simpl => //.
  - now rewrite andb_true_r.
  - now rewrite mkApps_app /= IHargs forallb_app andb_assoc /= andb_true_r.
Qed.



    Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} :
      on_free_vars P (it_mkProd_or_LetIn Δ t) =
      on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
  Proof.
    move: P. induction Δ using rev_ind => P.
    - cbn. now rewrite shiftnP0.
    - destruct x as [na [b|] ty]; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
        /on_free_vars_decl /test_decl /=. ring.
      rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
      /on_free_vars_decl /test_decl /=. ring.
  Qed.




(** Evaluation is a subrelation of reduction: *)

Tactic Notation "redt" uconstr(y) := eapply (CRelationClasses.transitivity (R:=red _ _) (y:=y)).

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

Fixpoint axiom_free_value Σ args t :=
  match t with
  | tApp hd arg => axiom_free_value Σ (axiom_free_value Σ [] arg :: args) hd
  | tConst kn _ => match lookup_env Σ kn with
                   | Some (ConstantDecl {| cst_body := None |}) => false
                   | _ => true
                   end
  | tCase _ _ discr _ => axiom_free_value Σ [] discr
  | tProj _ t => axiom_free_value Σ [] t
  | tFix defs i =>
    match nth_error defs i with
    | Some def => nth (rarg def) args true
    | None => true
    end
  | _ => true
  end.

Lemma axiom_free_axiom_free_value Σ t :
  axiom_free Σ ->
  axiom_free_value Σ [] t.
Proof.
  intros axfree.
  cut (Forall is_true []); [|constructor].
  generalize ([] : list bool).
  induction t using term_forall_list_ind; intros axfree_args all_true; cbn; auto.
  - destruct lookup_env eqn:find; auto.
    destruct g; auto.
    destruct c; auto.
    apply declared_constant_from_gen in find.
    apply axfree in find; cbn in *.
    now destruct cst_body0.
  - destruct nth_error; auto.
    rewrite nth_nth_error.
    destruct nth_error eqn:nth; auto.
    eapply nth_error_forall in nth; eauto.
Qed.

Section classification.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Notation wh_neutral := (whne RedFlags.default).
  Notation wh_normal := (whnf RedFlags.default).

  Transparent construct_cofix_discr.

  Lemma value_whnf t : closed t -> value Σ t -> wh_normal Σ [] t.
  Proof.
    intros cl ev.
    induction ev in cl |- * using value_values_ind.
    destruct t; simpl in H; try discriminate; try solve [constructor; constructor].
    - eapply (whnf_indapp _ _ [] _ _ []).
    - eapply (whnf_cstrapp _ _ [] _ _ _ []).
    - eapply (whnf_fixapp _ _ [] _ _ []).
      destruct nth_error as [rarg|] => /= //; [|easy].
      left ; eexists; split; eauto.
      now rewrite nth_error_nil.
    - eapply (whnf_cofixapp _ _ [] _ _ []).
    - eapply whnf_prim.
    - destruct X => //.
      pose proof cl as cl'.
      rewrite closedn_mkApps in cl'. move/andP: cl' => [clfix _].
      rewrite -closed_unfold_fix_cunfold_eq in e => //.
      rewrite /unfold_fix in e.
      destruct nth_error eqn:nth => //. noconf e.
      eapply whnf_fixapp. rewrite nth. left; eexists; split; eauto.
      now eapply nth_error_None.
  Qed.

  Lemma eval_whne t t' : closed t -> eval Σ t t' -> wh_normal Σ [] t'.
  Proof.
    intros cl ev.
    pose proof (eval_closed Σ _ _ cl ev).
    eapply eval_to_value in ev.
    now eapply value_whnf.
  Qed.

  Lemma typing_var {Γ n ty} : Σ ;;; Γ |- (tVar n) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Lemma typing_evar {Γ n l ty} : Σ ;;; Γ |- (tEvar n l) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.




  Lemma axiom_free_value_mkApps Σ' args hd args' :
    axiom_free_value Σ' args (mkApps hd args') =
    axiom_free_value Σ' (map (axiom_free_value Σ' []) args' ++ args) hd.
  Proof.
    revert hd args.
    induction args' using MRList.rev_ind; intros hd args; cbn; auto.
    rewrite mkApps_app /=.
    rewrite IHargs'.
    now rewrite map_app /= -app_assoc.
  Qed.

  Lemma wh_neutral_empty_gen Γ free t ty :
    axiom_free_value Σ free t ->
    wh_neutral Σ [] t ->
    Σ ;;; Γ |- t : ty ->
    Γ = [] ->
    False.
  Proof.
    intros axfree ne typed.
    induction ne in free, t, ty, axfree, ne, typed |- *; intros ->; simpl in *; try discriminate.
    - apply inversion_Rel in typed as (?&?&?&?); auto.
      rewrite nth_error_nil in e0; discriminate.
    - now eapply typing_var in typed.
    - now eapply typing_evar in typed.
    - apply inversion_Const in typed as [decl' [wfd [declc [cu cum]]]]; eauto.
      unshelve eapply declared_constant_to_gen in declc; eauto.
      red in declc. rewrite declc in e, axfree.
      noconf e.
      destruct decl; cbn in *.
      rewrite e0 in axfree; congruence.
    - eapply inversion_App in typed as [na [A [B [Hf _]]]]; eauto.
    - eapply inversion_mkApps in typed as (? & ? & ?); eauto.
      eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
      eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
      eapply typing_spine_strengthen in t0; eauto.
      rewrite /unfold_fix in e. rewrite e1 in e. noconf e.
      eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
      rewrite e0 in t0. destruct t0 as [ind [u [indargs [tyarg ckind]]]].
      rewrite axiom_free_value_mkApps in axfree.
      cbn in axfree.
      rewrite e1 nth_nth_error nth_error_app1 in axfree.
      1: { rewrite length_map.
           apply nth_error_Some_length in e0; auto. }
      rewrite nth_error_map e0 in axfree.
      cbn in axfree.
      eauto.
    - eapply inversion_Case in typed as (? & ? & ? & ? & [] & ?); tas; eauto.
    - eapply inversion_Proj in typed as (? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
  Qed.

  Lemma wh_neutral_empty t ty :
    axiom_free_value Σ [] t ->
    wh_neutral Σ [] t ->
    Σ ;;; [] |- t : ty ->
    False.
  Proof. eauto using wh_neutral_empty_gen. Qed.

  Lemma whnf_classification' t i u args :
    axiom_free_value Σ [] t ->
    wh_normal Σ [] t ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t).
  Proof.
    intros axfree ne typed.
    pose proof (subject_closed typed) as cl.
    depelim ne; simpl in *.
    - exfalso. eauto using wh_neutral_empty.
    - eapply inversion_Sort in typed as (? & ? & e); auto.
      now eapply invert_cumul_sort_ind in e.
    - eapply inversion_Prod in typed as (? & ? & ? & ? & e); auto.
      now eapply invert_cumul_sort_ind in e.
    - eapply inversion_Lambda in typed as (? & ? & ? & e); auto.
      now eapply invert_cumul_prod_ind in e.
    - now rewrite head_mkApps /= /head /=.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct nth_error; [|easy].
      destruct o as [[? [? ?]]|]; [|easy]. inversion H; eauto.
    - now rewrite head_mkApps /head /=.
    - eapply inversion_Prim in typed as [prim_ty [cdecl [? ? ? ? hp]]]; eauto.
      destruct p as [? []]; simp prim_type in w.
      1-3:eapply (invert_cumul_axiom_ind (args := [])) in w; eauto; destruct p0 as [? []]; eauto.
      eapply (invert_cumul_axiom_ind (args := [array_type a0])) in w; eauto. destruct p0 as [s []]; eauto.
  Qed.

  Lemma whnf_classification t i u args :
    axiom_free Σ ->
    wh_normal Σ [] t ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t).
  Proof.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply whnf_classification'; eauto.
  Qed.

  Definition notCoInductive Σ ind :=
    ~check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.

  Lemma ind_whnf_classification' t ind u indargs :
    axiom_free_value Σ [] t -> notCoInductive Σ ind ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t.
  Proof.
    intros axfree ck typed whnf.
    rewrite /isConstruct_app.
    eapply whnf_classification' in whnf; eauto.
    rewrite /head in whnf.
    destruct (decompose_app t) as [hd tl] eqn:da; simpl in *.
    destruct hd eqn:eqh => //. subst hd.
    eapply decompose_app_inv in da. subst.
    eapply typing_cofix_coind in typed.
    congruence.
  Qed.

  Lemma ind_whnf_classification t ind u indargs :
    axiom_free Σ -> notCoInductive Σ ind ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t.
  Proof.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply ind_whnf_classification'; eauto.
  Qed.

  Lemma fix_app_is_constructor {mfix idx args ty narg fn} :
    Σ;;; [] |- mkApps (tFix mfix idx) args : ty ->
    unfold_fix mfix idx = Some (narg, fn) ->
    match nth_error args narg return Type with
    | Some a => axiom_free_value Σ [] a -> wh_normal Σ [] a -> isConstruct_app a
    | None => ∑ na dom codom, Σ ;;; [] ⊢ tProd na dom codom ≤ ty
    end.
  Proof.
    intros typed unf.
    eapply inversion_mkApps in typed as (? & ? & ?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
    eapply typing_spine_strengthen in t0; eauto.
    rewrite /unfold_fix in unf. rewrite e in unf.
    noconf unf.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite /is_constructor. destruct (nth_error args (rarg x0)) eqn:hnth; [|assumption].
    destruct_sigma t0.
    intros axfree norm.
    eapply ind_whnf_classification' in t1; eauto.
    intros chk.
    pose proof (check_recursivity_kind_inj chk t0).
    discriminate.
  Qed.


  Lemma value_axiom_free Σ' t :
    value Σ' t ->
    axiom_free_value Σ' [] t.
  Proof.
    intros val.
    induction val using value_values_ind.
    - destruct t; try discriminate; auto.
      cbn.
      destruct ?; auto.
      destruct ?; auto.
    - cbn. constructor.
    - rewrite axiom_free_value_mkApps.
      rewrite app_nil_r.
      destruct X; try constructor.
      cbn.
      unfold isStuckFix, cunfold_fix in e.
      destruct nth_error; auto.
      rewrite nth_overflow; auto. len. now noconf e.
  Qed.

  (** Evaluation on well-typed terms corresponds to reduction.
      It differs in two ways from standard reduction:
      - using closed substitution operations applicable only on closed terms
      - it does not check that fixpoints that are applied to enough arguments
        have a constructor at their recursive argument as it is ensured by typing
        + classification. *)

  Import PCUICGlobalEnv.

  Lemma wcbveval_red t ty u :
    Σ ;;; [] |- t : ty ->
    eval Σ t u -> red Σ [] t u.
  Proof.
    intros Hc He.
    revert ty Hc.
    induction He; simpl; move=> ty Ht;
      try solve[econstructor; eauto].

    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      redt (tApp (tLambda na t b) a); eauto.
      eapply red_app; eauto.
      redt (tApp (tLambda na t b) a'). eapply red_app; eauto.
      specialize (IHHe1 _ t0). specialize (IHHe2 _ t1).
      redt (csubst a' 0 b).
      rewrite (closed_subst a' 0 b).
      eapply eval_closed; eauto. now eapply subject_closed in t1.
      eapply red1_red. constructor.
      pose proof (subject_closed t1); auto.
      eapply eval_closed in H; eauto.
      eapply subject_reduction in IHHe1. 2-3:eauto.
      eapply inversion_Lambda in IHHe1 as (? & ? & ? & e); eauto.
      eapply (substitution0 (Γ := [])) in t2; eauto.
      eapply IHHe3.
      rewrite (closed_subst a' 0 b); auto.
      rewrite /subst1 in t2. eapply t2.
      eapply (type_ws_cumul_pb (pb:=Conv)); eauto.
      eapply subject_reduction in IHHe2; eauto.
      now eapply isTypeRel_isType.
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna dom codom]; eauto.
      now symmetry.

    - eapply inversion_LetIn in Ht as (? & ? & ? & ?); auto.
      apply unlift_TermTyp in l as t0'.
      redt (tLetIn na b0' t b1); eauto.
      eapply red_letin; eauto.
      redt (b1 {0 := b0'}); auto.
      do 2 econstructor.
      specialize (IHHe1 _ t0').
      rewrite /subst1.
      rewrite -(closed_subst b0' 0 b1).
      eapply subject_reduction in t0'; eauto. eapply subject_closed in t0'; eauto.
      eapply IHHe2.
      rewrite closed_subst.
      eapply subject_reduction in t0'; eauto. eapply subject_closed in t0'; eauto.
      pose proof (subject_is_open_term t0).
      eapply substitution_let in t0; eauto.
      eapply subject_reduction in t0.
      3:{ eapply (red_red (Δ := [vass na t]) (Γ' := [])); eauto. 3:repeat constructor.
          cbn. rewrite addnP_shiftnP. eapply type_is_open_term in t0'. now erewrite t0'.
          repeat constructor. cbn. rewrite addnP_shiftnP.
          eapply subject_is_open_term in t0'. cbn in t0'. now setoid_rewrite shiftnP0 in t0'. }
      apply t0. auto.

    - redt (subst_instance u body); auto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.
      eapply IHHe. eapply subject_reduction; eauto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Case in Ht; auto. destruct_sigma Ht.
      unshelve epose proof (isdecl_ := declared_inductive_to_gen isdecl); eauto.
      destruct (declared_inductive_inj d isdecl_); subst mdecl0 idecl0.
      destruct c0.
      specialize (IHHe1 _ scrut_ty).
      assert (red Σ [] (tCase ci p discr brs) (iota_red ci.(ci_npar) p args br)).
      { clear X. redt _.
        eapply red_case; eauto.
        eapply All2_refl; intros; eauto. red.
        eapply All2_refl; split; reflexivity.
        eapply red1_red. destruct p => /= //.
        eapply red_iota; tea.
        rewrite e1 /cstr_arity eq_npars e3 //. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Proj in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      assert (red Σ [] (tProj p discr) a).
      { redt _.
        eapply red_proj_c; eauto.
        eapply red1_red; constructor; auto. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_App in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      epose proof (subject_reduction Σ [] _ _ _ wfΣ t IHHe1) as Ht2.
      epose proof (subject_reduction Σ [] _ _ _ wfΣ t0 IHHe2) as Ha2.
      assert (red Σ [] (tApp f4 a) (tApp (mkApps fn argsv) av)).
      { redt _.
        eapply red_app; eauto.
        rewrite -![tApp _ _](mkApps_app _ _ [_]).
        eapply red1_red.
        rewrite -closed_unfold_fix_cunfold_eq in e1.
        { eapply subject_closed in Ht2; auto.
          rewrite closedn_mkApps in Ht2. now move/andP: Ht2 => [clf _]. }
        eapply red_fix; eauto.
        assert (Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : B {0 := av}).
        { rewrite mkApps_app /=. eapply type_App'; eauto. }
        epose proof (fix_app_is_constructor X0 e1); eauto.
        rewrite /is_constructor.
        destruct nth_error eqn:hnth => //.
        2:{ eapply nth_error_None in hnth. len in hnth. }
        assert (All (closedn 0) (argsv ++ [av])).
        { eapply subject_closed in X0; eauto.
          rewrite closedn_mkApps in X0.
          move/andP: X0 => [clfix clargs].
          now eapply forallb_All in clargs. }
        assert (All (value Σ) (argsv ++ [av])).
        { eapply All_app_inv; [|constructor; [|constructor]].
          eapply eval_to_value in He1.
          eapply value_mkApps_inv in He1 as [[-> Hat]|[vh vargs]] => //.
          now eapply eval_to_value in He2. }
        solve_all.
        eapply nth_error_all in X3; eauto. simpl in X3.
        destruct X3 as [cl val]. eapply X1, value_whnf; auto.
        now eapply value_axiom_free. }
      redt _; eauto.

    - apply inversion_App in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      now eapply red_app.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Case in Ht; auto; destruct_sigma Ht.
      destruct c.
      specialize (IHHe1 _ scrut_ty).
      unshelve epose proof (subject_reduction Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closed X0).
      etransitivity. eapply red_case_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)).
      { eapply red1_red. eapply red_cofix_case.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
      redt _; eauto.
      eapply IHHe2.
      eapply subject_reduction. 3: eapply X1. eauto.
      eapply subject_reduction. 3: eapply red_case_c; eauto. all:eauto.
    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Proj in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      unshelve epose proof (subject_reduction Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closed X0).
      etransitivity. eapply red_proj_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))).
      { eapply red1_red. eapply red_cofix_proj.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
        redt _; eauto.
      eapply IHHe2.
      eapply subject_reduction. 3: eapply X1. eauto.
      eapply subject_reduction. 3: eapply red_proj_c; eauto. all:eauto.

    - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      rewrite mkApps_app /=. now eapply red_app.

    - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      now eapply red_app.

    - eapply inversion_Prim in Ht as [prim_type [decl []]]; eauto.
      depelim X. 1-3:reflexivity.
      depelim p1. specialize (r _ hdef).
      eapply red_primArray_congr; eauto.
      eapply All2_undep in a. solve_all.
  Qed.

  Theorem subject_reduction_eval {t u T} :
    Σ ;;; [] |- t : T -> eval Σ t u -> Σ ;;; [] |- u : T.
  Proof.
    intros Hty Hred.
    eapply wcbveval_red in Hred; eauto. eapply subject_reduction; eauto.
  Qed.

  Lemma value_classification {t i u args} :
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    value Σ t ->
    construct_cofix_discr (head t).
  Proof.
    intros Ht Hvalue.
    eapply value_axiom_free in Hvalue as H.
    eapply whnf_classification'; eauto.
    eapply eval_whne.
    2: eapply value_final; eauto.
    eapply @subject_closed with (Γ := []); eauto.
  Qed.

  Lemma eval_classification {t i u args} :
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    forall t', eval Σ t t' ->
    construct_cofix_discr (head t').
  Proof.
    intros Ht t' eval.
    pose proof (subject_closed Ht).
    eapply subject_reduction in Ht. 3:eapply wcbveval_red; eauto. 2:auto.
    eapply eval_to_value in eval as axfree.
    eapply value_axiom_free in axfree.
    eapply eval_whne in eval; auto.
    eapply whnf_classification'; eauto.
  Qed.

End classification.

(* Print Assumptions eval_ind_canonical. *)
