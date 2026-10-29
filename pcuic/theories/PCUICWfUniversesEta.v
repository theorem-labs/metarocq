(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICSigmaCalculus PCUICTyping PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICReduction PCUICCumulativity PCUICUnivSubst PCUICUnivSubstitutionConv PCUICSubstitution PCUICWfUniverses
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICWeakeningEnvTypEta
     PCUICUnivSubstitutionTypEta PCUICTypingEtaNotions.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

(** * Well-formed universes of terms typed in [typingE]

  The E copy of [PCUICWfUniverses]. Each lemma of the base file that mentions
  typing, cumulativity, [wf_local] or [wf] is copied, and its statement is the
  base statement with only the relations renamed: [typing] → [typingE],
  [cumulSpec0] → [cumulSpecE0], [wf] → [wfE], [env_prop] → [env_propE],
  [isType] → [isTypeE] ([PCUICTypingEtaNotions]).

  Copied (the E name is the base name with the suffix [E]):
  [wf_universe_subst_instance_univE], [wf_sort_subst_instance_sortE],
  [wf_sort_instantiateE], [wf_level_monoE], [wf_instance_subst_instanceE],
  [wf_universes_instE], [weaken_wf_universeE], [weaken_wf_levelE],
  [weaken_wf_instanceE], [weaken_wf_universesE], [wf_universes_weaken_fullE],
  [wf_universes_weakenE], [wf_level_closedE], [wf_universe_closedE],
  [wf_sort_closedE], [wf_instance_closedE], [wf_universes_closeduE],
  [wf_ctx_universes_closedE], [closed_ind_predicate_contextE], [closedu_indsE],
  [wf_typesE], [typing_wf_universesE], [typing_wf_sortE],
  [isType_wf_universesE], and the [Hint Extern] that proves [wf_sort] from a
  typing of the sort (over [typingE]).

  Not copied: every other declaration of the base file ([wf_sort_type0],
  [wf_sort_type1], [wf_sort_super], [wf_sort_sup], [wf_sort_product],
  [wf_level], [wf_instance], [wf_universes], [wf_sortb], their reflections,
  [on_universes_lift], [wf_universes_subst], [type_local_ctx_wf],
  [consistent_instance_ext_wf], [wf_universes_local_ctx_nth_error],
  [wf_abstract_instance], the [closedu] lemmas, and the rest): none of them
  mentions typing, cumulativity, [wf_local] or [wf]; they are used from the base
  file. The local tactics [to_prop], [to_wfu], [specIH] and the local notation
  [closedu_ctx] of the base section are restated here. *)

Section CheckerFlags.
  Context {cf:checker_flags}.

  Hint Resolve wf_sort_type1 wf_sort_super wf_sort_sup wf_sort_product : pcuic.
  Hint Rewrite test_context_mapi : map.
  Arguments wf_universe_reflect {Σ u}.

  Ltac to_prop :=
    repeat match goal with
    | [ H: is_true (?x && ?y) |- _ ] =>
     let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
    end.

  Ltac to_wfu :=
    repeat match goal with
    | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (elimT (@wf_universe_reflect _ x)) in H
    | [ |- is_true (wf_universeb _ ?x) ] => apply (introT (@wf_universe_reflect _ x))
    | [ H: is_true (Sort.on_sort (wf_universeb _) _ ?x) |- _ ] => apply (elimT (@wf_sort_reflect _ x)) in H
    | [ |- is_true (Sort.on_sort (wf_universeb _) _ ?x) ] => apply (introT (@wf_sort_reflect _ x))
    | [ H: is_true (wf_sortb _ ?x) |- _ ] => apply (elimT (@wf_sort_reflect _ x)) in H
    | [ |- is_true (wf_sortb _ ?x) ] => apply (introT (@wf_sort_reflect _ x))
    end.

  Lemma wf_universe_subst_instance_univE (Σ : global_env_ext) univs ui u :
    wfE Σ ->
    wf_universe Σ u ->
    wf_instance (Σ.1, univs) ui ->
    wf_universe (Σ.1, univs) (subst_instance ui u).
  Proof using Type.
    intros wfΣ Hl Hu e [[l n] [inl ->]]%In_subst_instance.
    destruct l as [|s|n']; simpl; auto.
    - apply global_ext_levels_InSet.
    - specialize (Hl (Level.level s, n) inl).
      simpl in Hl.
      apply monomorphic_level_in_global_ext in Hl.
      eapply LS.union_spec. now right.
    - specialize (Hl (Level.lvar n', n) inl).
      eapply LS.union_spec in Hl as [Hl|Hl].
      + red in Hu.
        unfold levels_of_udecl in Hl.
        destruct Σ.2.
        * simpl in Hu. simpl in *.
          unfold subst_instance; simpl.
          destruct nth_error eqn:hnth; simpl.
          eapply nth_error_forall in Hu; eauto.
          apply global_ext_levels_InSet.
        * unfold subst_instance. simpl.
          destruct (nth_error ui n') eqn:hnth.
          2:{ simpl. rewrite hnth. apply global_ext_levels_InSet. }
          eapply nth_error_forall in Hu. 2:eauto.
          change (nth_error ui n') with (nth_error ui n') in *.
          rewrite -> hnth. simpl. apply Hu.
      + now apply not_var_global_levelsE in Hl.
  Qed.

  Lemma wf_sort_subst_instance_sortE (Σ : global_env_ext) univs u s :
    wfE Σ ->
    wf_sort Σ s ->
    wf_instance (Σ.1, univs) u ->
    wf_sort (Σ.1, univs) (subst_instance u s).
  Proof using Type.
    destruct s as [| |t]; cbnr.
    apply wf_universe_subst_instance_univE.
  Qed.

  Lemma wf_sort_instantiateE Σ univs s u φ :
    wfE Σ ->
    wf_sort (Σ, univs) s ->
    wf_instance (Σ, φ) u ->
    wf_sort (Σ, φ) (subst_instance_sort u s).
  Proof using Type.
    intros wfΣ Hs.
    apply (wf_sort_subst_instance_sortE (Σ, univs) φ); auto.
  Qed.

  Lemma wf_level_monoE Σ u :
    wfE Σ ->
    on_udecl_prop Σ (Monomorphic_ctx) ->
    Forall (wf_level (Σ, Monomorphic_ctx)) u ->
    forallb (fun x => ~~ Level.is_var x) u.
  Proof using Type.
    intros wf uprop.
    induction 1 => /= //.
    destruct x eqn:isv => /= //.
    apply LS.union_spec in H as [H|H]; simpl in H.
    epose proof (@udecl_prop_in_var_poly _ (Σ, _) _ uprop H) as [ctx' eq].
    discriminate.
    now pose proof (not_var_global_levelsE wf _ H).
  Qed.

  Lemma wf_instance_subst_instanceE Σ univs u u' φ :
    wfE Σ ->
    on_udecl_prop Σ univs ->
    wf_instance (Σ, univs) u' ->
    wf_instance (Σ, φ) u ->
    wf_instance (Σ, φ) (subst_instance u u').
  Proof using Type.
    intros wfΣ onup Hs cu.
    destruct univs.
    - red in Hs |- *.
      unshelve epose proof (wf_level_monoE _ _ _ _ Hs); eauto.
      eapply forallb_Forall in H. apply Forall_map.
      solve_all. destruct x; simpl => //.
      red. apply global_ext_levels_InSet.
      eapply wf_level_sub; eauto.
    - clear onup.
      red in Hs |- *.
      eapply Forall_map, Forall_impl; eauto.
      intros x wfx.
      red in wfx. destruct x => /= //.
      { red. apply global_ext_levels_InSet. }
      eapply In_Level_global_ext_poly in wfx.
      apply LS.union_spec; now right.
      eapply in_var_global_extE in wfx; simpl in wfx; auto.
      unfold AUContext.levels, AUContext.repr in wfx.
      destruct cst as [? cst].
      rewrite mapi_unfold in wfx.
      eapply (proj1 (LevelSetProp.of_list_1 _ _)) in wfx.
      apply SetoidList.InA_alt in wfx as [? [<- wfx]]. simpl in wfx.
      eapply In_unfold_inj in wfx; [|congruence].
      destruct (nth_in_or_default n u (Level.lzero)).
      red in cu. eapply Forall_In in cu; eauto. rewrite e.
      red. apply global_ext_levels_InSet.
  Qed.

  Lemma wf_universes_instE {Σ : global_env_ext} univs t u :
    wfE Σ ->
    on_udecl_prop Σ.1 univs ->
    wf_instance Σ u  ->
    wf_universes (Σ.1, univs) t ->
    wf_universes Σ (subst_instance u t).
  Proof using Type.
    intros wfΣ onudecl cu wft.
    induction t using term_forall_list_ind; simpl in *; auto; try to_prop;
      try apply /andP; intuition eauto 4.

    all:cbn -[Universe.make'] in * ; to_wfu; autorewrite with map; repeat (f_equal; solve_all).

    - destruct Σ as [Σ univs']. simpl in *.
      eapply (wf_sort_subst_instance_sortE (Σ, univs)); auto.

    - apply forallb_All.
      rewrite -forallb_map wf_universeb_instance_forall.
      apply All_forallb in wft.
      rewrite -forallb_map wf_universeb_instance_forall in wft.
      apply/wf_instanceP.
      eapply wf_instance_subst_instanceE; eauto.
      destruct Σ; simpl in *.
      now move/wf_instanceP: wft.
    - apply forallb_All.
      rewrite -forallb_map wf_universeb_instance_forall.
      apply All_forallb in wft.
      rewrite -forallb_map wf_universeb_instance_forall in wft.
      apply/wf_instanceP.
      eapply wf_instance_subst_instanceE; eauto.
      destruct Σ; simpl in *.
      now move/wf_instanceP: wft.
    - apply forallb_All.
      rewrite -forallb_map wf_universeb_instance_forall.
      apply All_forallb in wft.
      rewrite -forallb_map wf_universeb_instance_forall in wft.
      apply/wf_instanceP.
      eapply wf_instance_subst_instanceE; eauto.
      destruct Σ; simpl in *.
      now move/wf_instanceP: wft.

    - apply forallb_All.
      rewrite -forallb_map wf_universeb_instance_forall.
      apply All_forallb in H.
      rewrite -forallb_map wf_universeb_instance_forall in H.
      apply/wf_instanceP.
      eapply wf_instance_subst_instanceE; eauto.
      destruct Σ ; simpl in *.
      now move/wf_instanceP: H.

    - now len.
    - rewrite /test_branch. rtoProp.
      move/andP: a => [] tctx wfu.
      split; auto. simpl.
      solve_all. now len.
    - rewrite -subst_instance_universe_make. to_wfu.
      eapply (wf_universe_subst_instance_univE (Σ.1, univs)) => //.
  Qed.

  Lemma weaken_wf_universeE Σ Σ' t : wfE Σ' -> extends Σ.1 Σ' ->
    wf_universe Σ t ->
    wf_universe (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ ext.
    intros Hl l inl; specialize (Hl l inl).
    apply LS.union_spec. apply LS.union_spec in Hl as [Hl|Hl]; simpl.
    left; auto.
    right. now eapply global_levels_sub; [apply ext|].
  Qed.

  Lemma weaken_wf_levelE {Σ : global_env_ext} Σ' t : wfE Σ -> wfE Σ' -> extends Σ Σ' ->
    wf_level Σ t ->
    wf_level (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    unfold wf_level.
    destruct t; simpl; auto using global_ext_levels_InSet;
    intros; apply LS.union_spec.
    - eapply LS.union_spec in H as [H|H].
      left; auto.
      right; auto. simpl.
      eapply global_levels_sub. apply ext. apply H.
    - cbn. eapply in_var_global_extE in H; eauto.
  Qed.

  Lemma weaken_wf_instanceE {Σ : global_env_ext} Σ' t : wfE Σ -> wfE Σ' -> extends Σ.1 Σ' ->
    wf_instance Σ t ->
    wf_instance (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    unfold wf_instance.
    intros H; eapply Forall_impl; eauto.
    intros. now eapply weaken_wf_levelE.
  Qed.

  Arguments Universe.make' : simpl never.

  Lemma weaken_wf_universesE {Σ : global_env_ext} Σ' t : wfE Σ -> wfE Σ' -> extends Σ.1 Σ' ->
    wf_universes Σ t ->
    wf_universes (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    induction t using term_forall_list_ind; cbn in *; auto; intros; to_prop;
    try apply /andP; to_wfu; intuition eauto 4.

  - solve_all.
  - move: H. destruct s => //=.
    now apply weaken_wf_universeE.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_universe_reflect /weaken_wf_universeE /wf_universe_reflect.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_universe_reflect /weaken_wf_universeE /wf_universe_reflect.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_universe_reflect /weaken_wf_universeE /wf_universe_reflect.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_universe_reflect /weaken_wf_universeE /wf_universe_reflect.
  - red in X.
    solve_all.
    rewrite /test_branch in b |- *.
    rtoProp.
    intuition.
  - red in X; solve_all.
  - red in X. solve_all.
  - eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
    intros; to_wfu; now eapply weaken_wf_universeE.
  Qed.

  Lemma wf_universes_weaken_fullE :
    weaken_env_prop_full cumulSpecE0 (lift_typing typingE)
      (fun Σ _ t T => wf_universes Σ t && wf_universes Σ T).
  Proof using Type.
    do 2 red. intros.
    to_prop; apply /andP; split; now apply weaken_wf_universesE.
  Qed.

  Lemma wf_universes_weakenE :
    weaken_env_prop cumulSpecE0 (lift_typing typingE)
      (fun Σ _ j => option_default (wf_universes Σ) (j_term j) true && wf_universes Σ (j_typ j) && option_default (wf_sortb Σ) (j_univ j) true).
  Proof using Type.
    intros Σ Σ' φ wfΣ wfΣ' Hext _ j Hj.
    pose proof (fun t => @weaken_wf_universesE (Σ, φ) Σ' t wfΣ wfΣ' Hext).
    rtoProp; repeat split; auto.
    1: destruct j_term => //; cbn in *; auto.
    1: destruct j_univ => //; cbn in *; now apply (H (tSort _)).
  Qed.

  Ltac specIH :=
    repeat match goal with
    | [ H : on_udecl _ _, H' : on_udecl _ _ -> _ |- _ ] => specialize (H' H)
    end.

  Notation closedu_ctx k := (test_context (closedu k)).

  Lemma wf_level_closedE {Σ : global_env} {wfΣ : wfE Σ} univs l :
    on_udecl_prop Σ univs ->
    wf_level (Σ, univs) l -> closedu_level #|polymorphic_instance univs| l.
  Proof using Type.
    intros ond Ht; destruct l => //.
    cbn in Ht. unfold closedu_level.
    cbn. red in Ht.
    eapply in_var_global_extE in Ht => //.
    cbn in Ht.
    destruct (udecl_prop_in_var_poly (Σ := (Σ, univs)) ond Ht) as [ctx eq].
    cbn in eq. subst univs.
    cbn in Ht. cbn. unfold AUContext.levels in Ht.
    eapply (proj1 (LevelSetProp.of_list_1 _ _)) in Ht.
    eapply InA_In_eq in Ht.
    destruct ctx as [names cstrs].
    unfold AUContext.repr in Ht |- *. cbn in *. len.
    rewrite mapi_unfold in Ht. eapply In_unfold_var in Ht as [k []].
    eapply Nat.leb_le. noconf H0. lia.
  Qed.

  Lemma wf_universe_closedE {Σ : global_env} {wfΣ : wfE Σ} univs u :
    on_udecl_prop Σ univs ->
    wf_universe (Σ, univs) u -> closedu_universe #|polymorphic_instance univs| u.
  Proof using Type.
    intros ond Ht.
    cbn in Ht. unfold closedu_universe.
    eapply LevelExprSet.for_all_spec.
    intros x y ?; subst; auto.
    intros i hi. specialize (Ht i hi).
    unfold closedu_level_expr.
    apply wf_level_closedE => //.
  Qed.

  Lemma wf_sort_closedE {Σ : global_env} {wfΣ : wfE Σ} univs s :
    on_udecl_prop Σ univs ->
    wf_sort (Σ, univs) s -> closedu_sort #|polymorphic_instance univs| s.
  Proof using Type.
    destruct s => //=.
    apply wf_universe_closedE.
  Qed.

  Lemma wf_instance_closedE {Σ : global_env} {wfΣ : wfE Σ} {univs u} :
    on_udecl_prop Σ univs ->
    wf_instance (Σ, univs) u ->
    closedu_instance #|polymorphic_instance univs| u.
  Proof using Type.
    intros ond Ht.
    red in Ht. unfold closedu_instance. solve_all.
    now eapply wf_level_closedE.
  Qed.

  Lemma wf_universes_closeduE {Σ : global_env} {wfΣ : wfE Σ} {univs t} :
    on_udecl_prop Σ univs ->
    wf_universes (Σ, univs) t -> closedu #|polymorphic_instance univs| t.
  Proof using Type.
    intros ond. induction t using term_forall_list_ind; cbn => //; solve_all.
    - apply wf_sort_closedE => //.
      destruct s => //=.
      now move/wf_universe_reflect: H.
    - eapply wf_instance_closedE => //.
      apply All_forallb in H.
      rewrite -forallb_map wf_universeb_instance_forall in H.
      now move/wf_instanceP: H.
    - eapply wf_instance_closedE => //.
      apply All_forallb in H.
      rewrite -forallb_map wf_universeb_instance_forall in H.
      now move/wf_instanceP: H.
    - eapply wf_instance_closedE => //.
      apply All_forallb in H.
      rewrite -forallb_map wf_universeb_instance_forall in H.
      now move/wf_instanceP: H.
    - unfold test_predicate_ku in *; solve_all.
      eapply wf_instance_closedE => //.
      apply All_forallb in H0.
      rewrite -forallb_map wf_universeb_instance_forall in H0.
      now move/wf_instanceP: H0.
    - unfold test_branch in *; solve_all.
    - unfold test_def in *; solve_all.
    - unfold test_def in *; solve_all.
    - eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
      intros. to_wfu. eapply wf_level_closedE; tea.
      now apply wf_universe_make.
  Qed.

  Lemma wf_ctx_universes_closedE {Σ} {wfΣ : wfE Σ} {univs ctx} :
    on_udecl_prop Σ univs ->
    wf_ctx_universes (Σ, univs) ctx ->
    closedu_ctx #|polymorphic_instance univs| ctx.
  Proof using Type.
    intros ond. induction ctx => //.
    rewrite /wf_ctx_universes /= => /andP[] wfa wfctx.
    rewrite IHctx // /=.
    unfold wf_decl_universes, test_decl in *.
    destruct a as [na [b|] ty]; cbn in *.
    move/andP: wfa => [].
    now do 2 move/(wf_universes_closeduE ond) => ->.
    now move/(wf_universes_closeduE ond): wfa => ->.
  Qed.

  Lemma closed_ind_predicate_contextE {Σ ind mdecl idecl} {wfΣ : wfE Σ} :
    declared_inductive Σ ind mdecl idecl ->
    closedu_ctx #|polymorphic_instance (ind_universes mdecl)|
        (ind_params mdecl) ->
    closedu_ctx #|polymorphic_instance (ind_universes mdecl)|
            (ind_indices idecl) ->
    test_context (closedu #|abstract_instance (ind_universes mdecl)|) (ind_predicate_context ind mdecl idecl).
  Proof using Type.
    intros decli.
    rewrite /ind_predicate_context; cbn.
    rewrite closedu_mkApps /=.
    rewrite closedu_abstract_instance /= => clpars clinds.
    apply/andP; split.
    * apply closedu_expand_lets_ctx. now rewrite clpars clinds.
    * apply closedu_to_extended_list_k.
      rewrite test_context_app.
      rewrite (closedu_smash_context _ _ clpars).
      apply closedu_expand_lets_ctx => //.
      now rewrite clpars.
  Qed.

  Lemma closedu_indsE {Σ ind mdecl} {wfΣ : wfE Σ} :
    forallb (closedu #|abstract_instance (ind_universes mdecl)|)
      (inds ind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl)).
  Proof using Type.
    rewrite /inds.
    induction #|ind_bodies mdecl|; cbn; auto.
    rewrite IHn andb_true_r.
    eapply closedu_abstract_instance.
  Qed.

  Theorem wf_typesE :
    env_propE (fun Σ Γ t T => wf_universes Σ t && wf_universes Σ T)
      (fun Σ _ j => lift_wfbu_term (wf_universes Σ) (wf_sortb Σ) j)
      (fun Σ Γ => wf_ctx_universes Σ Γ).
  Proof using Type.
    apply typingE_ind_env; unfold lift_wfbu_term; intros; rename_all_hyps; cbn; rewrite -!/(wf_universes _ _) ;
    specIH; to_prop;
    cbn; auto.

    - eapply MRReflect.introT. 1: apply lift_wfu_wfbu_term.
      apply lift_typing_subjtyp with (1 := X) => //= t T [] _ /andP[] //.

    - apply All_local_env_cst, All_forallb in X0.
      apply forallb_impl with (2 := X0) => [] [na bo ty] _ //= /andP[] //=.

    - rewrite wf_universes_lift.
      eapply forallb_nth_error with (n := n) in H0. rewrite heq_nth_error /= in H0.
      now move/andP: H0.

    - apply/andP; split; to_wfu; cbn ; eauto with pcuic.

    - cbn in *; to_wfu ; eauto with pcuic.
    - rewrite wf_universes_subst. constructor. to_wfu; auto. constructor.
      now move/andP: H1 => [].

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constant_invE _ _ _ _ wf_universes_weakenE wfΣ X H0) as [[_ X0]%andb_and _]%andb_and.
      unshelve eapply declared_constant_to_gen in H0; eauto.
      epose proof (weaken_lookup_on_global_env' Σ.1 _ _ wfΣ H0).
      eapply wf_universes_instE. 2:eauto. all:eauto.
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_inductive_invE wf_universes_weakenE wfΣ X isdecl).
      move/onArity : X0 => /andP[] /andP[] /= _ Hind _.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      eapply wf_universes_instE; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wfΣ (proj1 isdecl)).
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constructor_invE wf_universes_weakenE wfΣ X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_universes_subst.
      { apply wf_universes_inds.
        now eapply consistent_instance_ext_wf. }
      move/on_ctype : onc => /andP[] /andP[] /= _ onc _.
      clear nthe. unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      eapply wf_universes_instE; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wfΣ (proj1 (proj1 isdecl))).
      now eapply consistent_instance_ext_wf.

    - rewrite wf_universes_mkApps in H6.
      move/andP: H6 => /= [] wfu; rewrite forallb_app.
      move/andP=> [] wfpars wfinds.
      cbn in wfu.
      rewrite wfu /= wfpars wf_universes_mkApps /=
        forallb_app wfinds /= H0 /= !andb_true_r.
      pose proof (declared_inductive_invE wf_universes_weakenE wfΣ X isdecl) as Hoib.
      move:(onArityRed Hoib) => /andP[] /andP[] /= _ hty _.
      rewrite !wf_universes_it_mkProd_or_LetIn in hty.
      move/and3P: hty => [] wfp wfindis wfisort.
      have ond : on_udecl_prop Σ (ind_universes mdecl).
      { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      }
      eapply wf_ctx_universes_closedE in wfp => //.
      eapply wf_ctx_universes_closedE in wfindis => //.
      rewrite (consistent_instance_length H2).
      erewrite closedu_compare_decls; tea.
      rewrite closed_ind_predicate_contextE // /=.
      unfold test_branch.
      apply/andP; split.
      * have wfbrctx : All (fun cdecl =>
          closedu_ctx #|polymorphic_instance (ind_universes mdecl)| (cstr_args cdecl))
          (ind_ctors idecl).
        { pose proof (onConstructors := onConstructors Hoib).
          clear -wfΣ ond onConstructors.
          red in onConstructors. solve_all. destruct X.
          move : on_ctype => /andP[] /andP[] /= _ wfty _.
          rewrite cstr_eq in wfty.
          rewrite !wf_universes_it_mkProd_or_LetIn in wfty.
          move/and3P: wfty => [] _ clargs _.
          apply wf_ctx_universes_closedE in clargs => //. }
        solve_all.
        erewrite closedu_compare_decls; [|tea].
        rewrite /cstr_branch_context.
        eapply closedu_expand_lets_ctx.
        rewrite wfp. eapply closedu_subst_context.
        rewrite a.
        now rewrite closedu_indsE.
      * rewrite wf_universes_it_mkLambda_or_LetIn H7 andb_true_r.
        move: H4.
        rewrite /wf_ctx_universes forallb_app => /andP[hctx _].
        apply (MRReflect.introT onctxP).
        solve_all. unfold ondecl, wf_decl_universes, on_decl_universes in *.
        move/andP:H3 => [Hb Ht] //; split; tas.
        now destruct decl_body.

    - rewrite /subst1. rewrite wf_universes_subst.
      constructor => //. eapply All_rev.
      rewrite wf_universes_mkApps in H2.
      move/andP: H2 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_invE wf_universes_weakenE wfΣ X isdecl) as Hproj.
      destruct (declared_inductive_invE); simpl in *.
      destruct ind_ctors as [|cs []] => //.
      destruct ind_cunivs as [|cunivs []] => //;
      destruct Hproj as [[[? ?] ?] ?] => //.
      red in o0.
      destruct nth_error eqn:heq => //.
      destruct o0  as [_ ->].
      rewrite wf_universes_mkApps {1}/wf_universes /= -!/(wf_universes _ _)
        wf_universeb_instance_forall in H2.
      move/andP: H2 => [/wf_instanceP wfu wfargs].
      unshelve eapply declared_projection_to_gen in isdecl; eauto.
      eapply (wf_universes_instE (ind_universes mdecl)); eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wfΣ (proj1 (proj1 (proj1 isdecl)))).
      rewrite wf_universes_subst.
      eapply wf_universes_inds; eauto.
      eapply wf_abstract_instance.
      rewrite wf_universes_subst. apply wf_projs.
      rewrite wf_universes_lift.
      rewrite smash_context_app smash_context_acc in heq.
      autorewrite with len in heq. rewrite nth_error_app_lt in heq.
      autorewrite with len. lia.
      rewrite nth_error_subst_context in heq.
      autorewrite with len in heq. simpl in heq.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl)) _ _).
      autorewrite with len in H0. simpl in H0. rewrite -> H0 in heq. clear H0.
      autorewrite with len in heq.
      simpl in heq.
      destruct nth_error eqn:hnth; simpl in * => //.
      noconf heq. simpl.
      rewrite wf_universes_subst.
      apply wf_extended_subst.
      move:onArityRed => /andP[] /andP[] /= _ Hs _.
      rewrite !wf_universes_it_mkProd_or_LetIn in Hs.
      now move/andP: Hs => /andP /andP [].
      rewrite wf_universes_lift.
      eapply PCUICWfUniverses.wf_universes_local_ctx_smash in s.
      eapply wf_universes_local_ctx_nth_error in s; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - apply/andP; split; eauto.
      destruct X0; cbn => //.
      rtoProp; intuition eauto. solve_all.
      destruct X0; cbn => //.
      simp prim_type. cbn. rtoProp; intuition.
  Qed.

  Lemma typing_wf_universesE {Σ : global_env_ext} {Γ t T} :
    wfE Σ ->
    Σ ;;; Γ |-E t : T -> wf_universes Σ t && wf_universes Σ T.
  Proof using Type.
    intros wfΣ Hty.
    exact (env_propE_typing wf_typesE _ wfΣ _ _ _ Hty).
  Qed.

  Lemma typing_wf_sortE {Σ : global_env_ext} {Γ t s} :
    wfE Σ ->
    Σ ;;; Γ |-E t : tSort s -> wf_sort Σ s.
  Proof using Type.
    intros wfΣ Hty.
    apply typing_wf_universesE in Hty as [_ wfs]%andb_and; auto.
    cbn in wfs. now to_wfu.
  Qed.

  Lemma isType_wf_universesE {Σ Γ T} : wfE Σ.1 -> isTypeE Σ Γ T -> wf_universes Σ T.
  Proof using Type.
    intros wfΣ (_ & s & Hs & _). now eapply typing_wf_universesE in Hs as [HT _]%andb_and.
  Qed.

End CheckerFlags.

#[global]
Hint Extern 4 (wf_sort _ ?u) =>
  match goal with
  [ H : typingE _ _ _ (tSort u) |- _ ] => apply (typing_wf_sortE _ H)
  end : pcuic.
