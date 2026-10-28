(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, T0 copy 2: the closedness half of [Typing/PCUICClosedTyp.v] over [typingE]

  Base lines 13-552 at trunk 0729d50e (closedness of declarations and of typed
  terms, up to [declared_constant_closed_body]), copied over [typingE], [wfE],
  [wf_localE] and [cumulSpecE0] (lanes/eta/t0-plan.md §3 row 2); every lemma takes
  the suffix [E]; the proofs are base's. It gives the instance
  [wfE_ClosedBodies]: an environment checked with the η conversion satisfies the
  confluence spine's premise ([PCUICClosedBodies]). The reduction lemmas of the
  base file (from [red1_on_free_vars] on) do not mention typing and are not copied. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed
     PCUICOnFreeVars PCUICTyping PCUICReduction PCUICGlobalEnv PCUICWeakeningEnvConv PCUICClosedConv
     PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICClosedTyp
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICWeakeningEnvTypEta PCUICClosedBodies.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Lemma closedn_All_local_closedE:
  forall (cf : checker_flags) (Σ : global_env_ext) (Γ : context) (wfΓ : wf_localE Σ Γ),
    All_local_env_over (typingE Σ) (fun Γ _ t T _ => closedn #|Γ| t && closedn #|Γ| T) Γ wfΓ ->
    closed_ctx Γ.
Proof.
  intros cf Σ Γ wfΓ al.
  induction al; try constructor;
  rewrite closedn_ctx_cons IHal /= /test_decl //; cbn.
  now move/andP: Hs => [] /= -> _.
Qed.

(** [closed_cstr_branch_context_gen] without its unused [wf Σ] premise. *)
Lemma closed_cstr_branch_context_genE {c mdecl cdecl} :
  closed_inductive_decl mdecl ->
  closed_constructor_body mdecl cdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (cstr_branch_context c mdecl cdecl).
Proof.
  intros cl clc.
  move/andP: cl => [] clpars _.
  move/andP: clc => [] /andP [] clargs clinds cltype.
  rewrite /cstr_branch_context /=.
  eapply (closedn_ctx_expand_lets 0) => // /=.
  eapply (closedn_ctx_subst 0). len. now rewrite Nat.add_comm.
  eapply closed_inds.
Qed.

Lemma declared_minductive_ind_nparsE {cf : checker_flags} {Σ} {wfΣ : wfE Σ} {mdecl ind} :
  declared_minductive Σ ind mdecl ->
  ind_npars mdecl = context_assumptions mdecl.(ind_params).
Proof.
  intros h.
  unshelve eapply declared_minductive_to_gen in h; tea.
  unfold declared_minductive in h.
  eapply lookup_on_global_env in h; tea.
  destruct h as (Σ' & ext & wfΣ' & decl').
  red in decl'. destruct decl' as [h ? ? ?].
  now rewrite onNpars.
Qed.

Lemma weaken_env_prop_closedE {cf : checker_flags} :
  weaken_env_prop cumulSpecE0 (lift_typing typingE) (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)).
Proof. intros ?. auto. Qed.

Lemma declared_projection_closed_indE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ}{mdecl idecl cdecl p pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  on_global_env cumulSpecE0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ ->
  closedn (S (ind_npars mdecl)) pdecl.(proj_type).
Proof.
  intros isdecl X0.
  pose proof (declared_projection_invE weaken_env_prop_closedE wfΣ X0 isdecl) as onp.
  set (declared_inductive_invE _ wfΣ X0 _) as oib in *.
  clearbody oib. unfold declared_projection in isdecl.
  have onpars := onParams (declared_minductive_invE weaken_env_prop_closedE wfΣ X0 isdecl.p1.p1.p1).
  have parslen := onNpars (declared_minductive_invE weaken_env_prop_closedE wfΣ X0 isdecl.p1.p1.p1).
  simpl in onp.
  destruct (ind_ctors idecl) as [|? []] eqn:Heq; try contradiction.
  destruct onp as [_ onp].
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  destruct onp as [onna onp]. rewrite {}onp.
  pose proof (onConstructors oib) as onc.
  red in onc. rewrite Heq in onc. inv onc. clear X1.
  eapply on_cargs in X.
  simpl.
  replace (S (ind_npars mdecl)) with (0 + (1 + ind_npars mdecl)) by lia.
  eapply closedn_subst.
  { clear. unfold inds. generalize (ind_bodies mdecl).
    induction l; simpl; auto. }
  rewrite inds_length.
  eapply closedn_subst0.
  { clear. unfold projs. induction p.(proj_arg); simpl; auto. }
  rewrite projs_length /=.
  eapply (@closed_upwards (ind_npars mdecl + #|ind_bodies mdecl| + p.(proj_arg) + 1)).
  2:lia.
  eapply closedn_lift.
  clear -parslen isdecl Heq' onpars X.
  rename X into args.
  apply sorts_local_ctx_Pclosed in args.
  red in onpars.
  eapply All_local_env_Pclosed in onpars.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|ind_params mdecl| + i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  2:{ intros n x. rewrite app_context_length.
      intros H; eapply closed_decl_upwards; eauto. lia. }
  eapply (Alli_shiftn (P:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  rewrite Nat.add_0_r in args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in onpars.
  2:{ intros n x d. eapply closed_decl_upwards; eauto; lia. }
  epose proof (Alli_app_inv onpars). rewrite List.length_rev /= in X.
  specialize (X args). rewrite -List.rev_app_distr in X.
  clear onpars args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|arities_context (ind_bodies mdecl)| + i) d)) in X.
  2:intros; eapply closed_decl_upwards; eauto; lia.
  eapply closed_smash_context_unfold in X.
  eapply Alli_rev_nth_error in X; eauto.
  rewrite smash_context_length in X. simpl in X.
  eapply nth_error_Some_length in Heq'. rewrite smash_context_length in Heq'.
  simpl in Heq'. unfold closed_decl in X.
  move/andP: X => [] _ cl.
  eapply closed_upwards. eauto. rewrite arities_context_length.
  rewrite context_assumptions_app parslen.
  rewrite context_assumptions_app in Heq'. lia.
Qed.


Lemma declared_decl_closed_indE {cf : checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {cst decl} :
  lookup_env Σ cst = Some decl ->
  on_global_env cumulSpecE0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ ->
  on_global_decl cumulSpecE0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t))
                 (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_envE; eauto. do 2 red; eauto.
Qed.

Lemma declared_minductive_closed_indE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ}{mdecl mind} :
  on_global_env cumulSpecE0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) Σ ->
  declared_minductive Σ mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  intros HΣ decl. pose proof (decl_ := decl).
  unshelve eapply declared_minductive_to_gen in decl; tea.
  pose proof (declared_decl_closed_indE decl) as decl'.
  specialize (decl' HΣ).
  red in decl'.
  unfold closed_inductive_decl.
  apply andb_and. split. apply onParams in decl'.
  now apply closedn_All_local_env in decl'; auto.
  apply onInductives in decl'.
  eapply All_forallb.

  assert (Alli (fun i =>  declared_inductive Σ {| inductive_mind := mind; inductive_ind := i |} mdecl)
    0 (ind_bodies mdecl)).
  { eapply forall_nth_error_Alli. intros.
    split; auto.  }
  eapply Alli_mix in decl'; eauto. clear X.
  clear decl.
  eapply Alli_All; eauto.
  intros n x [decli oib].
  rewrite /closed_inductive_body.
  apply andb_and; split. apply andb_and. split.
  - rewrite andb_and. split.
    * apply onArity in oib.
      now move/andP: oib => [] /=.
    * pose proof (onArityRed oib) as X. unfold on_type_rel in X.
      cbn in X.
      rewrite !closedn_it_mkProd_or_LetIn /= !andb_true_r in X.
      now move/andP: X.
  - pose proof (onConstructors oib).
    red in X. eapply All_forallb. eapply All2_All_left; eauto.
    intros cdecl cs X0;
    move: (on_ctype X0) => /=. unfold on_type_rel. cbn.
    simpl. unfold closed_constructor_body.
    intros Hty.
    rewrite arities_context_length in Hty.
    rewrite Hty.
    rewrite X0.(cstr_eq) closedn_it_mkProd_or_LetIn in Hty.
    move/andP: Hty => [] _.
    rewrite closedn_it_mkProd_or_LetIn.
    move/andP=> [] ->. rewrite closedn_mkApps /=.
    move/andP=> [] _. rewrite forallb_app.
    now move/andP=> [] _ ->.

  - eapply All_forallb.
    pose proof (onProjections oib).
    destruct (eq_dec (ind_projs x) []) as [->|eq]; try constructor.
    destruct (ind_projs x) in X, eq; try congruence. clear eq.
    destruct (ind_ctors x) as [|cdecl []] eqn:hcdecl; try contradiction.
    apply on_projs in X.
    assert (Alli (fun i pdecl => declared_projection Σ
      (mkProjection {| inductive_mind := mind; inductive_ind := n |} mdecl.(ind_npars) i) mdecl x cdecl pdecl)
      0 (ind_projs x)).
    { eapply forall_nth_error_Alli.
      intros. split; auto. split; auto. cbn. now rewrite hcdecl. }
    eapply (Alli_All X0). intros.
    now eapply declared_projection_closed_indE in H.
Qed.



Lemma typecheck_closedE `{cf : checker_flags} :
  env_propE (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T)
           (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t))
           (fun Σ Γ => closed_ctx Γ).
Proof.
  assert (X := weaken_env_prop_closedE).
  apply typingE_ind_env; intros * wfΣ Γ wfΓ *; intros; unfold lift_wfb_term in *; cbn in *;
  rewrite -> ?andb_and in *; try solve [intuition auto].

  - destruct X0 as (Htm & s & (_ & Hty) & _).
    rewrite /= andb_true_r in Hty. split; tas.
    destruct j_term => //=.
    move:Htm => [] _ /andP [] //.

  - now apply closedn_All_local_closedE in X0.

  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition auto. all: try lia. clear H1.

    induction Γ in n, H, H0, H2 |- *. rewrite nth_error_nil in H. discriminate.
    destruct n.
    simpl in H. noconf H. simpl.
    rewrite -Nat.add_1_r. apply closedn_lift.
    rewrite closedn_ctx_cons in H0. move/andP: H0 => [_ ca].
    destruct a as [na [b|] ty]. simpl in ca.
    rewrite /test_decl /= in ca.
    now move/andP: ca => [_ cty].
    now rewrite /test_decl /= in ca.
    simpl.
    rewrite -Nat.add_1_r.
    rewrite -(simpl_lift _ (S n) 0 1 0); try lia.
    apply closedn_lift. apply IHΓ; auto.
    rewrite closedn_ctx_cons in H0.
    now move/andP: H0 => [H0 _]. simpl in H2; lia.

  - intuition auto.
    generalize (closedn_subst [u] #|Γ| 0 B). rewrite Nat.add_0_r.
    move=> Hs. apply: Hs => /=. simpl. rewrite H1 => //.
    rewrite Nat.add_1_r. auto.

  - unshelve eapply declared_constant_to_gen in H0; tea.
    rewrite closedn_subst_instance.
    eapply lookup_on_global_env in X0; eauto.
    destruct X0 as (Σ' & hext & [onu HΣ'] & [IHtm IHty]%andb_and).
    simpl in *.
    eauto using closed_upwards with arith.

  - rewrite closedn_subst_instance.
    eapply declared_inductive_invE in X0; eauto with extends.
    apply onArity in X0.
    rewrite /on_type_rel /lift_wfb_term /= in X0.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    apply closedn_subst0.
    + unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
      simpl. now rewrite IHn.
    + rewrite inds_length.
      rewrite closedn_subst_instance.
      eapply declared_inductive_invE in X0; eauto with extends.
      pose proof X0.(onConstructors) as XX.
      eapply All2_nth_error_Some in Hcdecl; eauto.
      destruct Hcdecl as [? [? ?]]. cbn in *.
      destruct o as [? ? HT _].
      rewrite /on_type_rel /lift_wfb_term /= in HT.
      rewrite arities_context_length in HT.
      eauto using closed_upwards with arith.

  - destruct H3 as [clret _].
    destruct H7 as [clc clty].
    rewrite closedn_mkApps in clty. simpl in clty.
    rewrite forallb_app in clty. move/andP: clty => [clpar clinds].
    rewrite app_context_length in clret.
    red in H9. eapply Forall2_All2 in H9.
    eapply All2i_All2_mix_left in X5; eauto.
    eapply declared_minductive_closed_indE in X0; tea. 2:exact isdecl.
    pose proof (closed_ind_closed_cstrs X0 isdecl).
    eapply All2i_All_mix_left in X5; tea. clear X6.
    intuition auto.
    + unfold test_predicate_k. simpl. rtoProp; intuition eauto.
      rewrite (closedn_ctx_alpha X1).
      eapply closed_ind_predicate_context in X0; tea.
      rewrite (wf_predicate_length_pars H1).
      now rewrite (declared_minductive_ind_nparsE isdecl).
      rewrite (All2_length X1).
      rewrite /predctx in clret.
      rewrite case_predicate_context_length_indices // in clret.
      { now rewrite ind_predicate_context_length. }
    + clear H9. solve_all. unfold test_branch_k. clear H7. solve_all.
      * rewrite (closedn_ctx_alpha a1).
        eapply closed_cstr_branch_context_genE in X0; tea.
        rewrite (wf_predicate_length_pars H1).
        now rewrite (declared_minductive_ind_nparsE isdecl).
      * rewrite (All2_length a1).
        len in H9.
        (*unfold case_branch_context_gen in H8. simpl in H9.
        rewrite case_branch_type_fst in H8. *)
        rewrite case_branch_context_length_args in H9 => //.
        now rewrite cstr_branch_context_length.
    + rewrite closedn_mkApps; auto.
      rewrite closedn_it_mkLambda_or_LetIn //.
      rewrite closedn_ctx_app in H4.
      now move/andP: H4 => [].
      now rewrite Nat.add_comm.
      rewrite forallb_app. simpl. now rewrite clc clinds.

  - intuition auto.
    apply closedn_subst0.
    + simpl. rewrite closedn_mkApps in H3.
      rewrite forallb_rev H2. apply H3.
    + rewrite closedn_subst_instance.
      eapply declared_projection_closed_indE in X0; eauto.
      simpl; rewrite List.length_rev H1.
      eapply closed_upwards; eauto. lia.

  - clear H.
    split. solve_all.
    rewrite /on_def_type /on_def_body ?andb_and in a0, b |- *. cbn in *.
    simpl in *. unfold test_def.
    rewrite -> app_context_length in *.
    subst types.
    rewrite fix_context_length in b. intuition auto.
    eapply nth_error_all in X1 as (_ & X1)%andb_and; eauto.

  - split. solve_all.
    rewrite /on_def_type /on_def_body ?andb_and in a0, b |- *. cbn in *.
    simpl in *. unfold test_def.
    rewrite -> app_context_length in *.
    subst types.
    rewrite fix_context_length in b. intuition auto.
    eapply nth_error_all in X1 as (_ & X1)%andb_and; eauto.

  - destruct p as [[] pv]; cbn in X0 |- *; simp prim_type => //.
    depelim pv. simp prim_type. cbn. depelim X1.
    move/andP: hdef => [] -> ->; rewrite !andb_true_r. split => //.
    solve_all.
Qed.

Lemma declared_minductive_closedE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mdecl mind} :
  declared_minductive Σ mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  eapply declared_minductive_closed_indE; tea.
  now apply (env_propE_sigma typecheck_closedE).
Qed.

Lemma declared_inductive_closedE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mdecl mind idecl} :
  declared_inductive Σ mind mdecl idecl ->
  closed_inductive_body mdecl idecl.
Proof.
  intros [decli hnth].
  eapply declared_minductive_closedE in decli; tea.
  move/andP: decli => [clpars cli].
  solve_all. eapply nth_error_all in cli; eauto.
  now simpl in cli.
Qed.

Lemma declared_projection_closedE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ}{mdecl idecl p cdecl pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.(proj_type).
Proof.
  intros; eapply declared_projection_closed_indE; eauto.
  eapply (env_propE_sigma typecheck_closedE); eauto.
Qed.

Lemma declared_inductive_closed_pars_indicesE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mdecl mind idecl} :
  declared_inductive Σ mind mdecl idecl ->
  closed_ctx (ind_params mdecl ,,, ind_indices idecl).
Proof.
  intros decli.
  pose proof (declared_minductive_closedE (proj1 decli)).
  move/andP: H => [] clpars _. move: decli.
  move/declared_inductive_closedE.
  move/andP => [] /andP [] clind clbodies.
  move/andP: clind => [] _ indpars _.
  now rewrite closedn_ctx_app clpars indpars.
Qed.

Lemma declared_constructor_closedE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mdecl idecl c cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closed_constructor_body mdecl cdecl.
Proof.
  intros declc.
  generalize (declared_minductive_closedE declc).
  rewrite /closed_inductive_decl.
  rewrite /closed_inductive_body.
  move/andP=> [_ clbs].
  destruct declc.
  destruct H.
  solve_all.
  eapply nth_error_all in clbs; eauto.
  simpl in clbs.
  move/andP: clbs => [] /andP [] _ clc _.
  solve_all.
  eapply nth_error_all in clc; eauto. now simpl in clc.
Qed.


Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma subject_closedE {cf} {Σ} {wfΣ : wfE Σ.1} {Γ t T} :
  Σ ;;; Γ |-E t : T ->
  closedn #|Γ| t.
Proof.
  now move/(env_propE_typing typecheck_closedE) => /andP [ct _].
Qed.

Lemma type_closedE {cf} {Σ} {wfΣ : wfE Σ.1} {Γ t T} :
  Σ ;;; Γ |-E t : T ->
  closedn #|Γ| T.
Proof.
  now move/typecheck_closedE => [_ [_ /andP [_ ct]]].
Qed.

#[global] Hint Extern 4 (closedn #|?Γ| ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |-E A : _ |- _ ] => exact (subject_closedE H)
  end : fvs.

#[global] Hint Extern 4 (closedn #|?Γ| ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |-E _ : A |- _ ] => exact (type_closedE H)
  end : fvs.

#[global] Hint Extern 10 => progress unfold PCUICTypingDef.typing in * : fvs.

Lemma lift_typing_closedE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ j} :
  lift_typing typingE Σ Γ j ->
  lift_wf_term (closedn #|Γ|) j.
Proof.
  intro Hj. apply lift_typing_subject with (1 := Hj) => t T.
  apply subject_closedE.
Qed.

Lemma is_open_term_closedE (Γ : context) t :
  closedn #|Γ| t = is_open_term Γ t.
Proof.
  rewrite closedP_on_free_vars.
  eapply on_free_vars_ext.
  now rewrite closedP_shiftnP.
Qed.

Lemma is_closed_ctx_closedE (Γ : context) :
  closed_ctx Γ = is_closed_context Γ.
Proof.
  rewrite closedn_ctx_on_free_vars //.
Qed.

#[global]
Hint Rewrite is_open_term_closedE is_closed_ctx_closedE : fvs.
#[global] Hint Extern 4 => progress autorewrite with fvs : fvs.

Lemma subject_is_open_termE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ t T} :
  Σ ;;; Γ |-E t : T ->
  is_open_term Γ t.
Proof.
  move/subject_closedE.
  now rewrite is_open_term_closedE.
Qed.

Lemma type_is_open_termE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ t T} :
  Σ ;;; Γ |-E t : T ->
  is_open_term Γ T.
Proof.
  move/type_closedE. now rewrite is_open_term_closedE.
Qed.

Lemma lift_typing_is_open_termE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ j} :
  lift_typing typingE Σ Γ j ->
  lift_wf_term (is_open_term Γ) j.
Proof.
  move/lift_typing_closedE => Hj.
  apply lift_wf_term_impl with (1 := Hj) => t.
  rewrite is_open_term_closedE //.
Qed.

Lemma closed_wf_localE `{checker_flags} {Σ Γ} :
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  closed_ctx Γ.
Proof.
  intros wfΣ wfΓ.
  apply (env_propE_wf_local typecheck_closedE Σ wfΣ _ wfΓ).
Qed.

#[global] Hint Extern 4 (is_open_term ?Γ ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |-E A : _ |- _ ] => exact (subject_is_open_termE H)
  end : fvs.

#[global] Hint Extern 4 (is_open_term ?Γ ?A = true) =>
  match goal with
  | [ H : _ ;;; Γ |-E _ : A |- _ ] => exact (type_is_open_termE H)
  end : fvs.

Lemma closed_ctx_on_ctx_free_varsE Γ : closed_ctx Γ = on_ctx_free_vars (closedP #|Γ| xpredT) Γ.
Proof.
  rewrite closedn_ctx_on_free_vars.
  now rewrite -on_free_vars_ctx_on_ctx_free_vars shiftnP_closedP shiftnP_xpredT Nat.add_0_r.
Qed.

Lemma wf_local_closed_contextE `{checker_flags} {Σ Γ} {wfΣ : wfE Σ} : wf_localE Σ Γ -> on_free_vars_ctx xpred0 Γ.
Proof.
  move/closed_wf_localE.
  now rewrite closed_ctx_on_ctx_free_varsE on_free_vars_ctx_on_ctx_free_vars_closedP.
Qed.

Lemma typing_closed_contextE {cf} {Σ} {wfΣ : wfE Σ} {Γ T U} :
  Σ ;;; Γ |-E T : U ->
  is_closed_context Γ.
Proof.
  now move/typingE_wf_local/wf_local_closed_contextE.
Qed.

#[global] Hint Extern 4 (is_closed_context ?Γ = true) =>
  match goal with
  | [ H : _ ;;; Γ |-E _ : _ |- _ ] => exact (typing_closed_contextE H)
  end : fvs.

Lemma ctx_inst_closedE {cf:checker_flags} (Σ : global_env_ext) Γ i Δ :
  wfE Σ.1 -> ctx_inst (typingE Σ) Γ i Δ -> All (closedn #|Γ|) i.
Proof.
  intros wfΣ; induction 1; auto; constructor; auto; fvs.
Qed.

#[global] Hint Resolve ctx_inst_closedE : fvs.

Lemma declared_decl_closedE `{checker_flags} {Σ : global_env} {cst decl} :
  wfE Σ ->
  lookup_env Σ cst = Some decl ->
  on_global_decl cumulSpecE0 (fun _ => lift_wfb_term1 (fun Γ t => closedn #|Γ| t)) (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  apply declared_decl_closed_indE; eauto.
  now eapply (env_propE_sigma typecheck_closedE).
Qed.



Lemma declared_constant_closed_typeE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {cst decl} :
  declared_constant Σ cst decl ->
  closed decl.(cst_type).
Proof.
  apply (env_propE_sigma typecheck_closedE) in wfΣ.
  intros h. unshelve eapply declared_constant_to_gen in h; tea.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as (Σ' & ext & wfΣ' & [Htm Hty]%andb_and).
  easy.
Qed.


Lemma declared_constant_closed_bodyE {cf : checker_flags} :
  forall (Σ : global_env) cst decl body,
    wfE Σ ->
    declared_constant Σ cst decl ->
    decl.(cst_body) = Some body ->
    closed body.
Proof.
  intros Σ cst decl body hΣ h e.
  apply (env_propE_sigma typecheck_closedE) in hΣ.
  unshelve eapply declared_constant_to_gen in h; tea.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as (Σ' & ext & wfΣ' & [Htm _]%andb_and).
  simpl in Htm.
  rewrite e in Htm.
  easy.
Qed.

(** The confluence spine's premise holds in an η-checked environment. With
    [wf_ClosedBodies] ([Typing/PCUICClosedTyp.v]) this gives BOTH instances FRAC
    requires for the [ClosedBodies] premise. *)
#[global] Instance wfE_ClosedBodies {cf : checker_flags} (Σ : global_env) {wfΣ : wfE Σ} :
  ClosedBodies Σ.
Proof.
  apply Build_ClosedBodies.
  - intros cst decl body h e. exact (declared_constant_closed_bodyE Σ cst decl body wfΣ h e).
  - destruct wfΣ as (_ & _ & o). exact (NoDup_on_global_decls _ _ _ _ _ o).
Qed.
