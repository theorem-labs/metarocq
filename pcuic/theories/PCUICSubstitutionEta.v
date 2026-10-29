(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICPosition PCUICCases PCUICSigmaCalculus
     PCUICUnivSubst PCUICContextSubst PCUICTyping
     PCUICWeakeningEnvConv PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICClosed PCUICClosedConv PCUICClosedTyp
     PCUICReduction PCUICWeakeningConv PCUICCumulativity PCUICUnivSubstitutionConv
     PCUICRenameDef PCUICRenameConv PCUICInstDef PCUICInstConv PCUICOnFreeVars PCUICClosedBodies
     PCUICSubstitution PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions PCUICWeakeningEnvTypEta PCUICClosedTypEta
     PCUICInstDefEta PCUICRenameTypEta PCUICWeakeningTypEta PCUICInstTypEta
     PCUICEtaDefs PCUICEtaCanon PCUICEtaConfluence PCUICEtaFInst PCUICEtaI5 PCUICEtaI5A2 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICWsCumulEtaSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Substitution lemmas for derivations over [typingE]

  The E copy of [PCUICSubstitution]. Each lemma of the base file that mentions
  typing, cumulativity, [wf_local] or [wf] is copied, and its statement is the
  base statement with only the relations renamed: [typing] → [typingE],
  [wf_local] → [wf_localE], [wf] → [wfE], [env_prop] → [env_propE], [isType] /
  [isTypeRel] → [isTypeE] / [isTypeRelE], [subs] / [subslet] → [subsE] /
  [subsletE], [well_subst] → [well_substE], [wt_cumul_pb] → [wt_cumul_pbE]
  ([PCUICWsCumulEtaCtxTyp]), [cumulSpec0] → [cumulSpecE0], and the algorithmic
  cumulativity [cumulAlgo] ([Σ ;;; Γ |- t <= u]) → [JoinE Σ Γ Cumul].

  Copied (the E name is the base name with the suffix [E]): the inductives
  [subsE] ([emptysE], [cons_assE]) and [subsletE] ([emptysletE], [cons_let_assE],
  [cons_let_defE]); [subs_lengthE], [subslet_defE], [subslet_ass_tipE],
  [subslet_def_tipE], [subslet_nth_errorE], [subslet_lengthE], [subst_lengthE],
  [subs_nth_error_geE], [subs_nth_error_ltE], [subslet_nth_error_ltE],
  [typed_substE], [subst_wf_localE], [subst_declared_constantE],
  [wf_arities_context'E], [wf_arities_contextE], [on_constructor_closed_aritiesE],
  [on_constructor_closedE], [subslet_untyped_subsletE], [subs_nth_errorE],
  [subs_usubstE]; the definitions [wt_cumulE], [wt_convE], [wt_cumul_cumE],
  [wt_conv_convE] and their notations; [red1P_on_free_vars_rightE],
  [isType_wf_localE], [isType_closedPTE], [substitution_red1E],
  [substitution_let_redE], [substitution_untyped_let_redE],
  [substitution_untyped_redE], [substitution_redE], [red_redE],
  [untyped_substitution_redE], [substitution_untyped_cumulE],
  [substitution_cumul0E], [substitution_cumul_letE], [usubst_well_substE],
  [subslet_well_substE], [All_local_env_instE], [substitution_propE],
  [substitutionE], [lift_typing_substitutionE], [lift_typing_substE],
  [isType_substitutionE], [isType_substE], [isTypeRel_substitutionE],
  [isTypeRel_substE], [substitution_wf_localE], [substitution0E],
  [substitution_letE], [substitution_wt_cumul_pbE], [substitution_cumulE],
  [substitution_convE].

  [substitution_wt_cumul_pbE] is base [substitution_wt_cumul_pb] with the twin
  statement, on another proof route: base goes through [wt_cumul_pb_equalityP],
  whose E form is false (refuted below); here the join is substituted by
  [untyped_substitution_ws_cumul_pbE] ([PCUICWsCumulEtaSubst]), after [wt_cumul_pbE_ws_cumul_pbE]. The
  route needs the substituted terms open, which [subsletE_open_terms] (a new
  helper, no base twin) gives from their typing. The proof of
  [substitution_propE] uses [on_wf_global_env_implE], the twin of
  [EnvironmentTyping.on_wf_global_env_impl] at [cumulSpecE0] and [typingE] (copied
  here, as no E copy of that file exists).

  Not copied: [wt_cumul_pb] (its twin [wt_cumul_pbE] is in [PCUICWsCumulEtaCtxTyp]);
  [wt_cumul_pb_equalityP] (its E form is false: [wt_cumul_pbE_equalityP_false]);
  [red_abs_alt], [red_letin_alt] (their section's [wf Σ] is not used: [Proof using
  Type]); the [_cb] lemmas ([substitution_untyped_let_red_cb],
  [substitution_untyped_red_cb], [red_red_cb]), which take only [ClosedBodies] and
  are used from base; [cumulP], [red1P] and every other declaration, which
  mention none of the relations. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Local Set Keyed Unification.

Set Default Goal Selector "!".

Local Open Scope sigma_scope.

(** Well-typed substitution into a context with *no* let-ins *)

Inductive subsE {cf:checker_flags} (Σ : global_env_ext) (Γ : context) : list term -> context -> Type :=
| emptysE : subsE Σ Γ [] []
| cons_assE Δ s na t T : subsE Σ Γ s Δ -> Σ ;;; Γ |-E t : subst0 s T -> subsE Σ Γ (t :: s) (Δ ,, vass na T).

Lemma subs_lengthE {cf:checker_flags} {Σ} {Γ s Δ} : subsE Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; auto. f_equal. auto.
Qed.

(** Well-typed substitution into a context with let-ins *)

Inductive subsletE {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptysletE : subsletE Σ Γ [] []
| cons_let_assE Δ s na t T : subsletE Σ Γ s Δ ->
              Σ ;;; Γ |-E t : subst0 s T ->
             subsletE Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_defE Δ s na t T :
    subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E subst0 s t : subst0 s T ->
    subsletE Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).
Derive Signature for subsletE.

#[global] Hint Constructors subsletE : pcuic.

Lemma subslet_defE {cf} {Σ : global_env_ext} {Γ Δ s na t T t'} :
  subsletE Σ Γ s Δ ->
  Σ;;; Γ |-E subst0 s t : subst0 s T ->
  t' = subst0 s t ->
  subsletE Σ Γ (t' :: s) (Δ ,, vdef na t T).
Proof.
  now intros sub Ht ->; constructor.
Qed.

Lemma subslet_ass_tipE {cf} {Σ : global_env_ext} {Γ na t T} :
  Σ;;; Γ |-E t : T ->
  subsletE Σ Γ [t] [vass na T].
Proof.
  intros; repeat constructor.
  now rewrite !subst_empty.
Qed.

Lemma subslet_def_tipE {cf} {Σ : global_env_ext} {Γ na t T} :
  Σ;;; Γ |-E t : T ->
  subsletE Σ Γ [t] [vdef na t T].
Proof.
  intros; apply subslet_defE; try constructor.
  all:now rewrite !subst_empty.
Qed.

#[global] Hint Resolve subslet_ass_tipE subslet_def_tipE : pcuic.

Lemma subslet_nth_errorE {cf:checker_flags} {Σ Γ s Δ decl n} :
  subsletE Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  ∑ t, nth_error s n = Some t ×
  let ty := subst0 (skipn (S n) s) (decl_type decl) in
  Σ ;;; Γ |-E t : ty ×
  match decl_body decl return Type with
  | Some t' =>
    let b := subst0 (skipn (S n) s) t' in
    (t = b)
  | None => unit
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. exists t; split; auto.
    simpl. split; auto.
  - intros. destruct decl as [na' [b|] ty]; cbn in *.
    + specialize (IHX _ H) as [t' [hnth [hty heq]]]. exists t'; intuition auto.
    + now apply IHX.
  - intros [= <-]. eexists; split; eauto.
    simpl. split; auto.
  - apply IHX.
Qed.

Lemma subslet_lengthE {cf:checker_flags} {Σ Γ s Δ} : subsletE Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; f_equal; auto.
Qed.

Lemma subst_lengthE {cf:checker_flags} Σ Γ s Γ' : subsE Σ Γ s Γ' -> #|s| = #|Γ'|.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma subs_nth_error_geE {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subsE Σ Γ s Γ' ->
  #|Γ' ,,, Γ''| <= v ->
  nth_error (Γ ,,, Γ' ,,, Γ'') v =
  nth_error (Γ ,,, subst_context s 0 Γ'') (v - #|Γ'|).
Proof.
  simpl.
  intros. rewrite app_context_length in H.
  rewrite !nth_error_app_ge; autorewrite with wf; f_equal; try lia.
Qed.

Lemma subs_nth_error_ltE {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subsE Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma subslet_nth_error_ltE {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subsletE Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma typed_substE `{checker_flags} Σ Γ t T n k :
  wfE Σ.1 -> k >= #|Γ| ->
  Σ ;;; Γ |-E t : T -> subst n k T = T /\ subst n k t = t.
Proof.
  intros wfΣ Hk Hty.
  have Ht := subject_closedE (wfΣ := wfΣ) Hty.
  have HT := type_closedE (wfΣ := wfΣ) Hty.
  split; apply subst_closedn; eapply closed_upwards; tea; lia.
Qed.

Lemma subst_wf_localE `{checker_flags} Σ Γ n k :
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  subst_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold subst_context, snoc; rewrite fold_context_k_snoc0;
    auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl.
  - destruct t0 as (_ & s & Ht & _). unfold vass. simpl. f_equal.
    eapply typed_substE; eauto. lia.
  - unfold vdef.
    destruct t0 as (Hb & s & Ht & _). cbn in Hb.
    f_equal.
    + f_equal. eapply typed_substE; eauto. lia.
    + eapply typed_substE; eauto. lia.
Qed.

Lemma subst_declared_constantE `{H:checker_flags} Σ cst decl n k u :
  wfE Σ ->
  declared_constant Σ cst decl ->
  map_constant_body (subst n k) (map_constant_body (subst_instance u) decl) =
  map_constant_body (subst_instance u) decl.
Proof.
  intros. unshelve eapply declared_constant_to_gen in H0; eauto.
  eapply declared_decl_closedE in H0 as [Hb Ht]%andb_and; eauto.
  unfold map_constant_body. cbn in *.
  f_equal.
  - rewrite <- (closedn_subst_instance 0 _ u) in Ht.
    apply subst_closedn; eauto using closed_upwards with arith wf.
  - destruct cst_body; cbn in *; auto.
    f_equal.
    rewrite <- (closedn_subst_instance 0 _ u) in Hb.
    eapply subst_closedn; eauto using closed_upwards with arith wf.
Qed.

Lemma wf_arities_context'E {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {mind mdecl} :
  on_inductive cumulSpecE0 (lift_typing typingE) Σ mind mdecl ->
  wf_localE Σ (arities_context (ind_bodies mdecl)).
Proof.
  intros Hdecl.
  apply onInductives in Hdecl.
  unfold arities_context.
  revert Hdecl.
  induction (ind_bodies mdecl) using rev_ind. 1: constructor.
  intros Ha.
  rewrite rev_map_app.
  simpl. apply Alli_app in Ha as [Hl Hx].
  inv Hx. clear X0.
  apply onArity in X as (_ & s & Hs & _ & Her).
  specialize (IHl Hl).
  econstructor; eauto.
  fold (arities_context l) in *.
  cbn in Her.
  repeat (eexists; cbn; tea).
  now eapply weaken_ctxE in Hs.
Qed.

Lemma wf_arities_contextE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mind mdecl} :
  declared_minductive Σ mind mdecl -> wf_localE (Σ, ind_universes mdecl) (arities_context mdecl.(ind_bodies)).
Proof.
  intros Hdecl.
  eapply declared_minductive_invE in Hdecl. 2:exact weaken_env_prop_typingE. all:eauto.
  eapply wf_arities_context'E; eauto.
Qed.

Lemma on_constructor_closed_aritiesE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mind mdecl idecl indices cdecl cs} :
  on_constructor cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) indices idecl cdecl cs ->
  closedn #|arities_context (ind_bodies mdecl)| cdecl.(cstr_type).
Proof.
  intros [? ? (_ & s & Hs & _) _ _ _ _].
  pose proof (typingE_wf_local Hs).
  destruct cdecl as [id cty car].
  apply subject_closedE in Hs; eauto.
Qed.

Lemma on_constructor_closedE {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mind mdecl u idecl indices cdecl cs} :
  on_constructor cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) indices idecl cdecl cs ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance u cdecl.(cstr_type))
  in closed cty.
Proof.
  intros [? ? (_ & s & Hs & _) _ _ _ _].
  pose proof (typingE_wf_local Hs).
  destruct cdecl as [id cty car].
  apply subject_closedE in Hs; eauto.
  rewrite arities_context_length in Hs.
  simpl in *.
  eapply (closedn_subst _ 0 0).
  - clear. unfold inds.
    induction #|ind_bodies mdecl|; simpl; try constructor; auto.
  - simpl. now rewrite -> inds_length, closedn_subst_instance.
Qed.

Lemma subslet_untyped_subsletE {cf:checker_flags} Σ Γ s Γ' : subsletE Σ Γ s Γ' -> untyped_subslet Γ s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.
Coercion subslet_untyped_subsletE : subsletE >-> untyped_subslet.

Lemma subs_nth_errorE {cf:checker_flags} Σ Γ s Δ decl n t :
  subsE Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  nth_error s n = Some t ->
  match decl_body decl return Type with
  | Some t' => False
  | None =>
    let ty := subst0 (skipn (S n) s) (decl_type decl) in
    Σ ;;; Γ |-E t : ty
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. intros [= ->].
    simpl. exact t1.
  - intros. destruct decl as [na' [b|] ty]; cbn in *.
    + eapply IHX. all: eauto.
    + now apply IHX.
Qed.

Arguments iota_red : simpl never.

(** Substitution without lets in Γ' *)
Lemma subs_usubstE {cf:checker_flags} Σ Γ Γ' Γ'' s :
  subsE Σ Γ s Γ' ->
  usubst (Γ,,, Γ',,, Γ'') (⇑^#|Γ''| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ'').
Proof.
  intros subs n decl.
  case: (nth_error_app_context (Γ ,,, Γ') Γ'' n) => // x hnth hlt [=] hx; subst x => b hb.
  - left; eexists n, _.
    split; auto.
    * rewrite Upn_eq /subst_consn idsn_lt //.
    * rewrite nth_error_app_lt; len => //.
      change (fun m => S (n + m)) with (lift_renaming (S n) 0).
      rewrite nth_error_subst_context /= hnth /=. split; eauto.
      rewrite /= hb /=. f_equal.
      rewrite subst_inst. rewrite Nat.add_0_r.
      rewrite rename_inst.
      replace #|Γ''| with ((#|Γ''| - S n) + S n) at 2 by lia.
      set (k := S n).
      sigma. apply inst_ext.
      rewrite /rshiftk. rewrite (ren_shiftk (S n)).
      rewrite -shiftn_Upn - !Upn_Upn. intros i; lia_f_equal.
  - move: hnth.
    case: (nth_error_app_context Γ Γ' _) => // x' hnth hn' [=] eq; subst x'.
    * exfalso.
      revert subs hnth hb; generalize (n - #|Γ''|); clear.
      intros n subs; induction subs in n |- *; simpl => //.
      { now rewrite nth_error_nil //. }
      { destruct n; simpl.
        * intros [= <-] => //.
        * intros hnth. now specialize (IHsubs _ hnth). }
    * left; exists (n - #|Γ'|), decl.
      repeat split.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None //; try lia.
        unfold subst_compose.
        apply subs_lengthE in subs.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        simpl. len. unfold shiftk. lia_f_equal.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + rewrite -lift_renaming_0_rshift hb /=.
        f_equal. rewrite rename_inst. rewrite lift_renaming_spec shiftn0 ren_shiftk.
        apply inst_ext.
        apply subs_lengthE in subs.
        replace (S n) with ((S (n - #|Γ''|)) + #|Γ''|) by lia.
        rewrite -shiftk_compose subst_compose_assoc.
        rewrite shiftn_Upn -subst_compose_assoc.
        replace (S (n - #|Γ''|)) with ((S (n - #|Γ''|) - #|Γ'|) + #|Γ'|) by lia.
        rewrite -shiftk_compose !subst_compose_assoc.
        rewrite -(subst_compose_assoc _ _ (↑^#|Γ''|)).
        rewrite subst_consn_shiftn //.
        rewrite !shiftk_compose. intros i; lia_f_equal.
Qed.

Definition wt_cumulE {cf} Σ Γ := wt_cumul_pbE Cumul Σ Γ.
Definition wt_convE {cf} Σ Γ := wt_cumul_pbE Conv Σ Γ.

Notation " Σ ;;; Γ |-E t <= u ✓" := (wt_cumulE Σ Γ t u) (at level 50, Γ, t, u at next level).
Notation " Σ ;;; Γ |-E t = u ✓" := (wt_convE Σ Γ t u) (at level 50, Γ, t, u at next level).

Definition wt_cumul_cumE {cf} {Σ Γ T U} : Σ ;;; Γ |-E T <= U ✓ -> JoinE Σ Γ Cumul T U.
Proof. intros H. apply (wt_cumul_pbE_eq H). Defined.
Coercion wt_cumul_cumE : wt_cumulE >-> JoinE.

Definition wt_conv_convE {cf} {Σ Γ T U} : Σ ;;; Γ |-E T = U ✓ -> JoinE Σ Γ Conv T U.
Proof. intros H; apply (wt_cumul_pbE_eq H). Defined.
Coercion wt_conv_convE : wt_convE >-> JoinE.

Definition red1P_on_free_vars_rightE {cf} {P Σ} {wfΣ : wfE Σ} {Γ t v} : red1P P Σ Γ t v -> on_free_vars P v.
Proof.
  intros [onΓ [ont red]].
  eapply red1_on_free_vars_cb; tea.
Qed.

Lemma isType_wf_localE {cf:checker_flags} {Σ Γ T} : isTypeE Σ Γ T -> wf_localE Σ Γ.
Proof.
  intros (_ & s & Hs & _).
  now eapply typingE_wf_local.
Qed.

(** The substituted terms of a typed substitution are open in its context. *)
Lemma subsletE_open_terms {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ s Δ} :
  subsletE Σ Γ s Δ -> forallb (is_open_term Γ) s.
Proof.
  induction 1; cbn; [reflexivity| |]; rewrite IHX andb_true_r;
    eapply subject_is_open_termE; eassumption.
Qed.

Section SubstitutionLemmasE.
  Context {cf} {Σ} {wfΣ : wfE Σ}.

  Lemma isType_closedPTE Γ T : isTypeE Σ Γ T -> on_free_vars (closedP #|Γ| xpredT) T.
  Proof using wfΣ.
    move/isType_closedE/(closedn_on_free_vars (P:=xpred0)).
    now rewrite shiftnPF_closedPT.
  Qed.

  Lemma substitution_red1E {Γ Γ' Γ'' s M N} :
    subsE Σ Γ s Γ' -> wf_localE Σ Γ ->
    is_open_term (Γ,,, Γ',,, Γ'') M ->
    red1 Σ (Γ ,,, Γ' ,,, Γ'') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
  Proof using wfΣ.
    intros Hs wfΓ H.
    rewrite !subst_inst.
    eapply red1_inst_cb; eauto.
    now eapply subs_usubstE.
  Qed.

  Lemma substitution_let_redE {Γ Δ Γ' s M N} :
    subsletE Σ Γ s Δ ->
    is_open_term (Γ,,, Δ,,, Γ') M ->
    red1 Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs wfΓ H.
    rewrite !subst_inst.
    eapply red1_inst_cb; eauto.
    now eapply (subslet_usubst (subslet_untyped_subsletE _ _ _ _ Hs)).
  Qed.

  Lemma substitution_untyped_let_redE {Γ Δ Γ' s M N} :
    untyped_subslet Γ s Δ ->
    is_open_term (Γ,,, Δ,,, Γ') M ->
    red1 Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ. intros; eapply substitution_untyped_let_red_cb; tea; typeclasses eauto. Qed.

  Lemma substitution_untyped_redE {Γ Δ Γ' s M N} :
    untyped_subslet Γ s Δ ->
    is_open_term (Γ ,,, Δ ,,, Γ') M ->
    on_ctx_free_vars (shiftnP #|Γ,,, Δ,,, Γ'| xpred0) (Γ,,, Δ,,, Γ') ->
    red Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ. intros; eapply substitution_untyped_red_cb; tea; typeclasses eauto. Qed.

  Lemma substitution_redE {Γ Δ Γ' s M N} :
    subsletE Σ Γ s Δ -> wf_localE Σ Γ ->
    is_open_term (Γ ,,, Δ ,,, Γ') M ->
    on_ctx_free_vars (shiftnP #|Γ,,, Δ,,, Γ'| xpred0) (Γ,,, Δ,,, Γ') ->
    red Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs Hl onM onctx Hred. induction Hred; trea.
    - eapply substitution_let_redE; eauto.
    - etransitivity; [eapply IHHred1|eapply IHHred2]; tea.
      eapply PCUICClosedTyp.red_on_free_vars_cb in Hred1; eauto.
  Qed.

  Lemma red_redE {P Γ Δ Γ' s s' b} :
    on_ctx_free_vars P (Γ ,,, Δ ,,, Γ') ->
    on_free_vars P b ->
    All2 (red Σ Γ) s s' ->
    All (on_free_vars (addnP (#|Γ'| + #|Δ|) P)) s ->
    untyped_subslet Γ s Δ ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
  Proof using wfΣ. intros; eapply red_red_cb; tea; typeclasses eauto. Qed.

  Lemma untyped_substitution_redE {Γ Δ Γ' s M N} :
    untyped_subslet Γ s Δ ->
    on_ctx_free_vars (shiftnP #|Γ,,, Δ,,, Γ'| xpred0) (Γ ,,, Δ ,,, Γ') ->
    is_open_term (Γ ,,, Δ ,,, Γ') M ->
    red Σ (Γ ,,, Δ ,,, Γ') M N ->
    red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
  Proof using wfΣ.
    intros Hs onΓ onM Hred. induction Hred; trea.
    - eapply substitution_untyped_let_redE; eauto.
    - etransitivity; [eapply IHHred1|eapply IHHred2]; eauto.
      eapply PCUICClosedTyp.red_on_free_vars_cb in Hred1; tea.
  Qed.

  (** The cumulativity relation is substitutive. Base inducts on the reductions of
      [cumulAlgo]; here the join is transported by [JoinE_map] along [subst s]. *)

  Lemma substitution_untyped_cumulE {Γ Γ' Γ'' s M N} :
    untyped_subslet Γ s Γ' ->
    is_open_term (Γ ,,, Γ' ,,, Γ'') M ->
    is_open_term (Γ ,,, Γ' ,,, Γ'') N ->
    on_ctx_free_vars (shiftnP #|Γ ,,, Γ' ,,, Γ''| xpred0) (Γ ,,, Γ' ,,, Γ'') ->
    JoinE Σ (Γ ,,, Γ' ,,, Γ'') Cumul M N ->
    JoinE Σ (Γ ,,, subst_context s 0 Γ'') Cumul (subst s #|Γ''| M) (subst s #|Γ''| N).
  Proof using wfΣ.
    intros Hs onM onN onΓ h.
    have hΓ : is_closed_context (Γ ,,, Γ' ,,, Γ'').
    { by rewrite on_free_vars_ctx_on_ctx_free_vars in onΓ. }
    eapply (JoinE_map Σ Σ _ (Γ ,,, Γ' ,,, Γ'') _ (subst s #|Γ''|)); try eassumption.
    - intros x y hx r. exact (substitution_untyped_let_redE Hs hx r).
    - intros x y e. exact (eta1_subst_step s x y e _).
    - intros x y e. rewrite !canon_subst. now rewrite e.
    - intros x y e. rewrite !canon_subst. apply finst_subst. exact (RF_canon Σ _ _ _ _ e).
  Qed.

  Lemma substitution_cumul0E {Γ na t u u' a} :
    on_ctx_free_vars (shiftnP #|Γ ,, vass na t| xpred0) (Γ ,, vass na t) ->
    is_open_term (Γ ,, vass na t) u ->
    is_open_term (Γ ,, vass na t) u' ->
    JoinE Σ (Γ ,, vass na t) Cumul u u' ->
    JoinE Σ Γ Cumul (subst10 a u) (subst10 a u').
  Proof using wfΣ.
    move=> onΓ onu onu' Hu.
    pose proof (@substitution_untyped_cumulE Γ [vass na t] [] [a] u u').
    forward X.
    { constructor. constructor. }
    simpl in X. now apply X.
  Qed.

  Lemma substitution_cumul_letE {Γ na t ty u u'} :
  on_ctx_free_vars (shiftnP #|Γ ,, vdef na t ty| xpred0) (Γ ,, vdef na t ty) ->
  is_open_term (Γ ,, vdef na t ty) u ->
  is_open_term (Γ ,, vdef na t ty) u' ->
  JoinE Σ (Γ ,, vdef na t ty) Cumul u u' ->
    JoinE Σ Γ Cumul (subst10 t u) (subst10 t u').
  Proof using wfΣ.
    move=> onΓ onu onu' Hu.
    pose proof (@substitution_untyped_cumulE Γ [vdef na t ty] [] [t] u u').
    forward X.
    { rewrite - {1}(subst_empty 0 t). constructor. constructor. }
    simpl in X. now apply X.
  Qed.

  Lemma usubst_well_substE {Γ σ Δ} :
    usubst Γ σ Δ ->
    (forall x decl, nth_error Γ x = Some decl ->
      Σ ;;; Δ |-E σ x : (decl.(decl_type)).[↑^(S x) ∘s σ]) ->
    well_substE Σ Γ σ Δ.
  Proof using Type.
    intros us hty. split; eauto.
    intros x decl hnth. specialize (hty x decl hnth). now sigma.
  Qed.

  Lemma subslet_well_substE {Γ Γ' s Δ} :
    subsletE Σ Γ s Γ' ->
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ->
    well_substE Σ (Γ ,,, Γ' ,,, Δ) (⇑^#|Δ| (s ⋅n ids)) (Γ ,,, subst_context s 0 Δ).
  Proof using wfΣ.
    intros hs hsΔ.
    apply usubst_well_substE.
    * apply (subslet_usubst (subslet_untyped_subsletE _ _ _ _ hs)).
    * intros x decl.
      case: nth_error_app_context => //.
      { intros d hnth hn [= ->].
        rewrite {1}Upn_eq subst_consn_lt; len => //. rewrite /subst_fn.
        rewrite idsn_lt //.
        eapply meta_convE.
        - econstructor; auto.
          rewrite nth_error_app_lt; len => //.
          now rewrite nth_error_subst_context hnth.
        - rewrite /subst_decl. simpl.
        sigma. rewrite -shiftk_shift -subst_compose_assoc -shiftk_shift.
          rewrite subst_shift_comm.
          rewrite -subst_fn_subst_consn. lia_f_equal. }
      { intros n hnth; len; intros hd [= ->].
        pose proof (subslet_lengthE hs).
        move: hnth; case: nth_error_app_context => //.
        * intros n hnth hx [= ->].
          rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
          rewrite subst_consn_compose.
          rewrite subst_consn_lt; len; try lia.
          unfold subst_fn. rewrite nth_error_map.
          destruct (subslet_nth_errorE hs hnth) as [t [hnths [hty hb]]].
          rewrite hnths /=. sigma in hty.
          eapply meta_convE in hty.
          2:now rewrite skipn_subst ?Upn_0; try lia.
          eapply (shift_typingE (Δ := subst_context s 0 Δ)) in hty.
          2:tas.
          2:now len.
          rewrite inst_assoc in hty.
          rewrite Upn_eq.
          eapply meta_convE; eauto.
          eapply inst_ext.
          rewrite (shift_subst_consn_ge (S x)); len; try lia.
          rewrite subst_compose_assoc.
          now replace (S x - #|Δ|) with (S (x - #|Δ|)) by lia.
        * intros n hnth hn [= ->].
          eapply meta_conv_allE.
          2:reflexivity.
          2:{ rewrite Upn_subst_consn_ge; try lia. rewrite compose_ids_l.
              instantiate (1 := tRel (x - #|s|)).
              rewrite /shiftk. lia_f_equal. }
          2:{ econstructor; eauto. }
          eapply meta_convE.
          { econstructor; tas.
            rewrite nth_error_app_context_ge; len; try lia.
            rewrite H. erewrite <- hnth. lia_f_equal. }
          rewrite lift0_inst.
          rewrite Upn_eq.
          rewrite shift_subst_consn_ge; len; try lia.
          rewrite subst_consn_compose shift_subst_consn_ge; len; try lia.
          rewrite H. rewrite shiftk_compose. lia_f_equal.
      }
  Qed.

  Lemma All_local_env_instE {Γ0 Γ' Δ s} :
    All_local_env (fun Γ j =>
      forall (Δ : PCUICEnvironment.context) (σ : nat -> term),
      wf_localE Σ Δ -> well_substE Σ Γ σ Δ ->
      (lift_typing0 (fun t T => Σ;;; Δ |-E t.[σ] : T.[σ])) j)
      (Γ0,,, Γ',,, Δ) ->
    wf_localE Σ Γ0 ->
    subsletE Σ Γ0 s Γ' ->
    wf_localE Σ (Γ0,,, subst_context s 0 Δ).
  Proof using wfΣ.
    intros HΓ HΓ0 sub.
    rewrite subst_context_inst_context.
    eapply (wf_local_app_instE _ (Γ0 ,,, Γ')); eauto.
    * now eapply All_local_env_app_inv in HΓ as [].
    * eapply (subslet_well_substE (Δ:=[])) in sub;
      rewrite ?subst_context_nil in sub |- *.
      + apply sub.
      + pcuicfo.
  Qed.
End SubstitutionLemmasE.

(* The copied proof below uses the default goal selector of its base file. *)
Set Default Goal Selector "1".

(** The twin of [EnvironmentTyping]'s [on_wf_global_env_impl] (functoriality of
    global environment typing, with the well-formed environment folded in), at
    [cumulSpecE0] and [typingE]; the proof of [substitution_propE] needs it. *)
Lemma on_wf_global_env_implE `{checker_flags} {Σ : global_env} {wfΣ : on_global_env cumulSpecE0 (lift_typing typingE) Σ} P Q :
  (forall Σ Γ j, on_global_env cumulSpecE0 (lift_typing typingE) Σ.1 ->
      on_global_env cumulSpecE0 P Σ.1 ->
      on_global_env cumulSpecE0 Q Σ.1 ->
      P Σ Γ j -> Q Σ Γ j) ->
  on_global_env cumulSpecE0 P Σ -> on_global_env cumulSpecE0 Q Σ.
Proof.
  intros X [cu [wfr IH]]. destruct wfΣ as [_ [_ wfΣ]].
  split; [assumption|]. split; [assumption|].
  revert cu wfr IH wfΣ; generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear Σ.
  induction g; intros; auto. constructor; auto.
  depelim IH. depelim wfΣ.
  specialize (IHg cu wfr IH wfΣ).
  constructor; auto.
  destruct o. constructor; auto.
  match goal with h : on_global_decl cumulSpecE0 P _ _ _ |- _ =>
    eapply on_global_decl_impl_simple; [|exact (cu, (wfr, IH))|exact h] end.
  intros Γ j HP Hj. eapply X; tea.
  - split; [exact cu|split; [exact wfr|exact wfΣ]].
  - split; [exact cu|split; [exact wfr|exact IHg]].
Qed.

Set Default Goal Selector "!".

Theorem substitution_propE {cf} : env_propE
  (fun Σ Γ0 t T =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subsletE Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ->
    Σ ;;; Γ ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T)
  (fun Σ Γ0 j =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subsletE Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ->
    lift_typing0 (fun t T => Σ ;;; Γ ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T) j)
  (fun Σ Γ0 =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subsletE Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_localE Σ (Γ ,,, subst_context s 0 Δ)).
Proof.
  intros Σ wfΣ Γ t T HT.
  pose proof (type_instE Σ wfΣ Γ t T HT) as [HΣ [HΓ HTy]].
  intuition auto.
  3:{
    subst Γ.
    rewrite !subst_inst. eapply HTy => //.
    eapply subslet_well_substE; eauto. }
  2:{ subst Γ.
      eapply typingE_wf_local in HT.
      eapply All_local_env_app_inv in HT as [HΓ0 _].
      eapply All_local_env_app_inv in HΓ0 as [HΓ0 _].
      eapply All_local_env_instE; eauto. }
  unshelve eapply on_wf_global_env_implE ; tea.
  clear. intros * HΣ HP HQ Hty.
  intros. subst Γ.
  unshelve eapply lift_typing_impl with (1 := Hty _ _ X _) => [||t T HT].
  3: rewrite !subst_inst; eapply HT => //.
  now unshelve eapply subslet_well_substE.
Qed.

Corollary substitutionE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s Δ t T} :
  subsletE Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |-E t : T ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros Hs Ht.
  eapply (env_propE_typing substitution_propE); trea.
  eapply (env_propE_wf_local substitution_propE); trea.
  now eapply typingE_wf_local in Ht.
Qed.

Corollary lift_typing_substitutionE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s Δ} j :
  subsletE Σ Γ s Γ' ->
  lift_typing typingE Σ (Γ ,,, Γ' ,,, Δ) j ->
  lift_typing typingE Σ (Γ ,,, subst_context s 0 Δ) (judgment_map (subst s #|Δ|) j).
Proof.
  intros Hs HT.
  apply lift_typing_f_impl with (1 := HT) => // ?? Ht.
  eapply substitutionE in Ht; tea.
Qed.

Corollary lift_typing_substE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s} j :
  subsletE Σ Γ s Γ' ->
  lift_typing typingE Σ (Γ ,,, Γ') j ->
  lift_typing typingE Σ Γ (judgment_map (subst0 s) j).
Proof.
  now apply @lift_typing_substitutionE with (Δ := []).
Qed.

Corollary isType_substitutionE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s Δ T} :
  subsletE Σ Γ s Γ' ->
  isTypeE Σ (Γ ,,, Γ' ,,, Δ) T ->
  isTypeE Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T).
Proof.
  apply lift_typing_substitutionE.
Qed.

Corollary isType_substE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ s T} :
  subsletE Σ Γ s Δ ->
  isTypeE Σ (Γ ,,, Δ) T ->
  isTypeE Σ Γ (subst0 s T).
Proof.
  apply lift_typing_substE.
Qed.

Corollary isTypeRel_substitutionE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s Δ T r} :
  subsletE Σ Γ s Γ' ->
  isTypeRelE Σ (Γ ,,, Γ' ,,, Δ) T r ->
  isTypeRelE Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T) r.
Proof.
  apply lift_typing_substitutionE.
Qed.

Corollary isTypeRel_substE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ s T r} :
  subsletE Σ Γ s Δ ->
  isTypeRelE Σ (Γ ,,, Δ) T r ->
  isTypeRelE Σ Γ (subst0 s T) r.
Proof.
  apply lift_typing_substE.
Qed.

Corollary substitution_wf_localE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s Δ} :
  subsletE Σ Γ s Γ' ->
  wf_localE Σ (Γ ,,, Γ' ,,, Δ) ->
  wf_localE Σ (Γ ,,, subst_context s 0 Δ).
Proof.
  intros Hs Ht.
  eapply (env_propE_wf_local substitution_propE); trea.
Qed.

Lemma substitution0E {cf} {Σ} {wfΣ : wfE Σ} {Γ n u U t T} :
  Σ ;;; Γ ,, vass n U |-E t : T -> Σ ;;; Γ |-E u : U ->
  Σ ;;; Γ |-E t {0 := u} : T {0 := u}.
Proof.
  intros Ht Hu.
  assert (wfΓ : wf_localE Σ Γ).
  { apply typingE_wf_local in Hu; eauto. }
  eapply (substitutionE (Γ' := [vass n U]) (Δ := [])); tea.
  now eapply subslet_ass_tipE.
Qed.

Lemma substitution_letE {cf} {Σ} {wfΣ : wfE Σ} {Γ n u U t T} :
  Σ ;;; Γ ,, vdef n u U |-E t : T ->
  Σ ;;; Γ |-E t {0 := u} : T {0 := u}.
Proof.
  intros Ht.
  assert ((wf_localE Σ Γ) * (Σ ;;; Γ |-E u : U)%type) as [wfΓ tyu].
  { apply typingE_wf_local in Ht; eauto with wf.
    depelim Ht; split; tas. now destruct l as (? & _).
  }
  eapply (substitutionE (Γ':=[vdef n u U]) (Δ := [])); tea.
  now eapply subslet_def_tipE.
Qed.

(** Substitution into a *well-typed* cumulativity/conversion derivation: the twin
    of base [substitution_wt_cumul_pb], on the route of the header. *)

Lemma substitution_wt_cumul_pbE {cf} {Σ} {wfΣ : wfE Σ} {pb Γ Γ' Γ'' s M N} :
  subsletE Σ Γ s Γ' ->
  wt_cumul_pbE pb Σ (Γ ,,, Γ' ,,, Γ'') M N ->
  wt_cumul_pbE pb Σ (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  move=> Hs wteq; split.
  + eapply (isType_substitutionE Hs), wteq.
  + eapply (isType_substitutionE Hs), wteq.
  + apply wsE_join.
    apply (untyped_substitution_ws_cumul_pbE (subslet_untyped_subsletE _ _ _ _ Hs)).
    * exact (subsletE_open_terms Hs).
    * exact (wt_cumul_pbE_ws_cumul_pbE wteq).
Qed.

Lemma substitution_cumulE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' Γ'' s M N} :
  subsletE Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |-E M <= N ✓ ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |-E  subst s #|Γ''| M <= subst s #|Γ''| N ✓.
Proof. apply substitution_wt_cumul_pbE. Qed.

Lemma substitution_convE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' Γ'' s M N} :
  subsletE Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |-E M = N ✓ ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |-E  subst s #|Γ''| M = subst s #|Γ''| N ✓.
Proof. apply substitution_wt_cumul_pbE. Qed.

(** ** The base lemma whose E form is false: [wt_cumul_pb_equalityP]

  Base [wt_cumul_pb_equalityP] turns a well-typed cumulativity into [cumulP], a
  closure of one-step reductions and [compare_term], which has no η step. Over the
  η relation that is false. Witness, in the empty environment and the context
  [F : Prop → Prop, G : (Prop → Prop) → Prop]: the types [G (λy:Prop. F y)] and
  [G F] are related (one η step in the argument), both are normal ([F] and [G] are
  assumptions), and [compare_term] never relates a λ to a variable. Both have type
  [Prop] over [typingE] ([wc_witness_typed]). The refutation stays registered. Its
  only base consumer, [substitution_wt_cumul_pb], is proved above on another
  route. *)
Section EqualityPFalse.

  #[local] Existing Instance default_checker_flags.

  Definition wc_G_ty : term := tProd c1b_na rf_F (tSort sProp).
  Definition wc_Γ : context := [vass c1b_na wc_G_ty; vass c1b_na rf_F].
  Definition wc_eta_F : term := tLambda c1b_na (tSort sProp) (tApp (tRel 2) (tRel 0)).
  Definition wc_T : term := tApp (tRel 0) wc_eta_F.
  Definition wc_U : term := tApp (tRel 0) (tRel 1).

  Lemma wc_Rel_normal Σ (Γ : context) n v :
    option_map decl_body (nth_error Γ n) = Some None -> red1 Σ Γ (tRel n) v -> False.
  Proof.
    intros hn H. inv_red H.
    match goal with e : option_map decl_body _ = Some (Some _) |- _ => rewrite hn in e; discriminate e end.
  Qed.

  Lemma wc_eta_body_normal Σ v : red1 Σ (wc_Γ ,, vass c1b_na (tSort sProp)) (tApp (tRel 2) (tRel 0)) v -> False.
  Proof.
    intros H. inv_red H.
    - exact (wc_Rel_normal _ (wc_Γ ,, vass c1b_na (tSort sProp)) 2 _ eq_refl ltac:(eassumption)).
    - eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma wc_eta_F_normal Σ v : red1 Σ wc_Γ wc_eta_F v -> False.
  Proof.
    apply red_normal_lam; [intros w; apply red_normal_Sort|intros w; apply wc_eta_body_normal].
  Qed.

  Lemma wc_T_normal Σ v : red1 Σ wc_Γ wc_T v -> False.
  Proof.
    intros H. inv_red H.
    - eapply red_normal_Rel0; eassumption.
    - eapply wc_eta_F_normal; eassumption.
  Qed.

  Lemma wc_U_normal Σ v : red1 Σ wc_Γ wc_U v -> False.
  Proof.
    intros H. inv_red H.
    - eapply red_normal_Rel0; eassumption.
    - exact (wc_Rel_normal _ wc_Γ 1 _ eq_refl ltac:(eassumption)).
  Qed.

  Lemma wc_not_compare Σ φ pb : compare_term Σ φ pb wc_T wc_U -> False.
  Proof.
    intros c. depelim c.
    repeat match goal with h : eq_term_upto_univ_napp _ _ _ _ _ _ _ |- _ => depelim h end.
  Qed.

  (** The witness is typable. *)
  Lemma wc_G_ty_typed (Γ : context) : wf_localE rf_Σ Γ ->
    rf_Σ ;;; Γ |-E wc_G_ty :
      tSort (Sort.sort_of_product (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (Sort.super sProp)).
  Proof.
    intros h. unfold wc_G_ty. apply typeE_Prod.
    - split; [exact tt|]. eexists. split; [exact (rf_F_typed Γ h)|]. split; reflexivity.
    - apply rf_P_typed. apply localenv_cons_abs; [exact h|].
      split; [exact tt|]. eexists. split; [exact (rf_F_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma wc_wf_Γ : wf_localE rf_Σ wc_Γ.
  Proof.
    apply localenv_cons_abs; [exact rf_wf_Γ|].
    split; [exact tt|]. eexists. split; [exact (wc_G_ty_typed rf_Γ rf_wf_Γ)|]. split; [exact I|reflexivity].
  Qed.

  Lemma wc_wf_Γy : wf_localE rf_Σ (wc_Γ ,, vass c1b_na (tSort sProp)).
  Proof. apply localenv_cons_abs; [exact wc_wf_Γ|exact (rf_P_vass wc_Γ wc_wf_Γ)]. Qed.

  Lemma wc_eta_F_typed : rf_Σ ;;; wc_Γ |-E wc_eta_F : rf_F.
  Proof.
    unfold wc_eta_F, rf_F. apply typeE_Lambda; [exact (rf_P_vass wc_Γ wc_wf_Γ)|].
    apply (typeE_App _ _ (tRel 2) c1b_na (tSort sProp) (tSort sProp)
             (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0)).
    - exact (rf_F_typed _ wc_wf_Γy).
    - exact (typeE_Rel _ _ 2 (vass c1b_na rf_F) wc_wf_Γy eq_refl).
    - exact (typeE_Rel _ _ 0 (vass c1b_na (tSort sProp)) wc_wf_Γy eq_refl).
  Qed.

  Lemma wc_app_typed u : rf_Σ ;;; wc_Γ |-E u : rf_F -> rf_Σ ;;; wc_Γ |-E tApp (tRel 0) u : tSort sProp.
  Proof.
    intros hu.
    exact (typeE_App _ _ (tRel 0) c1b_na rf_F (tSort sProp) _ u (wc_G_ty_typed wc_Γ wc_wf_Γ)
             (typeE_Rel _ _ 0 (vass c1b_na wc_G_ty) wc_wf_Γ eq_refl) hu).
  Qed.

  Lemma wc_T_typed : rf_Σ ;;; wc_Γ |-E wc_T : tSort sProp.
  Proof. exact (wc_app_typed _ wc_eta_F_typed). Qed.

  Lemma wc_U_typed : rf_Σ ;;; wc_Γ |-E wc_U : tSort sProp.
  Proof. exact (wc_app_typed _ (typeE_Rel _ _ 1 (vass c1b_na rf_F) wc_wf_Γ eq_refl)). Qed.

  (** In an environment that meets the refuted statement's premise [wf Σ] (and
      [wfE Σ]), [F : Prop → Prop, G : (Prop → Prop) → Prop] is a well-formed
      context, and [G (λy:Prop. F y)] and [G F] both have type [Prop] in it. *)
  Lemma wc_witness_typed :
    [× wf rf_Σ, wfE rf_Σ, wf_localE rf_Σ wc_Γ,
       rf_Σ ;;; wc_Γ |-E wc_T : tSort sProp & rf_Σ ;;; wc_Γ |-E wc_U : tSort sProp].
  Proof.
    split; [exact (@wf_empty_global_env default_checker_flags)
           |exact (wf_incl_E (@wf_empty_global_env default_checker_flags))
           |exact wc_wf_Γ|exact wc_T_typed|exact wc_U_typed].
  Qed.

  Definition wc_wfE : wfE rf_Σ := wf_incl_E (@wf_empty_global_env default_checker_flags).

  Lemma wc_isType (t : term) : rf_Σ ;;; wc_Γ |-E t : tSort sProp -> isTypeE rf_Σ wc_Γ t.
  Proof. intros h. split; [exact tt|]. exists sProp. split; [exact h|]. split; exact I. Qed.

  Lemma wc_spec : rf_Σ ;;; wc_Γ ⊢ wc_T ≤sE[Conv] wc_U.
  Proof.
    unfold wc_T, wc_U. apply cumulE_App; [apply cumulE_Refl|].
    unfold wc_eta_F. apply cumul_eta_l. apply cumulE_Refl.
  Qed.

  Lemma wc_premise : wt_cumul_pbE Conv rf_Σ wc_Γ wc_T wc_U.
  Proof.
    constructor; [exact (wc_isType _ wc_T_typed)|exact (wc_isType _ wc_U_typed)|].
    apply (wsE_join (cf := default_checker_flags)).
    apply (into_ws_cumul_pbE_spec (wfΣ := @wfE_ClosedBodies _ rf_Σ wc_wfE) wc_spec);
      [exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_wf_Γ)
      |exact (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_T_typed)
      |exact (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_U_typed)].
  Qed.

  Lemma wc_no_cumulP P : cumulP Conv rf_Σ P wc_Γ wc_T wc_U -> False.
  Proof.
    intros H. inversion H; subst.
    - eapply wc_not_compare; eassumption.
    - match goal with h : red1P _ _ _ wc_T _ |- _ => exact (wc_T_normal _ _ (red1P_red1 h)) end.
    - match goal with h : red1P _ _ _ wc_U _ |- _ => exact (wc_U_normal _ _ (red1P_red1 h)) end.
  Qed.

End EqualityPFalse.

(** **Refuted:** base [wt_cumul_pb_equalityP] over [wt_cumul_pbE], even under the
    stronger premise [wf Σ]. *)
Theorem wt_cumul_pbE_equalityP_false_wf :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) pb (Γ : context) T U,
     wt_cumul_pbE pb Σ Γ T U -> cumulP pb Σ (closedP #|Γ| xpredT) Γ T U) -> False.
Proof.
  intros H.
  exact (wc_no_cumulP _ (H default_checker_flags rf_Σ (@wf_empty_global_env default_checker_flags)
                           Conv wc_Γ wc_T wc_U wc_premise)).
Qed.

(** **Refuted:** base [wt_cumul_pb_equalityP] with only [wt_cumul_pb] →
    [wt_cumul_pbE] and [wf] → [wfE] (base's section variables explicit). *)
Theorem wt_cumul_pbE_equalityP_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) pb (Γ : context) T U,
     wt_cumul_pbE pb Σ Γ T U -> cumulP pb Σ (closedP #|Γ| xpredT) Γ T U) -> False.
Proof.
  intros H. apply wt_cumul_pbE_equalityP_false_wf.
  intros cf Σ wfΣ. exact (H cf Σ (wf_incl_E wfΣ)).
Qed.
