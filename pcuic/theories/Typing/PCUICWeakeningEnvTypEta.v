(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, T0 copy 1: [Typing/PCUICWeakeningEnvTyp.v] over [typingE]

  Base file at trunk 0729d50e, copied over [typingE], [wfE], [wf_localE] and
  [cumulSpecE0] (lanes/eta/t0-plan.md §3 row 1); every lemma takes the suffix [E].
  Environment weakening of the conversion rule goes through
  [weakening_env_cumulSpecE] ([PCUICCumulativitySpecEtaClosure], P2). The proofs
  are base's. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICReduction PCUICCumulativity PCUICTyping PCUICGuardCondition
  PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure
  PCUICTypingEta PCUICTypingEtaInd.
From Equations Require Import Equations.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

(** Hypothesis names for [typingE]/[wfE], as [PCUICTyping.my_rename_hyp] gives for
    [typing]/[wf]: the copied proofs refer to them. *)
Ltac my_rename_hypE h th :=
  match th with
  | (wfE ?E) => fresh "wf" E
  | (wfE (fst_ctx ?E)) => fresh "wf" E
  | (wfE _) => fresh "wf"
  | (typingE _ _ ?t _) => fresh "type" t
  | (@cumulSpecE _ _ _ ?t _) => fresh "cumul" t
  | (@convSpecE _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_sorting (@typingE _) _ _) ?G) => fresh "wf" G
  | (All_local_env (lift_sorting (@typingE _) _) _) => fresh "wf"
  | context [typingE _ _ (_ ?t) _] => fresh "IH" t
  | _ => PCUICWeakeningEnvTyp.my_rename_hyp h th
  end.

#[local] Ltac rename_hyp h ht ::= my_rename_hypE h ht.

Lemma extends_wf_local_genE `{cf : checker_flags} R Σ Γ (wfΓ : wf_localE Σ Γ) :
  All_local_env_over (typingE Σ)
      (fun Γ0 wfΓ (t T : term) ty =>
         forall Σ' : global_env,
           wfE Σ' ->
           R Σ Σ' ->
           (Σ', Σ.2);;; Γ0 |-E t : T
      ) Γ wfΓ ->
    forall Σ' : global_env, wfE Σ' -> R Σ Σ' -> wf_localE (Σ', Σ.2) Γ.
Proof.
  intros X0 Σ' H0.
  induction X0 in H0 |- *; try econstructor; simpl in *; intuition auto.
  - apply lift_sorting_it_impl with tu => //. intro; eauto.
  - apply lift_sorting_it_impl with tu => /=. all: intro; eauto.
Qed.

Definition extends_wf_localE `{cf : checker_flags} := extends_wf_local_genE extends.
Definition extends_decls_wf_localE `{cf : checker_flags} := extends_wf_local_genE extends_decls.
Definition extends_strictly_on_decls_wf_localE `{cf : checker_flags} := extends_wf_local_genE extends_strictly_on_decls.
Definition strictly_extends_decls_wf_localE `{cf : checker_flags} := extends_wf_local_genE strictly_extends_decls.
#[global]
Hint Resolve extends_wf_localE extends_decls_wf_localE extends_strictly_on_decls_wf_localE strictly_extends_decls_wf_localE : extends.

Lemma extends_check_recursivity_kindE `{cf : checker_flags} Σ ind k Σ' : extends Σ Σ' -> wfE Σ' ->
  check_recursivity_kind (lookup_env Σ) ind k -> check_recursivity_kind (lookup_env Σ') ind k.
Proof.
  intros ext wfΣ'.
  rewrite /check_recursivity_kind.
  destruct lookup_env eqn:Heq => //.
  eapply extends_lookup in Heq; eauto.
  now rewrite Heq.
Qed.

Lemma extends_mfix_on_indE `{cf : checker_flags} (Σ : global_env_ext) Σ' Γ check kind mfix :
  extends Σ.1 Σ' -> wfE Σ' ->
  mfix_on_ind check (conv_witnessE Σ Γ) (fun mind => check_recursivity_kind (lookup_env Σ) mind kind) mfix ->
  mfix_on_ind check (conv_witnessE (Σ', Σ.2) Γ)
    (fun mind => check_recursivity_kind (lookup_env Σ') mind kind) mfix.
Proof.
  destruct Σ as [Σ φ].
  intros ext wfΣ' h.
  refine (mfix_on_ind_All2 _ _ h).
  - apply All2_refl. intros d m [ty [hc [hop hconv]]].
    refine (ty; (hc, (hop, _))).
    eapply weakening_env_convSpecE; eauto.
  - intros m hm. eapply extends_check_recursivity_kindE; tea.
Qed.
#[global]
Hint Resolve extends_mfix_on_indE : extends.

Lemma extends_primitive_constantE Σ Σ' p t :
  extends Σ Σ' ->
  primitive_constant Σ p = Some t ->
  primitive_constant Σ' p = Some t.
Proof.
  intros [_ _ ext].
  unfold primitive_constant.
  case: ext => o [] o' [] o'' [] o''' _.
  destruct p => //.
  - intros hr. now rewrite hr in o; depelim o.
  - intros hr. now rewrite hr in o'; depelim o'.
  - intros hr. now rewrite hr in o''; depelim o''.
  - intros hr. now rewrite hr in o'''; depelim o'''.
Qed.
Local Hint Resolve extends_primitive_constantE : extends.

Lemma weakening_envE `{checker_flags} :
  env_propE (fun Σ Γ t T =>
              forall Σ', wfE Σ -> wfE Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |-E t : T)
           (fun Σ Γ j =>
              forall Σ', wfE Σ -> wfE Σ' -> extends Σ.1 Σ' -> lift_typing typingE (Σ', Σ.2) Γ j)
           (fun Σ Γ =>
             forall Σ', wfE Σ -> wfE Σ' -> extends Σ.1 Σ' -> wf_localE (Σ', Σ.2) Γ).
Proof.
  apply typingE_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - apply lift_typing_impl with (1 := X) => t T [] _ IH //.
    now apply IH.

  - apply All_local_env_impl with (1 := X0) => Γ' j Hj.
    now apply Hj.
  - econstructor; eauto 2 with extends.
    now apply extends_wf_sort.
  - econstructor; eauto 2 with extends. all: econstructor; eauto 2 with extends.
    * revert X5. clear -Σ' wf0 wfΣ' extΣ.
      induction 1; constructor; try destruct t0; eauto with extends.
    * close_Forall. intros; intuition eauto with extends.
  - assert (wffix' : wf_fixpointE (Σ', Σ.2) Γ mfix).
    { match goal with h : wf_fixpointE _ _ _ |- _ => destruct h as (? & ? & ?) end.
      split; [|split]; tas. now eapply extends_mfix_on_indE. }
    econstructor; eauto with extends.
    + specialize (forall_Σ' _ wf0 wfΣ' extΣ).
      now apply All_local_env_app_inv in forall_Σ'.
    + eapply fix_guard_extends; eauto.
    + eapply (All_impl X1); intros d X. now apply X.
    + eapply (All_impl X3); intros d X. now apply X.
  - assert (wfcofix' : wf_cofixpointE (Σ', Σ.2) Γ mfix) by (eapply extends_mfix_on_indE; tea).
    econstructor; eauto with extends.
    + specialize (forall_Σ' _ wf0 wfΣ' extΣ).
      now apply All_local_env_app_inv in forall_Σ'.
    + eapply cofix_guard_extends; eauto.
    + eapply (All_impl X1); intros d X. now apply X.
    + eapply (All_impl X3); intros d X. now apply X.
  - econstructor; eauto with extends.
    destruct X1; constructor; eauto with extends.
    * now eapply extends_wf_universe.
    * solve_all.
  - econstructor. 1: eauto.
    + eapply forall_Σ'1; eauto.
    + destruct Σ as [Σ φ]. eapply weakening_env_cumulSpecE in cumulA; eauto.
Qed.

(** [R] must imply [extends_prim], not merely [extends] (standing condition
    D-1 in common/theories/Environment.v): the [arity_red] and positivity
    obligations below go through [weakening_env_whd_rel]. *)
Lemma weakening_on_global_decl_genE `{checker_flags} R P Σ Σ' φ kn decl :
  CRelationClasses.subrelation R extends_prim ->
  weaken_env_prop_gen cumulSpecE0 (lift_typing typingE) R P ->
  wfE Σ -> wfE Σ' -> R Σ Σ' ->
  on_global_decl cumulSpecE0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpecE0 P (Σ', φ) kn decl.
Proof.
  unfold weaken_env_prop_gen.
  intros HRext HPΣ wfΣ wfΣ' Hext.
  pose proof (HRext _ _ Hext) as hfr. pose proof (extends_prim_extends _ _ hfr) as hex.
  apply on_global_decl_impl_full; eauto.
  - reflexivity.
  - intros ????. eapply weakening_env_arity_red; eauto.
  - intros ?????. eapply weakening_env_cumulSpecE0; eauto.
  - intro. eapply (extends_wf_sort (Σ:=(Σ,φ)) Σ'); auto.
  - unfold check_constructors_smaller. intros ???.
    eapply Forall_impl; tea; cbn. intros.
    eapply Forall_impl; tea; simpl; intros.
    eapply leq_sort_subset; tea.
    apply weakening_env_global_ext_constraints; tea; eauto.
  - rewrite /on_variance. intros u l. destruct u => //.
    destruct l => //.
    intros [univs' [i [i' []]]]. exists univs', i, i'. split => //.
    all:eapply weakening_env_consistent_instance; tea; eauto.
  - intros ????. eapply weakening_env_positive_cstr; tea.
    all: try exact hfr.
Qed.

Definition weakening_on_global_declE `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> wfE Σ' -> extends_prim Σ Σ' ->
  on_global_decl cumulSpecE0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpecE0 P (Σ', φ) kn decl.
Proof.
  intros HP wfΣ wfΣ' ext.
  eapply (weakening_on_global_decl_genE extends_prim); try eassumption.
  - intros ?? h; exact h.
  - intros Σ0 Σ0' φ0 w w' [e _]. exact (HP Σ0 Σ0' φ0 w w' e).
Qed.
Lemma weakening_on_global_decl_extE `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> wfE Σ' -> extends_decls Σ Σ' ->
  on_global_decl cumulSpecE0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpecE0 P (Σ', φ) kn decl.
Proof. intro; eapply weakening_on_global_decl_genE; [ | eassumption ]; tc. Qed.
Lemma weakening_on_global_decl_strictly_extE `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> wfE Σ' -> strictly_extends_decls Σ Σ' ->
  on_global_decl cumulSpecE0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpecE0 P (Σ', φ) kn decl.
Proof. intro; eapply weakening_on_global_decl_genE; [ | eassumption ]; tc. Qed.

Import CRelationClasses CMorphisms.
Lemma weakening_env_gen_lookup_on_global_envE `{checker_flags} R P Σ Σ' c decl :
  subrelation R extends_prim ->
  subrelation strictly_extends_decls R ->
  Transitive R ->
  weaken_env_prop_gen cumulSpecE0 (lift_typing typingE) R P ->
  wfE Σ' -> wfE Σ -> R Σ Σ' -> on_global_env cumulSpecE0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpecE0 P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HRext1 HRext2 HTR HP wfΣ' wfΣ Hext HΣ.
  destruct HΣ as [onu [wfr onΣ]].
  destruct Σ as [univs Σ retro]; cbn in *.
  induction onΣ; simpl. 1: congruence.
  assert (HH: R {| universes := univs; declarations := Σ; retroknowledge := retro |} Σ'). {
    etransitivity; [ eapply HRext2 | exact Hext ].
    split; cbv [snoc]; cbn; auto.
    eexists [_]; cbn; reflexivity.
  }
  case: eqb_specT; intro eq; subst.
  - intros [= ->]. subst. destruct o.
    clear Hext; eapply weakening_on_global_decl_genE; [ .. | eassumption ]; eauto; [].
    destruct wfΣ as [? [? wfΣ]]; inversion wfΣ; subst; (split; [|split]); tea.
  - destruct o. apply IHonΣ; auto.
    destruct wfΣ as [? [? o0]]. split; [|split]; [ assumption | assumption | now depelim o0 ].
Qed.

Lemma weakening_env_lookup_on_global_envE `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ' -> wfE Σ -> extends_prim Σ Σ' -> on_global_env cumulSpecE0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpecE0 P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HP wfΣ' wfΣ ext.
  eapply (weakening_env_gen_lookup_on_global_envE extends_prim); try eassumption.
  - intros ?? h; exact h.
  - exact _.
  - exact _.
  - intros Σ0 Σ0' φ0 w w' [e _]. exact (HP Σ0 Σ0' φ0 w w' e).
Qed.
Lemma weakening_env_decls_lookup_on_global_envE `{checker_flags} P Σ Σ' c decl :
  weaken_env_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ' -> wfE Σ -> extends_decls Σ Σ' -> on_global_env cumulSpecE0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpecE0 P (Σ', universes_decl_of_decl decl) c decl.
Proof. eapply weakening_env_gen_lookup_on_global_envE; tc. Qed.
Lemma weakening_env_strictly_decls_lookup_on_global_envE `{checker_flags} P Σ Σ' c decl :
  weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ' -> wfE Σ -> strictly_extends_decls Σ Σ' -> on_global_env cumulSpecE0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpecE0 P (Σ', universes_decl_of_decl decl) c decl.
Proof. eapply weakening_env_gen_lookup_on_global_envE; tc. Qed.

(* we can fill weaken_env_strictly_decls_prop with any other weaken_env_*_prop, so we only include this version *)
Lemma weaken_lookup_on_global_envE `{checker_flags} P Σ c decl :
  weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpecE0 P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_strictly_decls_lookup_on_global_envE; tea; tc; reflexivity.
Qed.

Lemma declared_constant_invE `{checker_flags} Σ P cst decl :
  weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  declared_constant Σ cst decl ->
  on_constant_decl P (Σ, cst_universes decl) decl.
Proof.
  intros.
  unshelve eapply declared_constant_to_gen in H0; tea.
  eapply weaken_lookup_on_global_envE in X1; eauto. apply X1.
Qed.

Lemma declared_minductive_invE `{checker_flags} {Σ P ind mdecl} :
  weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive cumulSpecE0 P (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  unshelve eapply declared_minductive_to_gen in H0; tea.
  eapply weaken_lookup_on_global_envE in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_invE `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body cumulSpecE0 P (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_invE in Hmdecl; cbn in X; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma weaken_decls_lookup_on_global_envE `{checker_flags} P Σ c decl :
  weaken_env_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpecE0 P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_decls_lookup_on_global_envE; eauto.
  split => //.
  - exists []; simpl; destruct Σ; eauto.
Qed.

Lemma declared_constructor_invE `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P)
  (wfΣ : wfE Σ)
  (HΣ : on_global_env cumulSpecE0 P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_invE HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor cumulSpecE0 P (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_invE HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_minductive_inv_declsE `{checker_flags} {Σ P ind mdecl} :
  weaken_env_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive cumulSpecE0 P (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  unshelve eapply declared_minductive_to_gen in H0; tea.
  eapply weaken_decls_lookup_on_global_envE in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv_declsE `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_decls_prop cumulSpecE0 (lift_typing typingE) P ->
  wfE Σ -> on_global_env cumulSpecE0 P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body cumulSpecE0 P (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv_declsE in Hmdecl; cbn in X; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma declared_constructor_inv_declsE `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_decls_prop cumulSpecE0 (lift_typing typingE) P)
  (wfΣ : wfE Σ)
  (HΣ : on_global_env cumulSpecE0 P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv_declsE HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor cumulSpecE0 P (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv_declsE HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_projection_invE `{checker_flags} {Σ P mdecl idecl cdecl ref pdecl} :
  forall (HP : weaken_env_strictly_decls_prop cumulSpecE0 (lift_typing typingE) P)
  (wfΣ : wfE Σ)
  (HΣ : on_global_env cumulSpecE0 P Σ)
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl),
  match idecl.(ind_ctors) return Type with
  | [c] =>
    let oib := declared_inductive_invE HP wfΣ HΣ (let (x, _) := Hdecl in
      let (x, _) := x in x) in
    (match oib.(ind_cunivs) with
     | [cs] => sorts_local_ctx P (Σ, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args c) cs
     | _ => False
    end) *
    on_projections mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) idecl (idecl.(ind_indices)) c *
    (ref.(proj_arg) < context_assumptions c.(cstr_args)) *
    on_projection mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) c ref.(proj_arg) pdecl
  | _ => False
  end.
Proof.
  intros.
  destruct (declared_inductive_invE HP wfΣ HΣ (let (x, _) := Hdecl in let (x, _) := x in x)) in *.
  destruct Hdecl as [Hidecl [Hcdecl Hnpar]]. simpl.
  move: onProjections. generalize (nth_error_Some_length Hcdecl).
  case: (ind_projs idecl) => //= .
  { lia. }
  destruct (ind_ctors idecl) as [|? []]; try contradiction.
  destruct ind_cunivs as [|? []]; try contradiction; depelim onConstructors.
  2:{ depelim onConstructors. }
  intuition auto.
  - destruct onProjections.
    destruct (ind_ctors idecl) as [|? []]; simpl in *; try discriminate.
    inv onConstructors. now eapply on_cargs in o.
  - destruct onProjections. eapply nth_error_Some_length in Hcdecl. lia.
  - destruct onProjections.
    eapply nth_error_alli in Hcdecl; eauto.
    eapply Hcdecl.
Qed.


Lemma weaken_env_prop_typingE `{checker_flags} : weaken_env_prop cumulSpecE0 (lift_typing typingE) (lift_typing typingE).
Proof.
  do 2 red. intros * wfΣ wfΣ' Hext Γ j Hj.
  apply lift_typing_impl with (1 := Hj); intros ?? HT.
  eapply (weakening_envE (_, _)).
  2: eauto.
  all: auto.
Qed.

#[global]
 Hint Unfold weaken_env_prop weaken_env_prop_gen : pcuic.

Lemma on_declared_constantE `{checker_flags} {Σ cst decl} :
  wfE Σ -> declared_constant Σ cst decl ->
  on_constant_decl (lift_typing typingE) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply declared_constant_invE; tea.
  exact weaken_env_prop_typingE.
Qed.


Lemma weaken_wf_localE `{checker_flags} (Σ : global_env_ext) Σ' Γ :
  wfE Σ -> extends Σ Σ' -> wfE Σ' -> wf_localE Σ Γ -> wf_localE (Σ', Σ.2) Γ.
Proof.
  intros * wfΣ Hext wfΣ' *.
  intros wfΓ.
  eapply (env_propE_wf_local weakening_envE); eauto.
Qed.

#[global]
Hint Resolve weaken_wf_localE | 100 : pcuic.

Lemma on_declared_minductiveE `{checker_flags} {Σ ref decl} :
  wfE Σ ->
  declared_minductive Σ ref decl ->
  on_inductive cumulSpecE0 (lift_typing typingE) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_invE weaken_env_prop_typingE wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductiveE `{checker_flags} {Σ ref mdecl idecl} {wfΣ : wfE Σ} :
  declared_inductive Σ ref mdecl idecl ->
  on_inductive cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros Hdecl.
  split.
  - destruct Hdecl as [Hmdecl _]. now apply on_declared_minductiveE in Hmdecl.
  - apply (declared_inductive_invE weaken_env_prop_typingE wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_constructorE `{checker_flags} {Σ ref mdecl idecl cdecl}
  {wfΣ : wfE Σ}
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  on_inductive cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl)
               (inductive_mind (fst ref)) mdecl *
  on_ind_body cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl)
              (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  ∑ ind_ctor_sort,
    let onib := declared_inductive_invE weaken_env_prop_typingE wfΣ wfΣ (let (x, _) := Hdecl in x) in
     nth_error (ind_cunivs onib) ref.2 = Some ind_ctor_sort
    ×  on_constructor cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl)
                 mdecl (inductive_ind (fst ref))
                 idecl idecl.(ind_indices) cdecl ind_ctor_sort.
Proof.
  split.
  - destruct Hdecl; now apply on_declared_inductiveE.
  - apply (declared_constructor_invE weaken_env_prop_typingE wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_projectionE `{checker_flags} {Σ ref mdecl idecl cdecl pdecl} {wfΣ : wfE Σ}
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl) :
  on_inductive cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) (inductive_mind ref.(proj_ind)) mdecl *
  (idecl.(ind_ctors) = [cdecl]) *
  let oib := declared_inductive_invE weaken_env_prop_typingE wfΣ wfΣ (let (x, _) := Hdecl in let (x, _) := x in x) in
  (match oib.(ind_cunivs) with
  | [cs] => sorts_local_ctx (lift_typing typingE) (Σ, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args cdecl) cs
    | _ => False
  end) *
  on_projections mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) idecl (idecl.(ind_indices)) cdecl *
  (ref.(proj_arg) < context_assumptions cdecl.(cstr_args)) *
  on_projection mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) cdecl ref.(proj_arg) pdecl.
Proof.
  have hctors : idecl.(ind_ctors) = [cdecl].
  { pose proof (declared_projection_invE weaken_env_prop_typingE wfΣ wfΣ Hdecl).
    move: X. destruct Hdecl. destruct d. cbn in *.
    move: e. destruct (ind_ctors idecl) as [|? []] => //.
    intros [= ->] => //. }
  split.
  - split => //. destruct Hdecl as [[] ?]. now eapply on_declared_inductiveE.
  - pose proof (declared_projection_invE weaken_env_prop_typingE wfΣ wfΣ Hdecl).
    destruct Hdecl. cbn in *. destruct d; cbn in *.
    now rewrite hctors in X.
Qed.
