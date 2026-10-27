(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config EnvMap.
From MetaRocq.Template Require Ast TypingWf WfAst TermEquality.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICWeakeningConv PCUICWeakeningTyp PCUICWeakeningEnv
     PCUICSubstitution PCUICGeneration PCUICCasesContexts
     PCUICOnFreeVars PCUICWellScopedCumulativity PCUICConversion
     PCUICProgram.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags).

Set Default Proof Using "Type*".

Coercion Ast.Env.fst_ctx : Ast.Env.global_env_ext >-> Ast.Env.global_env.

Definition lengths :=
  (@Ast.Env.context_assumptions_subst_context,
  Ast.Env.context_assumptions_app,
  @Ast.Env.context_assumptions_subst_instance, @Ast.Env.context_assumptions_lift_context,
   @Ast.Env.expand_lets_ctx_length, @Ast.Env.subst_context_length,
  @Ast.Env.subst_instance_length,
  @Ast.Env.expand_lets_k_ctx_length,
  @Ast.inds_length, @Ast.Env.lift_context_length,
  @length_app, @List.length_rev, @Ast.Env.extended_subst_length, @reln_length,
  Nat.add_0_r, @app_nil_r,
  @length_map, @mapi_length, @mapi_rec_length,
  @fold_context_k_length, @Typing.cofix_subst_length, @Typing.fix_subst_length,
  @Ast.Env.smash_context_length, @Ast.Env.arities_context_length).

Definition plengths :=
    (@context_assumptions_subst_context,
    @context_assumptions_app,
    @context_assumptions_subst_instance, @context_assumptions_lift_context,
     @expand_lets_ctx_length, @subst_context_length,
    @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
    @length_app, @List.length_rev, @extended_subst_length, @reln_length,
    Nat.add_0_r, @app_nil_r,
    @length_map, @mapi_length, @mapi_rec_length,
    @fold_context_k_length, @cofix_subst_length, @fix_subst_length,
    @smash_context_length, @context_assumptions_smash_context,
    @arities_context_length).

Lemma ind_predicate_context_length ind mdecl idecl :
  #|Ast.ind_predicate_context ind mdecl idecl| = S #|idecl.(Ast.Env.ind_indices)|.
Proof.
  rewrite /Ast.ind_predicate_context /=. now len.
Qed.

Definition pclengths :=
  (@PCUICCases.ind_predicate_context_length,
    @PCUICCases.cstr_branch_context_length,
    @PCUICCases.inst_case_branch_context_length,
    @PCUICCases.inst_case_predicate_context_length,
    @ind_predicate_context_length).

Ltac len ::=
  repeat (rewrite !lengths /= // || rewrite !plengths /= // || rewrite !pclengths /= //);
  try lia.

Tactic Notation "len" "in" hyp(id) :=
  repeat (rewrite !lengths /= // in id || rewrite !plengths /= // in id ||
    rewrite !pclengths /= // in id);
  try lia.

(* Source =Template, Target (unqualified) = Rocq *)

Module S :=Template.Ast.
Module SEq :=Template.TermEquality.
Module ST :=Template.Typing.
Module SL :=Template.LiftSubst.

Lemma wf_fresh_globals {cf : checker_flags} (Σ : global_env) : wf Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; constructor; auto.
  destruct o; auto.
Qed.

Lemma of_global_env_cons {cf:checker_flags} d g : EnvMap.fresh_globals (add_global_decl g d).(declarations) ->
  EnvMap.of_global_env (add_global_decl g d).(declarations) = EnvMap.add d.1 d.2 (EnvMap.of_global_env g.(declarations)).
Proof.
  unfold EnvMap.of_global_env. simpl. unfold KernameMapFact.uncurry.
  reflexivity.
Qed.

Lemma trans_lookup_minductive {cf} {Σ : global_env_map} mind : wf Σ ->
  TransLookup.lookup_minductive Σ mind = PCUICAst.lookup_minductive Σ mind.
Proof.
  intros wf.
  unfold TransLookup.lookup_minductive.
  rewrite (EnvMap.lookup_spec Σ.(declarations)) //.
  now eapply wf_fresh_globals. apply Σ.
Qed.

Lemma trans_lookup_inductive {cf} {Σ : global_env_map} mind : wf Σ ->
  TransLookup.lookup_inductive Σ mind = PCUICAst.lookup_inductive Σ mind.
Proof.
  intros wf.
  unfold TransLookup.lookup_inductive, lookup_inductive.
  rewrite trans_lookup_minductive //.
Qed.

Lemma mkApps_morphism (f : term -> term) u v :
  (forall x y, f (tApp x y) = tApp (f x) (f y)) ->
  f (mkApps u v) = mkApps (f u) (List.map f v).
Proof.
  intros H.
  revert u; induction v; simpl; trivial.
  intros.
  now rewrite IHv H.
Qed.

Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !length_map;
  try solve_all; try typeclasses eauto with core.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  revert f l'; induction l; simpl; trivial.
Qed.

Ltac maps := rewrite_strat (topdown (old_hints map)).
Ltac lengths := rewrite_strat (topdown (hints len)).

Lemma destArity_mkApps ctx t l : l <> [] -> destArity ctx (mkApps t l) = None.
Proof.
  destruct l as [|a l]. congruence.
  intros _. simpl.
  revert t a; induction l; intros; simpl; try congruence.
Qed.

Lemma trans_global_decls_app {Σ : global_env_map} (Σ' Σ'' : Ast.Env.global_declarations) :
  trans_global_decls Σ (Σ' ++ Σ'') =
  trans_global_decls (trans_global_decls Σ Σ'') Σ'.
Proof.
  rewrite /trans_global_decls.
  now rewrite fold_right_app.
Qed.

Lemma incl_cs_refl cs : cs ⊂_cs cs.
Proof.
  split; [lsets|csets].
Qed.

Lemma extends_trans_global_decls_acc (Σ' : global_env_map) (Σ : Ast.Env.global_declarations) :
  strictly_extends_decls Σ' (trans_global_decls Σ' Σ).
Proof.
  induction Σ.
  * split; cbn; now try exists [].
  * rewrite /=.
    destruct IHΣ as [univs [Σ'' eq]]. cbn in *.
    split; cbn; auto.
    eexists (_ :: Σ'').
    rewrite -app_comm_cons. now f_equal.
Qed.

Definition wf_global_decl {cf} (Σ : Ast.Env.global_env_ext) kn decl :=
  Typing.on_global_decl Typing.cumul_gen (fun (Σ : Ast.Env.global_env_ext) => WfAst.wf_decl_pred Σ) Σ kn decl.

(* Issue in equations: signatures cannot be found up-to arbitrary conversions. *)
(* #[global] Hint Extern 4 (Signature (Typing.wf _) _ _) => exact (on_global_env_Signature _ _ _) : typeclass_instances. *)

Lemma trans_lookup_env {cf} {Σ : Ast.Env.global_env} cst {wfΣ : Typing.wf Σ} :
  match Ast.Env.lookup_env Σ cst with
  | None => lookup_env (trans_global_env Σ) cst = None
  | Some d =>
    ∑ Σ' : Ast.Env.global_env,
      [× Ast.Env.strictly_extends_decls Σ' Σ,
        Typing.wf Σ',
        wf_global_decl (Σ', Ast.universes_decl_of_decl d) cst d,
        strictly_extends_decls (trans_global_env Σ') (trans_global_env Σ) &
        lookup_env (trans_global_env Σ) cst = Some (trans_global_decl (trans_global_env Σ') d)]
  end.
Proof.
  destruct Σ as [univs Σ retro].
  induction Σ.
  - cbn; auto.
  - unfold Ast.Env.lookup_env. cbn -[trans_global_env].
    destruct eq_kername eqn:eqk.
    change (eq_kername cst a.1) with (eqb cst a.1) in eqk.
    apply eqb_eq in eqk; subst.
    eexists {| S.Env.universes := univs; S.Env.declarations := Σ; S.Env.retroknowledge := retro |}.
    split.
    * split => //. now exists [a].
    * destruct wfΣ as [onu ond]. depelim ond.
      split => //.
    * eapply TypingWf.typing_wf_sigma in wfΣ.
      destruct wfΣ as [onu ond]. depelim ond. now destruct o.
    * split => //.
      now exists [(a.1, trans_global_decl (trans_global_env {| S.Env.universes := univs; S.Env.declarations := Σ;
        S.Env.retroknowledge := retro |}) a.2)].
    * cbn. now rewrite eq_kername_refl.
    * destruct wfΣ as [onu ond]. depelim ond.
      specialize (IHΣ (onu, ond)).
      unfold Ast.Env.lookup_env in IHΣ. cbn [Ast.Env.declarations] in IHΣ.
      destruct (Ast.Env.lookup_global Σ cst) eqn:h.
      destruct IHΣ as [Σ' [ext wf ext' hl]].
      exists Σ'. split => //.
      destruct ext as [equ [? eq]].
      split => //. exists ((kn, d) :: x). cbn.
      cbn in eq. now rewrite eq.
      destruct hl as [equ' [? eq']].
      split => //.
      rewrite /trans_global_env /= /on_snd /=.
      eexists ((kn, _) :: x).
      cbn. rewrite -eq'. reflexivity.
      cbn. rewrite eqk /=. apply e.
      cbn. now rewrite eqk.
Qed.

Lemma trans_weakening {cf} Σ {Σ' : global_env_map} t :
  Typing.wf Σ -> extends (trans_global_env Σ) Σ' -> wf (trans_global_env Σ) -> wf Σ' ->
  WfAst.wf Σ t ->
  trans (trans_global_env Σ) t = trans Σ' t.
Proof.
  intros wfΣ ext wftΣ wfΣ' wft.
  induction wft using WfAst.term_wf_forall_list_ind; cbn; auto; try solve [f_equal; solve_all].
  rewrite !trans_lookup_inductive.
  destruct H as [H hnth].
  unshelve eapply Typing.TemplateDeclarationTyping.declared_minductive_to_gen in H; eauto.
  red in H.
  generalize (trans_lookup_env (inductive_mind ci)).
  move: H.
  rewrite /lookup_inductive /lookup_minductive. intros ->.
  intros [Σ'' [ext' wfΣ'' _ ext'' hl]].
  unfold lookup_inductive_gen, lookup_minductive_gen.
  rewrite hl => /= //. cbn.
  rewrite nth_error_map hnth /=.
  rewrite (extends_lookup _ _ _ _ wfΣ' ext hl) /=.
  rewrite nth_error_map hnth /=.
  red in X0.
  f_equal => //. rewrite /id. unfold trans_predicate. f_equal; solve_all.
  f_equal. solve_all.
  do 4 f_equal; solve_all.
Qed.

Lemma trans_decl_weakening {cf} Σ {Σ' : global_env_map} t :
  Typing.wf Σ -> extends (trans_global_env Σ) Σ' -> wf (trans_global_env Σ) -> wf Σ' ->
  WfAst.wf_decl Σ t ->
  trans_decl (trans_global_env Σ) t = trans_decl Σ' t.
Proof.
  intros wfΣ ext wftΣ wfΣ' wft.
  rewrite /trans_decl; destruct t as [na [b|] ty] => /=; f_equal;
  rewrite trans_weakening => //; apply wft.
Qed.

Lemma trans_local_length {Σ : global_env_map} Γ : #|trans_local Σ Γ| = #|Γ|.
Proof. now rewrite length_map. Qed.

#[global]
Hint Rewrite @trans_local_length : len.

Lemma trans_local_weakening {cf} Σ {Σ' : global_env_map} t :
  Typing.wf Σ -> extends (trans_global_env Σ) Σ' -> wf (trans_global_env Σ) -> wf Σ' ->
  All (WfAst.wf_decl Σ) t ->
  trans_local (trans_global_env Σ) t = trans_local Σ' t.
Proof.
  intros wfΣ ext wftΣ wfΣ' a.
  induction a; cbn; auto.
  f_equal. 2:apply IHa.
  rewrite /trans_decl; destruct x as [na [b|] ty] => /=; f_equal;
  rewrite trans_weakening => //; apply p.
Qed.

Lemma trans_ind_body_weakening {cf} Σ {Σ' : global_env_map} b :
  Typing.wf Σ -> extends (trans_global_env Σ) Σ' -> wf (trans_global_env Σ) -> wf Σ' ->
  TypingWf.wf_inductive_body Σ b ->
  trans_one_ind_body (trans_global_env Σ) b = trans_one_ind_body Σ' b.
Proof.
  intros wfΣ ext wftΣ wfΣ' H.
  destruct H. rewrite /trans_one_ind_body; destruct b; cbn in *.
  f_equal; solve_all.
  - rewrite trans_weakening //.
  - rewrite trans_weakening //.
  - unfold trans_constructor_body; destruct x; cbn in *; f_equal.
    * rewrite [map _ _]trans_local_weakening //.
    * solve_all. rewrite trans_weakening //.
    * rewrite trans_weakening //.
  - destruct x. unfold trans_projection_body; cbn. f_equal.
    rewrite trans_weakening //.
Qed.

Lemma trans_global_decl_weaken {cf} (Σ : Ast.Env.global_env_ext) {Σ' : global_env_map} kn d :
  Typing.wf Σ -> extends (trans_global_env Σ) Σ' -> wf (trans_global_env Σ) -> wf Σ' ->
  wf_global_decl Σ kn d ->
  trans_global_decl (trans_global_env Σ) d = trans_global_decl Σ' d.
Proof.
  intros wfΣ ext wftΣ wfΣ' wfd.
  destruct d; cbn; f_equal.
  - rewrite /trans_constant_body /=.
    do 3 red in wfd.
    destruct (Ast.Env.cst_body c) => /=. cbn.
    f_equal.
    erewrite trans_weakening; tea. reflexivity. apply wfd.
    erewrite trans_weakening; tea. reflexivity. apply wfd.
    f_equal.
    erewrite trans_weakening; tea. reflexivity. apply wfd.
  - rewrite /trans_minductive_body. f_equal.
    * erewrite trans_local_weakening; trea.
      eapply TypingWf.on_global_inductive_wf_params in wfd. solve_all.
    * eapply TypingWf.on_global_inductive_wf_bodies in wfd. solve_all.
      rewrite trans_ind_body_weakening //.
Qed.

Import TypingWf.

Lemma weaken_wf_decl_pred {cf} (Σ Σ' : Ast.Env.global_env) Γ j :
  Typing.wf Σ -> Ast.Env.extends Σ Σ' -> Typing.wf Σ' ->
  WfAst.wf_decl_pred Σ Γ j -> WfAst.wf_decl_pred Σ' Γ j.
Proof.
  intros wf ext wf' ong.
  red in ong |- *.
  destruct j_term; cbn in *.
  all: intuition eauto using wf_extends.
Qed.

Lemma trans_lookup {cf} Σ cst :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  lookup_env (trans_global_env Σ) cst =
  option_map (trans_global_decl (trans_global_env Σ)) (Ast.Env.lookup_env Σ cst).
Proof.
  intros wf wf'.
  generalize (trans_lookup_env cst).
  destruct Ast.Env.lookup_env eqn:heq => //.
  intros [Σ' [ext wfΣ' wfdecl ext' hl]].
  rewrite hl. cbn. f_equal.
  eapply (trans_global_decl_weaken (Σ', Ast.universes_decl_of_decl g)); tea; tc.
  eapply strictly_extends_decls_wf; tea.
Qed.

Section Translation.
  Context (Σ : Ast.Env.global_env).
  Notation trans := (trans (trans_global_env Σ)).
  Notation trans_decl := (trans_decl (trans_global_env Σ)).
  Notation trans_local := (trans_local (trans_global_env Σ)).

  Ltac dest_lookup :=
    destruct TransLookup.lookup_inductive as [[mdecl idecl]|].
  Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' :
    map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
  Proof.
    induction l in l' |- *; destruct l'; simpl; auto. f_equal.
    apply IHl.
  Qed.

Lemma trans_lift n k t :
  trans (Template.Ast.lift n k t) = lift n k (trans t).
Proof.
  revert k. induction t using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite lift_mkApps IHt map_map.
    f_equal. rewrite map_map; solve_all.

  - destruct X; red in X0.
    dest_lookup. simpl.
    * f_equal; auto.
      unfold trans_predicate, map_predicate_k; cbn.
      f_equal; auto. solve_list.
      + rewrite e. f_equal.
        now rewrite map2_bias_left_length.
      + rewrite !map_map_compose.
        rewrite map_map2 !PCUICUnivSubstitutionConv.map2_map_r.
        clear -X0. cbn.
        generalize (ind_ctors idecl).
        induction X0; simpl; auto. destruct l; reflexivity.
        intros l0; destruct l0; try reflexivity.
        cbn. rewrite IHX0. f_equal.
        rewrite /trans_branch /= p // /map_branch /map_branch_k /= /id. f_equal.
        now rewrite map2_bias_left_length.
    * simpl. rewrite /id /map_predicate_k /=. f_equal; eauto.
      f_equal; auto. rewrite !map_map_compose. solve_all.
      rewrite e. now rewrite length_map.
  - f_equal; auto. maps. solve_all.
  - f_equal; auto; solve_all.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - cbn; do 4 f_equal; auto.
    rewrite /map_array_model. f_equal; eauto. cbn. solve_all.
Qed.

Lemma trans_mkApp u a : trans (Template.Ast.mkApp u a) = tApp (trans u) (trans a).
Proof.
  induction u; simpl; try reflexivity.
  rewrite map_app.
  replace (tApp (mkApps (trans u) (map trans args)) (trans a))
    with (mkApps (mkApps (trans u) (map trans args)) [trans a]) by reflexivity.
  rewrite mkApps_app. reflexivity.
Qed.

Lemma trans_mkApps u v :
  trans (Template.Ast.mkApps u v) = mkApps (trans u) (List.map trans v).
Proof.
  revert u; induction v.
  simpl; trivial.
  intros.
  rewrite <-Template.AstUtils.mkApps_mkApp; auto.
  rewrite IHv. simpl. f_equal.
  apply trans_mkApp.
Qed.

Lemma trans_subst t k u :
  trans (Template.Ast.subst t k u) = subst (map trans t) k (trans u).
Proof.
  revert k. induction u using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.

  - repeat nth_leb_simpl; auto.
    rewrite trans_lift.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0. congruence.

  - f_equal; solve_list.

  - rewrite subst_mkApps. rewrite <- IHu.
    rewrite trans_mkApps. f_equal.
    solve_list.

  - destruct X; red in X0.
    dest_lookup; cbn; f_equal; auto; solve_list.
    unfold trans_predicate, map_predicate_k; cbn.
    f_equal; auto. solve_list.
    + rewrite e. f_equal.
      now rewrite map2_bias_left_length.
    + rewrite map_map2 !PCUICUnivSubstitutionConv.map2_map_r.
      clear -X0. cbn.
      generalize (ind_ctors idecl).
      induction X0; simpl; auto. destruct l; reflexivity.
      intros l0; destruct l0; try reflexivity.
      cbn. rewrite IHX0. f_equal.
      rewrite /trans_branch /= p // /map_branch /map_branch_k /= /id. f_equal.
      now rewrite map2_bias_left_length.
    + unfold subst_predicate, id => /=.
      f_equal; auto; solve_all.
  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - cbn; f_equal; auto. rewrite /map_array_model; cbn; do 3 f_equal; eauto.
    solve_all.
Qed.

Notation Tterm :=Template.Ast.term.
Notation Tcontext :=Template.Ast.Env.context.

Lemma All_map2 {A B C} P (l : list A) (l' : list B) (f g : A -> B -> C) :
  All P l' ->
  (forall x y, P y -> f x y = g x y) ->
  map2 f l l' = map2 g l l'.
Proof.
  induction 1 in l |- * => Hfg /=; destruct l => //.
  cbn. rewrite IHX //. f_equal.
  now apply Hfg.
Qed.

Lemma trans_subst_instance u t : trans (subst_instance u t) = subst_instance u (trans t).
Proof.
  rewrite /subst_instance /=.
  induction t using Template.Induction.term_forall_list_ind; simpl; try congruence.
  { f_equal. rewrite !map_map_compose. solve_all. }
  { rewrite IHt. rewrite map_map_compose.
    rewrite mkApps_morphism; auto. f_equal.
    rewrite !map_map_compose. solve_all. }
  2-3:f_equal; auto; unfold BasicAst.tFixProp, Ast.tCaseBrsProp in *;
    repeat toAll; solve_list.
  destruct X; red in X0.
  dest_lookup; cbn; f_equal; auto; solve_list.
  - rewrite /trans_predicate /= /map_predicate /=.
    f_equal; solve_all.
  - rewrite PCUICUnivSubstitutionConv.map2_map_r. cbn.
    rewrite map_map2 PCUICUnivSubstitutionConv.map2_map_r.
    eapply All_map2; tea; cbn => cdecl br.
    rewrite /map_branch /trans_branch /= /id.
    now intros; f_equal.
  - rewrite /id /map_predicate /=. f_equal; solve_all.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - cbn. rewrite /mapu_array_model; cbn; do 4 f_equal; auto; solve_all.
Qed.


Lemma trans_destArity {cf} {wfΣ : Typing.wf Σ} ctx t :
 Template.WfAst.wf Σ t ->
  wf (trans_global_env Σ) ->
  match Ast.destArity ctx t with
  | Some (args, s) =>
    destArity (trans_local ctx) (trans t) =
    Some (trans_local args, s)
  | None => destArity (trans_local ctx) (trans t) = None
  end.
Proof.
  intros wf wf'; revert ctx.
  induction wf using WfAst.term_wf_forall_list_ind; intros ctx; simpl; trivial.
  apply (IHwf0 (Ast.Env.vass n t :: ctx)).
  apply (IHwf1 (Ast.Env.vdef n t t0 :: ctx)).
  destruct l. congruence.
  now apply destArity_mkApps.
  destruct H as []. red in H.
  epose proof (trans_lookup Σ (inductive_mind ci.(ci_ind)) wfΣ wf').
  destruct TransLookup.lookup_inductive as [[mdecl' idecl']|] eqn:hl => //.
Qed.

(* TODO Duplicate? *)
Lemma Alli_map_option_out_mapi_Some_spec {A B B'} (f : nat -> A -> option B) (g' : B -> B')
      (g : nat -> A -> option B') P l t :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some (g' t)) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some (map g' t).
Proof.
  unfold mapi. generalize 0.
  move => n Hl Hfg. move: n Hl t.
  induction 1; try constructor; auto.
  simpl. move=> t [= <-] //.
  move=> /=.
  case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> t [= <-]. now rewrite (IHHl _ E').
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B' S} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') P l (ls : list S) t,
    All2 P l ls ->
    (forall i x t s, P x s -> f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' S f g' g P l ls t.
  unfold mapi. generalize 0.
  intros n hall h e.
  induction hall in t, n, h, e |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n x) eqn:e'. 2: discriminate.
    eapply h in e' as h'. 2: eassumption.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHhall in e'' as h''. 2: assumption.
    rewrite h''. apply some_inj in e. subst.
    simpl. reflexivity.
Qed.

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma trans_inds kn u bodies : map trans (Ast.inds kn u bodies) =
  inds kn u (map (trans_one_ind_body (trans_global_env Σ)) bodies).
Proof.
  unfold inds, Ast.inds. rewrite length_map.
  induction bodies. simpl. reflexivity. simpl; f_equal. auto.
Qed.

Lemma trans_it_mkProd_or_LetIn ctx t :
  trans (Ast.Env.it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (map trans_decl ctx) (trans t).
Proof.
  induction ctx in t |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl.
  now rewrite IHctx.
  now rewrite IHctx.
Qed.

Lemma trans_it_mkLambda_or_LetIn ctx t :
  trans (Ast.Env.it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (map trans_decl ctx) (trans t).
Proof.
  induction ctx in t |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl.
  now rewrite IHctx.
  now rewrite IHctx.
Qed.

Lemma trans_local_subst_instance u (Γ : Ast.Env.context) :
  trans_local (subst_instance u Γ) = subst_instance u (trans_local Γ).
Proof.
  rewrite /subst_instance /=.
  induction Γ as [| [na [b|] A] Γ ih ] in u |- *.
  - reflexivity.
  - simpl. f_equal. 2: eapply ih.
    unfold map_decl, trans_decl. simpl.
    rewrite 2!trans_subst_instance.
    reflexivity.
  - simpl. f_equal. 2: eapply ih.
    unfold map_decl, trans_decl. simpl.
    rewrite trans_subst_instance.
    reflexivity.
Qed.

Lemma decompose_prod_assum_mkApps_nonnil ctx f args :
  args <> [] ->
  decompose_prod_assum ctx (mkApps f args) = (ctx, mkApps f args).
Proof.
  induction args => //.
  intros.
  rewrite mkApps_nonempty //.
Qed.

Notation trΣ := (trans_global_env Σ).

Lemma trans_ind_params mdecl : trans_local (Ast.Env.ind_params mdecl) = ind_params (trans_minductive_body trΣ mdecl).
Proof. reflexivity. Qed.

Lemma trans_ind_bodies mdecl : map (trans_one_ind_body trΣ) (Ast.Env.ind_bodies mdecl) =
  ind_bodies (trans_minductive_body (trans_global_env Σ) mdecl).
Proof. reflexivity. Qed.

(* From MetaRocq.PCUIC Require Import PCUICClosed PCUICInductiveInversion.

Lemma instantiate_params_spec params paramsi concl ty :
  instantiate_params params paramsi (it_mkProd_or_LetIn params concl) = Some ty ->
  ty = (subst (List.rev paramsi) 0 (expand_lets params concl)).
Proof.
  intros h. eapply instantiate_params_make_context_subst in h as [ctx'' [ms [s' [da [dp ->]]]]].
  eapply make_context_subst_spec in dp.
  rewrite List.rev_involutive in dp.
  pose proof (PCUICContexts.context_subst_length2 dp).
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in da. noconf da.
  apply context_subst_subst_extended_subst in dp as ->.
  rewrite map_subst_expand_lets ?List.length_rev //.
Qed. *)

Lemma trans_ind_bodies_length mdecl : #|Ast.Env.ind_bodies mdecl| = #|ind_bodies (trans_minductive_body trΣ mdecl)|.
Proof. simpl. now rewrite length_map. Qed.

Lemma trans_ind_params_length mdecl : #|Ast.Env.ind_params mdecl| = #|ind_params (trans_minductive_body trΣ mdecl)|.
Proof. simpl. now rewrite length_map. Qed.

Lemma trans_ind_npars mdecl : Ast.Env.ind_npars mdecl = ind_npars (trans_minductive_body trΣ mdecl).
Proof. simpl. reflexivity. Qed.

Lemma trans_reln l p Γ : map trans (Ast.Env.reln l p Γ) =
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; [auto..|].
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (Ast.Env.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

Lemma context_assumptions_map ctx : context_assumptions (map trans_decl ctx) = Ast.Env.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Hint Resolve Template.TypingWf.typing_wf : wf.

Lemma mkApps_trans_wf U l :Template.WfAst.wf Σ (Template.Ast.tApp U l) -> exists U' V', trans (Template.Ast.tApp U l) = tApp U' V'.
Proof.
  simpl. induction l using rev_ind. intros. inv X. congruence.
  intros. rewrite map_app. simpl. exists (mkApps (trans U) (map trans l)), (trans x).
  clear. revert U x ; induction l. simpl. reflexivity.
  simpl. intros.
  rewrite mkApps_app. simpl. reflexivity.
Qed.

Derive Signature for SEq.eq_term_upto_univ_napp.

End Translation.

(* Derive Signature for Typing.on_global_env. *)

Section Trans_Global.
  Context {cf : checker_flags}.
  Context (Σ : Ast.Env.global_env).
  Notation Σ' := (trans_global_env Σ).
  Context (wfΣ : Typing.wf Σ).
  Context (wfΣ' : wf Σ').

  Lemma forall_decls_declared_constant cst decl :
    Ast.declared_constant Σ cst decl ->
    declared_constant Σ' cst (trans_constant_body Σ' decl).
  Proof.
    intro H.
    unshelve eapply Typing.TemplateDeclarationTyping.declared_constant_to_gen in H; eauto.
    unshelve eapply declared_constant_from_gen; eauto. move:H.
    unfold declared_constant, Ast.declared_constant,
      declared_constant_gen, Ast.declared_constant_gen.
    now rewrite trans_lookup => -> /=.
  Qed.

  Lemma forall_decls_declared_minductive cst decl :
    Ast.declared_minductive Σ cst decl ->
    declared_minductive (trans_global_env Σ) cst (trans_minductive_body Σ' decl).
  Proof.
    intro H.
    unshelve eapply Typing.TemplateDeclarationTyping.declared_minductive_to_gen in H; eauto.
    unshelve eapply declared_minductive_from_gen; eauto. move:H.
    unfold declared_minductive, Ast.declared_minductive.
    unfold declared_minductive_gen, Ast.declared_minductive_gen.
    now rewrite trans_lookup => -> /=.
  Qed.

  Lemma forall_decls_declared_inductive ind mdecl idecl :
    Ast.declared_inductive Σ ind mdecl idecl ->
    declared_inductive Σ' ind (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl).
  Proof.
    unfold declared_inductive, Ast.declared_inductive.
    move=> [decl' Hnth].
    pose proof (forall_decls_declared_minductive _ _ decl').
    eexists. eauto.
    now rewrite nth_error_map Hnth.
  Qed.

  Lemma forall_decls_declared_constructor cst mdecl idecl cdecl :
    Ast.declared_constructor Σ cst mdecl idecl cdecl ->
    declared_constructor Σ' cst (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl)
        (trans_constructor_body Σ' cdecl).
  Proof.
    unfold declared_constructor, Ast.declared_constructor.
    move=> [decl' Hnth].
    pose proof (forall_decls_declared_inductive _ _ _ decl'). split; auto.
    by rewrite nth_error_map Hnth.
  Qed.

  Lemma forall_decls_declared_projection cst mdecl idecl cdecl pdecl :
    Ast.declared_projection Σ cst mdecl idecl cdecl pdecl ->
    declared_projection (trans_global_env Σ) cst (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl)
      (trans_constructor_body Σ' cdecl)  (trans_projection_body Σ' pdecl).
  Proof.
    unfold declared_constructor, Ast.declared_constructor.
    move=> [decl' [Hnth Hnpar]].
    pose proof (forall_decls_declared_constructor _ _ _ _ decl'). split; auto.
    by rewrite nth_error_map Hnth.
  Qed.
End Trans_Global.

Lemma on_global_env_impl `{checker_flags} {Σ : Ast.Env.global_env} P Q :
  (forall (Σ : Ast.Env.global_env_ext) Γ j, ST.on_global_env Typing.cumul_gen P Σ -> P Σ Γ j -> Q Σ Γ j) ->
  ST.on_global_env Typing.cumul_gen P Σ -> ST.on_global_env Typing.cumul_gen Q Σ.
Proof.
  apply on_global_env_impl.
Qed.

Lemma typing_wf_wf {cf}:
  forall (Σ : Ast.Env.global_env),
    ST.wf Σ ->
    ST.on_global_env ST.cumul_gen
      (fun Σ Γ j => WfAst.wf_decl_pred Σ Γ j) Σ.
Proof.
  intros Σ.
  eapply on_global_env_impl. clear.
  intros Σ' Γ j ? Hj.
  apply lift_typing_wf_pred with (Γ := Γ).
  apply ST.lift_typing_impl with (1 := Hj).
  eapply typing_wf.
  apply X.
Qed.

Lemma declared_inductive_inj {cf Σ mdecl mdecl' ind idecl idecl'}
  {wfΣ : Typing.wf Σ}:
  Ast.declared_inductive Σ ind mdecl' idecl' ->
  Ast.declared_inductive Σ ind mdecl idecl ->
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] []. unfold Ast.declared_minductive in *.
  unshelve eapply Typing.TemplateDeclarationTyping.declared_minductive_to_gen in H, H1; eauto.
  unfold Ast.declared_minductive_gen in H1.
  rewrite H in H1. inversion H1. subst. rewrite H2 in H0. inversion H0. eauto.
Qed.

Lemma lookup_inductive_None {cf} Σ {wfΣ : wf Σ} ind : lookup_inductive Σ ind = None ->
    ~ (exists mdecl idecl, declared_inductive Σ ind mdecl idecl).
Proof.
  intros hl [mdecl [idecl [decli hnth]]].
  unshelve eapply declared_minductive_to_gen in decli; eauto.
  unfold declared_inductive, declared_minductive in decli.
  unfold lookup_inductive, lookup_inductive_gen,
    lookup_minductive, lookup_minductive_gen in hl.
  unfold declared_minductive_gen in decli.
  destruct lookup_env eqn:heq.
  noconf decli. cbn in hl.
  destruct nth_error; congruence. congruence.
Qed.

Section Trans_Global.
  Context {cf : checker_flags}.
  Context (Σ : Ast.Env.global_env).
  Notation Σ' := (trans_global_env Σ).
  Context (wfΣ : Typing.wf Σ).
  Context (wfΣ' : wf Σ').

  Lemma trans_cmp_global_instance {cmp_universe pb gref napp u u'} :
    SEq.cmp_global_instance Σ cmp_universe pb gref napp u u' ->
    cmp_global_instance (trans_global_env Σ) cmp_universe pb gref napp u u'.
  Proof.
    unfold SEq.cmp_global_instance, SEq.global_variance.
    destruct gref; simpl; auto.
    - unfold cmp_global_instance_gen, cmp_opt_variance; cbn.
      unfold Ast.lookup_inductive_gen, lookup_inductive_gen,
        Ast.lookup_minductive_gen, lookup_minductive_gen.
      rewrite trans_lookup. destruct Ast.Env.lookup_env eqn:look => //; simpl.
      destruct g => /= //.
      rewrite nth_error_map.
      destruct nth_error eqn:hnth => /= //.
      rewrite /app_context /trans_local.
      rewrite -map_app context_assumptions_map. now intros.
    - unfold cmp_global_instance_gen, cmp_opt_variance; cbn.
      unfold lookup_constructor, lookup_inductive, lookup_minductive.
      unfold Ast.lookup_constructor, Ast.lookup_inductive, Ast.lookup_minductive.
      unfold lookup_constructor_gen, lookup_inductive_gen, lookup_minductive_gen.
      unfold Ast.lookup_constructor_gen, Ast.lookup_inductive_gen, Ast.lookup_minductive_gen.
      rewrite trans_lookup. destruct Ast.Env.lookup_env => //; simpl.
      destruct g => /= //. rewrite nth_error_map.
      destruct nth_error => /= //.
      rewrite nth_error_map.
      destruct nth_error => /= //.
  Qed.

  Lemma eq_binder_annot_eq_context_gen_set_binder_name Γ Γ' Δ :
    All2 eq_binder_annot Γ Γ' ->
    eq_context_upto_names (map2 set_binder_name Γ Δ) (map2 set_binder_name Γ' Δ).
  Proof.
    induction 1 in Δ |- *.
    - constructor.
    - destruct Δ; cbn; constructor; auto.
      destruct c as [na [b|] ty]; cbn; constructor; auto.
  Qed.

  Lemma map2_map_map {A B C D E} (f : C -> A) (g : D -> B) (h : A -> B -> E) l l':
    map2 h (map f l) (map g l') = map2 (fun x y => h (f x) (g y)) l l'.
  Proof.
    induction l in l' |- *; destruct l'; cbn; f_equal; auto.
  Qed.

  Lemma All2_map2 {A B C} (P : A -> A -> Type) (x : list C) (f : C -> B -> A) (l l' : list B) :
    All3 (fun x y z => P (f x y) (f x z)) x l l' ->
    All2 P (map2 f x l) (map2 f x l').
  Proof.
    induction 1; cbn; constructor; auto.
  Qed.

  Lemma All2_All2_All2_All3 {A B C} (P : A -> B -> C -> Type) (Q : A -> B -> Type) (Q' : A -> C -> Type)
    (R : B -> C -> Type)
    (x : list A) (l : list B) (l' : list C):
    All2 Q x l -> All2 Q' x l' -> All2 R l l' ->
    (forall x y z, Q x y -> Q' x z -> R y z -> P x y z) ->
    All3 P x l l'.
  Proof.
    induction 1 in l' |- *; intros H; depelim H; intros H'; depelim H'; cbn; constructor; auto.
  Qed.

  Lemma trans_eq_term_upto_univ {cmp_universe cmp_sort pb napp t u} :
    WfAst.wf Σ t ->
    WfAst.wf Σ u ->
    SEq.eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t u ->
    eq_term_upto_univ_napp (trans_global_env Σ) cmp_universe cmp_sort pb napp (trans (trans_global_env Σ) t) (trans (trans_global_env Σ) u).
  Proof.
    intros wt wu e.
    induction t using Induction.term_forall_list_rect in pb, napp, wt, u, wu, e |- *.
    all: invs e; cbn.
    all: try solve [ constructor ; auto ].
    all: repeat (match goal with
      | H : WfAst.wf _ (_ _) |- _ => apply WfAst.wf_inv in H; simpl in H
      | H : _ /\ _ |- _ => destruct H
    end).
    all: try solve [
      repeat constructor ; auto ;
      match goal with
      | ih : forall pb napp (u : Ast.term), _ |- _ =>
        now eapply ih
      end
    ].
    - constructor.
      solve_all.
    - eapply eq_term_upto_univ_napp_mkApps.
      + rewrite length_map. now eapply IHt.
      + destruct wt, wu. solve_all.
    - constructor. apply trans_cmp_global_instance; auto.
    - constructor. apply trans_cmp_global_instance; auto.
    - red in X, X0.
      destruct wt as [mdecl' [idecl' [decli hci hpctx lenpar eqpars eqret eqc eqbrs]]].
      destruct wu as [mdecl'' [idecl'' [decli' hci' hpctx' lenpars' eqpars' eqret' eqc' eqbrs']]].
      destruct (declared_inductive_inj decli decli'). subst.
      eapply forall_decls_declared_inductive in decli; tea.
      rewrite trans_lookup_inductive.
      destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
      2:{ eapply lookup_inductive_None in hl; tea. elim hl. eauto. }
      apply lookup_inductive_declared in hl.
      unshelve epose proof (decli'' := declared_inductive_to_gen decli); eauto.
      destruct (PCUICGlobalEnv.declared_inductive_inj decli'' hl). subst.
      destruct X.
      constructor. all: try solve [
        match goal with
        | ih : forall pb napp u, _ |- _ =>
          now eapply ih
        end
      ].
      unfold trans_predicate, eq_predicate; cbn.
      repeat split; solve_all; try typeclasses eauto with typeclass_instances core.
      * rewrite map2_map2_bias_left; len.
        eapply All2_length in hpctx. len in hpctx.
        rewrite map2_map2_bias_left; len.
        eapply All2_length in hpctx'. len in hpctx'.
        now eapply eq_binder_annot_eq_context_gen_set_binder_name.
      * rewrite !map2_map_map.
        eapply All2_map2. cbn.
        eapply All2_All_mix_right in eqbrs; tea.
        eapply All2_All2_All2_All3; tea.
        cbn. intros cdecl br br' [[eq wfb] IH] [eq' wfb'] [eqbs eqbods].
        split.
        { unfold trans_branch; cbn.
          rewrite map2_map2_bias_left; len.
          eapply All2_length in eq. now len in eq.
          rewrite map2_map2_bias_left; len.
          eapply All2_length in eq'. now len in eq'.
          now eapply eq_binder_annot_eq_context_gen_set_binder_name. }
        eapply IH; eauto; tc.

    - constructor.
      assert (
        w1 :
          All (fun def =>
            WfAst.wf Σ (dtype def) ×
            WfAst.wf Σ (dbody def)
          ) m
      ).
      { solve_all. }
      assert (
        w2 :
          All (fun def =>
            WfAst.wf Σ (dtype def) ×
            WfAst.wf Σ (dbody def)) mfix'
      ).
      { solve_all. }
      pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
      pose proof (All2_All_mix_left w1 h1) as h2.
      pose proof (All2_All_mix_right w2 h2) as h3.
      simpl in h3.
      eapply All2_map.
      eapply All2_impl. 1: exact h3.
      simpl.
      intros [? ? ? ?] [? ? ? ?] [[[? ?] [[ih1 ih2] [? ?]]] [? ?]].
      simpl in *.
      intuition eauto.
    - constructor.
      assert (
        w1 :
          All (fun def => WfAst.wf Σ (dtype def) × WfAst.wf Σ (dbody def)) m
      ).
      { solve_all. }
      assert (
        w2 :
          All (fun def => WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)) mfix'
      ).
      { solve_all. }
      pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
      pose proof (All2_All_mix_left w1 h1) as h2.
      pose proof (All2_All_mix_right w2 h2) as h3.
      simpl in h3.
      eapply All2_map.
      eapply All2_impl. 1: exact h3.
      simpl.
      intros [? ? ? ?] [? ? ? ?] [[[? ?] [[ih1 ih2] [? ?]]] [? ?]].
      simpl in *.
      intuition eauto.
    - constructor; eauto. intuition auto; constructor; cbn; eauto.
      + inv H4. auto.
      + solve_all.
  Qed.

  Lemma trans_leq_term ϕ T U :
    WfAst.wf Σ T -> WfAst.wf Σ U -> SEq.leq_term Σ ϕ T U ->
    leq_term (trans_global_env Σ) ϕ (trans Σ' T) (trans Σ' U).
  Proof.
    intros HT HU H.
    eapply trans_eq_term_upto_univ ; eauto.
  Qed.

  Lemma trans_eq_term φ t u :
    WfAst.wf Σ t -> WfAst.wf Σ u -> SEq.eq_term Σ φ t u ->
    eq_term (trans_global_env Σ) φ (trans Σ' t) (trans Σ' u).
  Proof.
    intros HT HU H.
    eapply trans_eq_term_upto_univ ; eauto.
  Qed.

  Lemma trans_eq_term_list {φ l l'} :
      All (WfAst.wf Σ) l ->
      All (WfAst.wf Σ) l' ->
      All2 (SEq.eq_term Σ φ) l l' ->
      All2 (eq_term (trans_global_env Σ) φ) (List.map (trans Σ') l) (List.map (trans Σ') l').
  Proof.
    intros w w' h.
    eapply All2_map.
    pose proof (All2_All_mix_left w h) as h1.
    pose proof (All2_All_mix_right w' h1) as h2.
    simpl in h2.
    apply (All2_impl h2).
    intuition auto using trans_eq_term.
  Qed.
End Trans_Global.

From MetaRocq.PCUIC Require Import PCUICArityRed.
From MetaRocq.Template Require TemplateArityRed.

Section Trans_Global.
  Context {cf : checker_flags}.
  Context (Σ : Ast.Env.global_env).
  Notation Σ' := (trans_global_env Σ).

  Lemma trans_nth n l x : trans Σ' (nth n l x) = nth n (List.map (trans Σ') l) (trans Σ' x).
  Proof using Σ.
    induction l in n |- *; destruct n; trivial.
    simpl in *. congruence.
  Qed.

  Lemma trans_extended_subst Γ k :
    map (trans Σ') (Ast.Env.extended_subst Γ k) = extended_subst (trans_local Σ' Γ) k.
  Proof using Σ.
    induction Γ in k |- *; cbn; auto.
    destruct a as [na [b|] ty] => /= //; try congruence.
    * f_equal => //. rewrite trans_subst trans_lift IHΓ. f_equal => //.
      len. now rewrite context_assumptions_map.
    * now f_equal.
  Qed.

  Lemma trans_expand_lets_k Γ k t :
    trans Σ' (Ast.Env.expand_lets_k Γ k t) = expand_lets_k (trans_local Σ' Γ) k (trans Σ' t).
  Proof using Σ.
    rewrite /Ast.Env.expand_lets /Ast.Env.expand_lets_k.
    rewrite trans_subst trans_lift /expand_lets /expand_lets_k.
    rewrite trans_extended_subst. f_equal. len.
    now rewrite context_assumptions_map.
  Qed.

  Lemma trans_expand_lets Γ t :
    trans Σ' (Ast.Env.expand_lets Γ t) = expand_lets (trans_local Σ' Γ) (trans Σ' t).
  Proof using Σ.
    now rewrite /Ast.Env.expand_lets trans_expand_lets_k.
  Qed.

  Lemma trans_subst_context s k Γ :
    trans_local Σ' (Ast.Env.subst_context s k Γ) =
    subst_context (map (trans Σ') s) k (trans_local Σ' Γ).
  Proof using Σ.
    induction Γ.
    * cbn; auto.
    * simpl. rewrite subst_context_snoc Ast.Env.subst_context_snoc /= /snoc /subst_decl.
      len. f_equal => //.
      rewrite /map_decl /trans_decl /=.
      destruct a as [na [b|] ty]; cbn.
      f_equal. f_equal. rewrite trans_subst. now len.
      now rewrite trans_subst.
      f_equal.
      now rewrite trans_subst.
  Qed.

  Lemma trans_lift_context n k Γ :
    trans_local Σ' (Ast.Env.lift_context n k Γ) =
    lift_context n k (trans_local Σ' Γ).
  Proof using Σ.
    induction Γ.
    * cbn; auto.
    * simpl. rewrite !lift_context_snoc PCUICLiftSubst.lift_context_snoc /= /snoc /subst_decl.
      f_equal => //.
      rewrite /lift_decl /map_decl /trans_decl /=.
      destruct a as [na [b|] ty]; cbn.
      f_equal. f_equal. all:rewrite trans_lift; len => //.
  Qed.

  Lemma trans_expand_lets_ctx Γ Δ :
    trans_local Σ' (Ast.Env.expand_lets_ctx Γ Δ) = expand_lets_ctx (trans_local Σ' Γ) (trans_local Σ' Δ).
  Proof using Σ.
    rewrite /Ast.Env.expand_lets_ctx /Ast.Env.expand_lets_k_ctx.
    rewrite trans_subst_context trans_lift_context /expand_lets_ctx /expand_lets_k_ctx.
    rewrite trans_extended_subst. f_equal. len.
    now rewrite context_assumptions_map.
  Qed.

  Lemma trans_smash_context Γ Δ : trans_local Σ' (Ast.Env.smash_context Γ Δ) = smash_context (trans_local Σ' Γ) (trans_local Σ' Δ).
  Proof using Σ.
    induction Δ in Γ |- *; simpl; auto.
    destruct a as [na [b|] ty] => /=.
    rewrite IHΔ. f_equal.
    now rewrite (trans_subst_context [_]).
    rewrite IHΔ. f_equal. rewrite /trans_local map_app //.
  Qed.

  Lemma map_decl_subst_instance_set_binder_name i x y :
    map_decl (subst_instance i) (set_binder_name x y) =
    set_binder_name x (map_decl (subst_instance i) y).
  Proof using Σ.
    now rewrite /map_decl /set_binder_name /=.
  Qed.

  Lemma map2_trans l l' :
    map2
      (fun (x : aname) (y : BasicAst.context_decl Ast.term) =>
        trans_decl Σ' (Ast.Env.set_binder_name x y)) l l' =
    map2 (fun (x : aname) (y : BasicAst.context_decl Ast.term) =>
      set_binder_name x (trans_decl Σ' y)) l l'.
  Proof using Σ.
    eapply map2_ext.
    intros x y. rewrite /trans_decl. now destruct y; cbn.
  Qed.

  Lemma map_map_comm {A B B' C} (f : B -> C) (g : A -> B) (f' : B' -> C) (g' : A -> B') (l : list A) :
    (forall x, f (g x) = f' (g' x)) ->
    map f (map g l) = map f' (map g' l).
  Proof.
    intros Hfg.
    induction l; cbn; auto.
    now rewrite Hfg IHl.
  Qed.

  Lemma trans_cstr_branch_context ind mdecl cdecl :
    let mdecl' := trans_minductive_body Σ' mdecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    map (trans_decl Σ') (Ast.cstr_branch_context ind mdecl cdecl) =
    cstr_branch_context ind mdecl' cdecl'.
  Proof using Σ.
    cbn; intros.
    rewrite /Ast.cstr_branch_context /cstr_branch_context.
    rewrite [map _ _]trans_expand_lets_ctx. f_equal.
    rewrite trans_subst_context. f_equal.
    2:now repeat len.
    rewrite trans_inds //.
  Qed.

  Lemma trans_iota_red ind mdecl idecl cdecl pars p args br :
    let bctx := Ast.case_branch_context ind mdecl cdecl p br in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    let p' := trans_predicate ind mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl| ->
    trans Σ' (ST.iota_red pars args bctx br) =
    iota_red pars p' (List.map (trans Σ') args)
      (let br' := Ast.map_branch (trans Σ') br in
        trans_branch ind mdecl' cdecl' br'.(Ast.bcontext) br'.(Ast.bbody)).
  Proof using Σ.
    intros.
    unfold ST.iota_red, iota_red.
    rewrite /map_predicate /=.
    rewrite trans_subst map_rev map_skipn. f_equal.
    rewrite trans_expand_lets. f_equal.
    rewrite /bctx /id. rewrite /Ast.case_branch_context /Ast.case_branch_context_gen.
    rewrite /inst_case_branch_context. cbn.
    rewrite /inst_case_context.
    rewrite map2_map2_bias_left; len.
    rewrite /subst_context /id /subst_instance /subst_instance_context
      /map_context map_map2.
    change (map2
    (fun (x : aname) (y : context_decl) =>
     map_decl (subst_instance (Ast.puinst p)) (set_binder_name x y)))
     with
     (map2
     (fun (x : aname) (y : context_decl) =>
      set_binder_name x (map_decl (subst_instance (Ast.puinst p)) y))).
    rewrite -PCUICUnivSubstitutionConv.map2_map_r.
    rewrite -[fold_context_k _ _]PCUICRenameConv.map2_set_binder_name_fold; len.
    rewrite /trans_local map_map2 map2_trans.
    rewrite -PCUICUnivSubstitutionConv.map2_map_r. f_equal.
    rewrite [map _ _]trans_subst_context map_rev.
    rewrite /subst_context. f_equal.
    rewrite /Ast.Env.subst_instance_context /map_context.
    rewrite /trans_local.
    rewrite (map_map_comm _ _ (map_decl (subst_instance (Ast.puinst p))) (trans_decl Σ')).
    intros x. rewrite /map_decl /trans_decl; cbn.
    rewrite trans_subst_instance. f_equal.
    destruct (decl_body x) => /= //.
    now rewrite trans_subst_instance.
    f_equal.
    now rewrite trans_cstr_branch_context.
  Qed.

  Lemma trans_isLambda t :
    WfAst.wf Σ t -> isLambda (trans Σ' t) = Ast.isLambda t.
  Proof using Σ.
    destruct 1; cbnr.
    destruct u; [contradiction|]. cbn.
    generalize (map (trans Σ') u) (trans Σ' t) (trans Σ' t0); clear.
    induction l; intros; cbnr. apply IHl.
    destruct TransLookup.lookup_inductive as [[]|] => //.
  Qed.

  Lemma trans_unfold_fix mfix idx narg fn :
    All (fun def : def Ast.term => WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)) mfix ->
    ST.unfold_fix mfix idx = Some (narg, fn) ->
    unfold_fix (map (map_def (trans Σ') (trans Σ')) mfix) idx = Some (narg, trans Σ' fn).
  Proof using Σ.
    unfold ST.unfold_fix, unfold_fix. intros wffix.
    rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
    cbn.
    intros [= <- <-]. simpl.
    repeat f_equal.
    rewrite trans_subst.
    f_equal. clear Hdef.
    unfold fix_subst, ST.fix_subst. rewrite length_map.
    generalize mfix at 1 3.
    induction wffix; trivial.
    simpl; intros mfix. f_equal.
    eapply (IHwffix mfix).
  Qed.

  Lemma trans_unfold_cofix mfix idx narg fn :
    All (fun def : def Ast.term => WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)) mfix ->
    ST.unfold_cofix mfix idx = Some (narg, fn) ->
    unfold_cofix (map (map_def (trans Σ') (trans Σ')) mfix) idx = Some (narg, trans Σ' fn).
  Proof using Σ.
    unfold ST.unfold_cofix, unfold_cofix. intros wffix.
    rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef.
    intros [= <- <-]. simpl. repeat f_equal.
    rewrite trans_subst.
    f_equal. clear Hdef.
    unfold cofix_subst, ST.cofix_subst. rewrite length_map.
    generalize mfix at 1 3.
    induction wffix; trivial.
    simpl; intros mfix. f_equal.
    eapply (IHwffix mfix). congruence.
  Qed.

  Definition isApp t := match t with tApp _ _ => true | _ => false end.

  Lemma trans_is_constructor:
    forall (args : list Ast.term) (narg : nat),
      ST.is_constructor narg args = true -> is_constructor narg (map (trans Σ') args) = true.
  Proof using Σ.
    intros args narg.
    unfold ST.is_constructor, is_constructor.
    rewrite nth_error_map. destruct nth_error. simpl. intros.
    destruct t; try discriminate || reflexivity. simpl in H.
    destruct t; try discriminate || reflexivity.
    simpl. unfold isConstruct_app.
    unfold decompose_app. rewrite decompose_app_rec_mkApps. now simpl.
    congruence.
  Qed.

  Lemma refine_red1_r Σg Γ t u u' : u = u' -> red1 Σg Γ t u -> red1 Σg Γ t u'.
  Proof.
    intros ->. trivial.
  Qed.

  Lemma refine_red1_Γ Σg Γ Γ' t u : Γ = Γ' -> red1 Σg Γ t u -> red1 Σg Γ' t u.
  Proof.
    intros ->. trivial.
  Qed.
  Ltac wf_inv H := try apply WfAst.wf_inv in H; simpl in H; rdest.

  Lemma nth_error_map2 {A B C} (f : A -> B -> C) n l l' a b :
    nth_error l n = Some a ->
    nth_error l' n = Some b ->
    nth_error (map2 f l l') n = Some (f a b).
  Proof.
    induction l in n, l' |- *; destruct l', n; cbn; auto; try congruence.
  Qed.

  Lemma cstr_branch_context_assumptions ci mdecl cdecl :
    context_assumptions (cstr_branch_context ci mdecl cdecl) =
    context_assumptions cdecl.(cstr_args).
  Proof.
    rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
    now rewrite !context_assumptions_fold.
  Qed.

  Lemma Ast_cstr_branch_context_assumptions ci mdecl cdecl :
    Ast.Env.context_assumptions (Ast.cstr_branch_context ci mdecl cdecl) =
    Ast.Env.context_assumptions cdecl.(Ast.Env.cstr_args).
  Proof.
    rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
    now rewrite !Ast.Env.context_assumptions_fold.
  Qed.

  Lemma map2_set_binder_name_context_assumptions (l : list aname) (l' : Ast.Env.context) :
    #|l| = #|l'| ->
    Ast.Env.context_assumptions (map2 Ast.Env.set_binder_name l l') = Ast.Env.context_assumptions l'.
  Proof.
    induction l in l' |- *; destruct l'; cbn => //.
    intros [=]. destruct decl_body => //; eauto.
    f_equal; auto.
  Qed.

  Lemma Ast_inst_case_context_length pars puinst ctx :
    #|Ast.inst_case_context pars puinst ctx| = #|ctx|.
  Proof.
    rewrite /Ast.inst_case_context. now len.
  Qed.
  Hint Rewrite Ast_inst_case_context_length : len.

  Lemma Ast_inst_case_context_assumptions pars puinst ctx :
    Ast.Env.context_assumptions (Ast.inst_case_context pars puinst ctx) =
    Ast.Env.context_assumptions ctx.
  Proof.
    rewrite /Ast.inst_case_context.
    rewrite !Ast.Env.context_assumptions_fold.
    now rewrite Ast.Env.context_assumptions_map.
  Qed.

  Lemma case_branch_context_assumptions ci mdecl cdecl p br :
    #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl| ->
    Ast.Env.context_assumptions (Ast.case_branch_context ci mdecl cdecl p br) =
    Ast.Env.context_assumptions cdecl.(Ast.Env.cstr_args).
  Proof.
    intros.
    rewrite /Ast.case_branch_context /Ast.case_branch_context_gen; len.
    rewrite map2_set_binder_name_context_assumptions; len.
  Qed.

  Lemma declared_inductive_lookup {wfΣ' : wf Σ'} {ind mdecl idecl} :
    declared_inductive Σ' ind mdecl idecl ->
    lookup_inductive Σ' ind = Some (mdecl, idecl).
  Proof.
    intros [].
    unshelve eapply declared_minductive_to_gen in H; eauto.
    unfold lookup_inductive, lookup_minductive.
    unfold lookup_inductive_gen, lookup_minductive_gen.
    now rewrite H H0.
  Qed.

  (* Require Import PCUICInductiveInversion. *)
  Lemma map2_cst {A B} (l : list A) (l' : list B) :
    #|l| = #|l'| ->
    map2 (fun x y => x) l l' = l.
  Proof.
    induction l in l' |- *; destruct l'; cbn; auto. congruence.
    intros [=]. f_equal; auto.
  Qed.

  Lemma trans_inst_case_context pars puinst ctx :
    trans_local Σ' (Ast.inst_case_context pars puinst ctx) =
    inst_case_context (map (trans Σ') pars) puinst (trans_local Σ' ctx).
  Proof using Σ.
    rewrite /Ast.inst_case_context /inst_case_context.
    now rewrite trans_subst_context map_rev trans_local_subst_instance.
  Qed.

  Lemma trans_local_app Γ Δ : trans_local Σ' (Γ ,,, Δ) = trans_local Σ' Γ ,,, trans_local Σ' Δ.
  Proof using Σ.
    now rewrite /trans_local map_app.
  Qed.

  Lemma trans_case_predicate_context (ci : case_info) mdecl idecl p :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    #|Ast.pcontext p| = S #|Ast.Env.ind_indices idecl| ->
      (trans_local Σ' (Ast.case_predicate_context ci mdecl idecl p)) =
      (case_predicate_context ci mdecl' idecl' p').
  Proof using Σ.
    intros bctx p' mdecl' idecl' p'' eqp.
    rewrite /Ast.case_predicate_context /case_predicate_context /case_predicate_context_gen.
    rewrite /Ast.case_predicate_context_gen.
    rewrite /trans_local map_map2 map2_trans.
    rewrite -PCUICUnivSubstitutionConv.map2_map_r. f_equal.
    { cbn. rewrite map2_map2_bias_left; len.
      rewrite map_map2. cbn. rewrite map2_cst //.
      len. }
    rewrite /Ast.pre_case_predicate_context_gen /pre_case_predicate_context_gen.
    rewrite [map _ _]trans_inst_case_context. f_equal.
    rewrite /Ast.ind_predicate_context /ind_predicate_context /= /trans_decl.
    f_equal; cbn. f_equal.
    { rewrite trans_mkApps /=. f_equal.
      rewrite trans_reln /= /to_extended_list /to_extended_list_k. f_equal.
      rewrite trans_local_app trans_smash_context. f_equal.
      now rewrite trans_expand_lets_ctx. }
    now rewrite trans_expand_lets_ctx.
  Qed.

  Lemma trans_ind_predicate_context (Γ : list aname) ind mdecl idecl :
    let mdecl':= trans_minductive_body Σ' mdecl in
    let idecl':= trans_one_ind_body Σ' idecl in
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ (Ast.ind_predicate_context ind mdecl idecl) ->
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ (ind_predicate_context ind mdecl' idecl').
  Proof using Σ.
    intros.
    rewrite /Ast.ind_predicate_context in X.
    depelim X. constructor. now cbn in *.
    clear e.
    rewrite /mdecl' /idecl'. cbn.
    rewrite -trans_expand_lets_ctx. eapply All2_map_right.
    solve_all.
  Qed.

  Lemma trans_cstr_branch_context_alpha (Γ : list aname) ind mdecl cdecl :
    let mdecl' := trans_minductive_body Σ' mdecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ
      (Ast.cstr_branch_context ind mdecl cdecl) ->
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ
      (cstr_branch_context ind mdecl' cdecl').
  Proof using Σ.
    intros.
    rewrite -trans_cstr_branch_context. eapply All2_map_right.
    eapply All2_impl; tea. now cbn.
  Qed.

   Lemma inst_case_predicate_context_eq (ci : case_info) mdecl idecl p :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    WfAst.wf_nactx (Ast.pcontext p) (Ast.ind_predicate_context ci mdecl idecl) ->
    (trans_local Σ' (Ast.case_predicate_context ci mdecl idecl p)) =
    (inst_case_predicate_context p').
  Proof using Σ.
    intros.
    rewrite -(@inst_case_predicate_context_eq mdecl' idecl' ci p'0).
    2:{ apply trans_case_predicate_context.
        eapply All2_length in X; len in X. }
    rewrite /p'0. cbn.
    rewrite map2_map2_bias_left; len.
    eapply All2_length in X; len in X.
    apply eq_binder_annots_eq.
    now eapply trans_ind_predicate_context.
  Qed.

  Lemma trans_case_branch_context (ci : case_info) mdecl idecl cdecl p br :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    let br' := trans_branch ci mdecl' cdecl' br.(Ast.bcontext) (trans Σ' br.(Ast.bbody)) in
    WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci mdecl cdecl) ->
    (trans_local Σ' (Ast.case_branch_context ci mdecl cdecl p br)) =
    case_branch_context ci mdecl' p' (forget_types (bcontext br')) cdecl'.
  Proof using Σ.
    intros.
    rewrite /Ast.case_branch_context /Ast.case_branch_context_gen.
    rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
    rewrite /trans_local map_map2 map2_trans -PCUICUnivSubstitutionConv.map2_map_r.
    f_equal. cbn. rewrite map2_map2_bias_left.
    eapply All2_length in X. len in X. now len.
    rewrite map_map2 /= map2_cst //.
    eapply All2_length in X. len in X. now len.
    rewrite [map _ _]trans_inst_case_context. f_equal.
    now rewrite -trans_cstr_branch_context.
  Qed.

  Lemma inst_case_branch_context_eq (ci : case_info) mdecl idecl cdecl p br :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    let br' := trans_branch ci mdecl' cdecl' br.(Ast.bcontext) (trans Σ' br.(Ast.bbody)) in
    WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci mdecl cdecl) ->
    (trans_local Σ' (Ast.case_branch_context ci mdecl cdecl p br)) =
    (inst_case_branch_context p' br').
  Proof.
    intros.
    rewrite -(@inst_case_branch_context_eq ci mdecl' cdecl' p'0 br').
    { cbn. rewrite map2_map2_bias_left. len.
      eapply All2_length in X. now len in X.
      eapply eq_binder_annots_eq.
      now eapply trans_cstr_branch_context_alpha. }
    now apply trans_case_branch_context.
  Qed.

  Lemma OnOne2_map2 {A B C} (P : A -> A -> Type) (f : B -> C -> A) l l' l'' :
    OnOne2All (fun x y z => P (f x y) (f x z)) l l' l'' ->
    OnOne2 P (map2 f l l') (map2 f l l'').
  Proof.
    induction 1; cbn; constructor; auto.
  Qed.

  Lemma OnOne2All_map2 {A B D} (P : D -> B -> B -> Type)
    (f : B -> A -> D) (l : list A) (l' : list B) (l'' : list B) :
    #|l| = #|l'| ->
    OnOne2All P (map2 f l' l) l' l'' ->
    OnOne2All (fun x y z => P (f y x) y z) l l' l''.
  Proof.
    induction l' in l, l'' |- *; destruct l; cbn; intros hlen H; depelim H.
    constructor => //. lia.
    constructor => //. apply IHl' => //. lia.
  Qed.

  Lemma All2_nth_hyp {A B} (R : A -> B -> Type) l l' :
    All2 R l l' ->
    All2 (fun x y =>
      ∑ i, nth_error l i = Some x × R x y) l l'.
  Proof.
    intros a.
    induction a; constructor; auto.
    exists 0. cbn. auto.
    eapply (All2_impl IHa).
    intros ? ? [i hnth]. now exists (S i); cbn.
  Qed.

  Context (wfΣ : Typing.wf Σ).
  Context (wfΣ' : wf Σ').

  Lemma wf_wf_decl_pred : Typing.on_global_env Typing.cumul_gen (fun Σ => WfAst.wf_decl_pred Σ) Σ.
  Proof. now eapply typing_wf_sigma. Qed.
  Hint Resolve wf_wf_decl_pred : wf.

  Lemma trans_red1 Γ T U :
    All (WfAst.wf_decl Σ) Γ ->
    WfAst.wf Σ T ->
    ST.red1 Σ Γ T U ->
    red1 Σ' (trans_local Σ' Γ) (trans Σ' T) (trans Σ' U).
  Proof.
    intros wfΓ Hwf.
    induction 1 using ST.red1_ind_all; wf_inv Hwf; simpl in *;
      try solve [econstructor; eauto].

    - simpl. wf_inv w. inv a0.
      rewrite trans_mkApps; auto.
      rewrite trans_subst; auto.
      apply red1_mkApps_f. constructor.

    - rewrite trans_subst; eauto. repeat constructor.

    - rewrite trans_lift; eauto.
      destruct nth_error eqn:Heq.
      econstructor. unfold trans_local. rewrite nth_error_map. rewrite Heq. simpl.
      destruct c; simpl in *. injection H; intros ->. simpl. reflexivity.
      econstructor. simpl in H. discriminate.

    - rewrite trans_mkApps; eauto with wf; simpl.
      destruct a as [isdecl hci hpctx lenpar wfpar wfret wfc wfbrs].
      destruct (declared_inductive_inj isdecl (proj1 H0)). subst x x0.
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite trans_lookup_inductive.
      rewrite (declared_inductive_lookup isdecl).
      eapply All2_nth_error in wfbrs as []; tea. 2:exact (proj2 H0).
      have lenbr := (All2_length a); len in lenbr.
      rewrite (trans_iota_red _ mdecl idecl cdecl) //.
      constructor. cbn.
      rewrite map2_map_map.
      etransitivity. eapply nth_error_map2; tea. eapply H0. reflexivity.
      unfold Ast.map_branch; cbn.
      rewrite map2_map2_bias_left; len.
      rewrite PCUICCases.map2_set_binder_name_context_assumptions; len.
      rewrite H1 /bctx.
      rewrite case_branch_context_assumptions //; len.
      cbn. rewrite context_assumptions_map //.

    - simpl. rewrite trans_mkApps.
      eapply red_fix. wf_inv w.
      apply trans_unfold_fix; eauto.
      now apply trans_is_constructor.

    - destruct a as [isdecl hci hpctx lenpar wfpar wfret wfc wfbrs].
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite trans_lookup_inductive.
      rewrite (declared_inductive_lookup isdecl).
      apply WfAst.wf_mkApps_napp in wfc as []; auto.
      pose proof (unfold_cofix_wf _ _ _ _ _ H w). wf_inv w.
      rewrite !trans_mkApps; eauto with wf.
      apply trans_unfold_cofix in H; eauto with wf.
      eapply red_cofix_case; eauto.

    - eapply WfAst.wf_mkApps_napp in Hwf; auto.
      intuition. pose proof (unfold_cofix_wf _ _ _ _ _ H a). wf_inv a.
      rewrite !trans_mkApps; intuition eauto with wf.
      cbn.
      eapply red_cofix_proj; eauto.
      apply trans_unfold_cofix; eauto with wf.

    - rewrite trans_subst_instance. econstructor.
      apply (forall_decls_declared_constant _ wfΣ wfΣ' c decl H).
      now destruct decl as [na [b|] ty]; cbn; noconf H0.

    - rewrite trans_mkApps; eauto with wf.
      simpl. constructor. now rewrite nth_error_map H.

    - constructor. apply IHX. constructor; hnf; simpl; auto. hnf. auto.

    - constructor. apply IHX. constructor; hnf; simpl; auto. auto.

    - destruct a as [isdecl hci hpctx lenpar wfpar wfret wfc wfbrs].
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite trans_lookup_inductive.
      rewrite (declared_inductive_lookup isdecl).
      constructor. solve_all.
      apply OnOne2_map. apply (OnOne2_All_mix_left wfpar) in X. clear wfpar.
      solve_all.

    - destruct a as [isdecl' hci hpctx wfpar wfret wfc wfbrs].
      destruct (declared_inductive_inj isdecl isdecl').
      subst x x0.
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite trans_lookup_inductive.
      rewrite (declared_inductive_lookup isdecl).
      constructor. cbn.
      rewrite trans_local_app in IHX.
      rewrite inst_case_predicate_context_eq in IHX => //.
      eapply All2_length in hpctx; len in hpctx.
      eapply IHX => //.
      eapply All_app_inv => //.
      eapply declared_inductive_wf_case_predicate_context => //.

    - destruct a as [isdecl hci hpctx wfpar wfret wfc wfbrs].
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite trans_lookup_inductive (declared_inductive_lookup isdecl).
      constructor. cbn. apply IHX => //.

    - destruct a as [isdecl' hci hpctx lenpar wfpar wfret wfc wfbrs].
      destruct (declared_inductive_inj isdecl isdecl').
      subst x x0.
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite trans_lookup_inductive (declared_inductive_lookup isdecl).
      constructor.
      eapply OnOne2_map2.
      eapply All2_nth_hyp in wfbrs.
      rewrite /Ast.case_branches_contexts in X.
      eapply OnOne2All_map2 in X.
      2:{ now eapply All2_length in wfbrs. }
      cbn. eapply OnOne2All_map_all.
      eapply OnOne2All_All2_mix_left in X; tea.
      solve_all. red. rewrite b0. cbn. split => //.
      destruct b as [cstr [hnth [b wfbod]]].
      rewrite trans_local_app in b1.
      rewrite (inst_case_branch_context_eq _ mdecl idecl) in b1 => //.
      cbn in b1. rewrite b0 in b1. apply b1 => //.
      eapply All_app_inv => //.
      fold (Ast.case_branch_context ind mdecl i p y).
      assert (Ast.declared_constructor Σ (ind.(ci_ind), cstr) mdecl idecl i).
      { split; auto. }
      now eapply (declared_constructor_wf_case_branch_context H).

    - rewrite !trans_mkApps; auto with wf.
      eapply wf_red1 in X; auto with wf.
      eapply red1_mkApps_f; auto.

    - clear e w n. revert M1. induction X.
      simpl. intros. destruct p. specialize (r0 wfΓ).
      apply red1_mkApps_f.
      apply app_red_r. apply r0. now depelim a.
      inv a. intros. specialize (IHX X1).
      eapply (IHX (Template.Ast.tApp M1 [hd])).

    - constructor. apply IHX. constructor; hnf; simpl; auto. auto.
    - constructor. induction X; simpl; repeat constructor. apply p; auto. now inv Hwf.
      apply IHX. now inv Hwf.

    - constructor. constructor. eapply IHX; auto.
    - eapply refine_red1_r; [|constructor]. unfold subst1. simpl. now rewrite lift0_p.

    - constructor. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody.
      inversion b0. clear b0.
      intuition eauto.
      unfold map_def. simpl. congruence.

    - apply fix_red_body. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
      + unfold app_context, trans_local in b.
        simpl in a. rewrite -> map_app in b.
        unfold app_context. unfold ST.fix_context in b.
        rewrite map_rev map_mapi in b. simpl in b.
        unfold fix_context. rewrite mapi_map. simpl.
        forward b.
        { clear b. solve_all. eapply All_app_inv; auto.
          apply All_rev. apply All_mapi.
          clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
          intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
          now eapply WfAst.wf_lift.
          depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        }
        forward b by auto.
        eapply (refine_red1_Γ); [|apply b].
        f_equal. f_equal. apply mapi_ext; intros [] [].
        rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity. cbn.
        rewrite /trans_decl /= /vass. f_equal.
        now rewrite trans_lift.
      + simpl; congruence.

    - constructor. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody.
      inversion b0. clear b0.
      intuition eauto.
      unfold map_def. simpl. congruence.

    - apply cofix_red_body. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
      + unfold app_context, trans_local in b.
        simpl in a. rewrite -> map_app in b.
        unfold app_context. unfold ST.fix_context in b.
        rewrite map_rev map_mapi in b. simpl in b.
        unfold fix_context. rewrite mapi_map. simpl.
        forward b.
        { clear b. solve_all. eapply All_app_inv; auto.
          apply All_rev. apply All_mapi.
          clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
          intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
          now eapply WfAst.wf_lift.
          depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        }
        forward b by auto.
        eapply (refine_red1_Γ); [|apply b].
        f_equal. f_equal. apply mapi_ext; intros [] [].
        rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
        cbn. rewrite /trans_decl /vass /=.
        now rewrite trans_lift.
      + simpl; congruence.
    - simpl. eapply array_red_val. eapply (OnOne2_All_mix_left a) in X.
      apply OnOne2_map; solve_all.
  Qed.

  (** ** Transport of the kernel arity relations

    The translation maps a Template derivation of [whd_rel]/[arity_red] to the
    PCUIC one on the translated terms: a head cast becomes a beta-redex (two
    machine steps), an n-ary application a spine of binary ones, and the
    Template iota premises (declared constructor, branch context built from it)
    the PCUIC ones (the translated branch carries that context).  The terms
    need to be well formed ([WfAst]), as for [trans_red1]. *)

  Lemma All_cons_split {A} {P : A -> Type} {x l} : All P (x :: l) -> P x × All P l.
  Proof. intros h. depelim h. split; assumption. Qed.

  Lemma wf_red {Γ M N} :
    All (WfAst.wf_decl Σ) Γ -> WfAst.wf Σ M -> ST.red Σ Γ M N -> WfAst.wf Σ N.
  Proof.
    intros wfΓ wfM r. induction r as [|P N r IH s]; [exact wfM|].
    eapply wf_red1; [exact wf_wf_decl_pred|exact wfΓ|exact IH|exact s].
  Qed.

  (** The result of the machine on well-formed terms is well formed. *)
  Lemma whd_rel_wf {z Γ t args h l} :
    All (WfAst.wf_decl Σ) Γ -> WfAst.wf Σ t -> All (WfAst.wf Σ) args ->
    ST.whd_rel z Σ Γ t args h l -> WfAst.wf Σ h × All (WfAst.wf Σ) l.
  Proof.
    intros wfΓ wft wfargs w.
    have wfhl := wf_red wfΓ (WfAst.wf_mkApps _ _ _ wft wfargs)
      (TemplateArityRed.whd_rel_red _ _ w).
    exact (WfAst.wf_mkApps_napp Σ h l
      ltac:(now rewrite (TemplateArityRed.whd_rel_out_napp w)) wfhl).
  Qed.

  Lemma trans_whd_is_construct t : S.isApp t = false ->
    whd_is_construct (trans Σ' t) = ST.whd_is_construct t.
  Proof.
    destruct t => //= _. destruct TransLookup.lookup_inductive as [[]|] => //.
  Qed.

  Lemma trans_whd_is_construct0 t : S.isApp t = false ->
    whd_is_construct0 (trans Σ' t) = ST.whd_is_construct0 t.
  Proof.
    destruct t => //= _. destruct TransLookup.lookup_inductive as [[]|] => //.
  Qed.

  Lemma trans_whd_is_cofix t : S.isApp t = false ->
    whd_is_cofix (trans Σ' t) = ST.whd_is_cofix t.
  Proof.
    destruct t => //= _. destruct TransLookup.lookup_inductive as [[]|] => //.
  Qed.

  Lemma trans_whd_arity_head t l : S.isApp t = false ->
    whd_arity_head (trans Σ' t) (map (trans Σ') l) = ST.whd_arity_head t l.
  Proof.
    destruct t, l => //= _; try (destruct TransLookup.lookup_inductive as [[]|] => //).
  Qed.

  Lemma trans_whd_stop_head t args : ST.whd_stop_head t args ->
    whd_stop_head (trans Σ' t) (map (trans Σ') args).
  Proof. destruct t, args => //=. Qed.

  Lemma trans_whd_rel {z Γ t args h l} :
    All (WfAst.wf_decl Σ) Γ -> WfAst.wf Σ t -> All (WfAst.wf Σ) args ->
    ST.whd_rel z Σ Γ t args h l ->
    whd_rel z Σ' (trans_local Σ' Γ) (trans Σ' t) (map (trans Σ') args)
      (trans Σ' h) (map (trans Σ') l).
  Proof.
    intros wfΓ wft wfargs w. revert wft wfargs.
    induction w as [c args d b h l hnth hbod w IH|c args d hnth hbod
      |na b B t args h l hz w IH|na b B t args hz
      |c u decl body args h l hcst hbod w IH|c u decl args hcst hbod
      |c k T args h l w IH
      |f l args h l' hf hl w IH
      |na A t a args h l w IH
      |mfix idx narg fn args c ind n ui cargs h l hunf hnth wa IHa wb IHb
      |mfix idx narg fn args c t cargs hunf hnth wa IHa hnc
      |mfix idx narg fn args hunf hnth|mfix idx args hunf
      |ci p c brs args n ui cargs mdecl idecl cdecl br h l wa IHa hbr hdecl hlen wb IHb
      |ci p c brs args mfix idx cargs narg fn h l wa IHa hunf wb IHb
      |ci p c brs args t cargs wa IHa hnc hncf
      |p c args u cargs a h l wa IHa hnth wb IHb
      |p c args mfix idx cargs narg fn h l wa IHa hunf wb IHb
      |p c args t cargs wa IHa hnc hncf
      |t args hs]; intros wft wfargs.
    (* tRel, let-bound *)
    - have wfb : WfAst.wf Σ b.
      { destruct (nth_error_all hnth wfΓ) as [wdb _]. rewrite hbod in wdb. exact wdb. }
      eapply whd_rel_unfold.
      + rewrite /trans_local nth_error_map hnth. reflexivity.
      + cbn. rewrite hbod. reflexivity.
      + rewrite -trans_lift. exact (IH (WfAst.wf_lift _ _ _ _ wfb) wfargs).
    (* tRel, assumption *)
    - eapply whd_rel_assum.
      + rewrite /trans_local nth_error_map hnth. reflexivity.
      + cbn. now rewrite hbod.
    (* zeta *)
    - destruct (WfAst.wf_inv wft) as [[wfb wfB] wft'].
      eapply whd_zeta; [exact hz|].
      have tw := IH (WfAst.wf_subst1 _ _ _ _ wfb wft') wfargs.
      rewrite trans_subst in tw. exact tw.
    (* let, zeta off *)
    - apply whd_letin_stop. exact hz.
    (* delta *)
    - have wfbody : WfAst.wf Σ body.
      { destruct (declared_constant_wf _ _ wf_wf_decl_pred
          (Typing.TemplateDeclarationTyping.declared_constant_from_gen hcst)) as [wfbd _].
        rewrite hbod in wfbd. exact wfbd. }
      eapply whd_delta.
      + rewrite (trans_lookup Σ c wfΣ wfΣ') hcst. reflexivity.
      + cbn. rewrite hbod. reflexivity.
      + rewrite -trans_subst_instance.
        exact (IH (WfAst.wf_subst_instance _ _ _ wfbody) wfargs).
    (* axiom *)
    - eapply whd_axiom.
      + rewrite (trans_lookup Σ c wfΣ wfΣ') hcst. reflexivity.
      + cbn. now rewrite hbod.
    (* a head cast is a beta-redex in PCUIC *)
    - destruct (WfAst.wf_inv wft) as [wfc wfT].
      cbn [trans]. apply whd_app, whd_beta. cbn. rewrite lift0_p.
      exact (IH wfc wfargs).
    (* an n-ary application is a spine of binary ones *)
    - destruct (WfAst.wf_inv wft) as [[[_ _] wff] wfl].
      cbn [trans]. apply whd_rel_mkApps. rewrite -map_app.
      exact (IH wff (All_app_inv _ _ _ wfl wfargs)).
    (* beta *)
    - destruct (WfAst.wf_inv wft) as [wfA wft'].
      destruct (All_cons_split wfargs) as [wfa wfargs'].
      cbn [trans map]. apply whd_beta.
      have tw := IH (WfAst.wf_subst1 _ _ _ _ wfa wft') wfargs'.
      rewrite trans_subst in tw. exact tw.
    (* fix unfolding *)
    - have wfmfix := WfAst.wf_inv wft.
      have wfc : WfAst.wf Σ c := nth_error_all hnth wfargs.
      destruct (whd_rel_wf wfΓ wfc All_nil wa) as [_ wfcargs].
      have wffn := unfold_fix_wf _ _ _ _ _ hunf wft.
      have tw := IHb wffn ltac:(apply All_app_inv; [now apply All_firstn|
        constructor; [apply WfAst.wf_mkApps; [constructor|exact wfcargs]|now apply All_skipn]]).
      rewrite map_app /= -firstn_map map_skipn trans_mkApps /= in tw.
      eapply whd_fix_iota.
      + exact (trans_unfold_fix _ _ _ _ wfmfix hunf).
      + rewrite nth_error_map hnth. reflexivity.
      + exact (IHa wfc All_nil).
      + exact tw.
    (* stuck fix *)
    - have wfmfix := WfAst.wf_inv wft.
      have wfc : WfAst.wf Σ c := nth_error_all hnth wfargs.
      have ht := TemplateArityRed.whd_rel_out_napp wa.
      rewrite map_app /= -firstn_map map_skipn trans_mkApps.
      eapply whd_fix_stuck.
      + exact (trans_unfold_fix _ _ _ _ wfmfix hunf).
      + rewrite nth_error_map hnth. reflexivity.
      + exact (IHa wfc All_nil).
      + rewrite (trans_whd_is_construct t ht). exact hnc.
    - eapply whd_fix_noarg.
      + exact (trans_unfold_fix _ _ _ _ (WfAst.wf_inv wft) hunf).
      + now rewrite nth_error_map hnth.
    - apply whd_fix_nounfold.
      move: hunf. rewrite /ST.unfold_fix /unfold_fix nth_error_map.
      by destruct nth_error.
    (* iota: the Template premises give the translated branch and its context *)
    - destruct (WfAst.wf_inv wft) as [mdecl' [idecl' [isdecl hci hpctx lenpar wfpar wfret wfc wfbrs]]].
      have hdecl' : Ast.declared_constructor Σ (ci.(ci_ind), n) mdecl idecl cdecl.
      { apply Typing.TemplateDeclarationTyping.declared_constructor_from_gen.
        apply (Ast.lookup_constructor_declared_gen (lookup := Ast.Env.lookup_env Σ)
          (id := (ci.(ci_ind), n))).
        exact hdecl. }
      destruct (declared_inductive_inj isdecl (proj1 hdecl')). subst mdecl' idecl'.
      destruct (All2_nth_error _ _ _ wfbrs (proj2 hdecl') hbr) as [wfnac wfbr].
      have lenbr := All2_length wfnac. len in lenbr.
      destruct (whd_rel_wf wfΓ wfc All_nil wa) as [_ wfcargs].
      have wfiota : WfAst.wf Σ (ST.iota_red ci.(ci_npar) cargs
          (Ast.case_branch_context ci.(ci_ind) mdecl cdecl p br) br).
      { eapply (wf_red1 _ (S.tCase ci p (S.mkApps (S.tConstruct ci.(ci_ind) n ui) cargs) brs));
          [exact wf_wf_decl_pred|exact wfΓ| |].
        2:{ eapply ST.red_iota; [exact hbr|exact hdecl'|exact hlen]. }
        econstructor; tea. apply WfAst.wf_mkApps; [constructor|exact wfcargs]. }
      have tw := IHb wfiota wfargs.
      rewrite (trans_iota_red _ mdecl idecl cdecl _ _ _ _ lenbr) in tw.
      eapply forall_decls_declared_inductive in isdecl; tea.
      cbn [trans]. rewrite (trans_lookup_inductive _ wfΣ') (declared_inductive_lookup isdecl).
      eapply whd_iota.
      + exact (IHa wfc All_nil).
      + cbn. rewrite map2_map_map.
        erewrite nth_error_map2; [reflexivity|exact (proj2 hdecl')|exact hbr].
      + unfold Ast.map_branch; cbn.
        rewrite map2_map2_bias_left; len.
        rewrite PCUICCases.map2_set_binder_name_context_assumptions; len.
        rewrite hlen.
        rewrite case_branch_context_assumptions //; len.
        cbn. rewrite context_assumptions_map //.
      + exact tw.
    (* case on a cofix *)
    - destruct (WfAst.wf_inv wft) as [mdecl' [idecl' [isdecl hci hpctx lenpar wfpar wfret wfc wfbrs]]].
      destruct (whd_rel_wf wfΓ wfc All_nil wa) as [wfcofix wfcargs].
      have wffn := unfold_cofix_wf _ _ _ _ _ hunf wfcofix.
      have wfcase' : WfAst.wf Σ (S.tCase ci p (S.mkApps fn cargs) brs).
      { econstructor; tea. now apply WfAst.wf_mkApps. }
      have tw := IHb wfcase' wfargs. have ta := IHa wfc All_nil.
      have tu := trans_unfold_cofix _ _ _ _ (WfAst.wf_inv wfcofix) hunf.
      move: tw ta. cbn [trans]. rewrite trans_mkApps.
      destruct TransLookup.lookup_inductive as [[]|] => tw ta;
        (eapply whd_case_cofix; [exact ta|exact tu|exact tw]).
    (* stuck case *)
    - destruct (WfAst.wf_inv wft) as [mdecl' [idecl' [isdecl hci hpctx lenpar wfpar wfret wfc wfbrs]]].
      have ht := TemplateArityRed.whd_rel_out_napp wa.
      have ta := IHa wfc All_nil.
      move: ta. cbn [trans]. rewrite trans_mkApps.
      destruct TransLookup.lookup_inductive as [[]|] => ta;
        (eapply whd_case_stuck; [exact ta|
          rewrite (trans_whd_is_construct t ht); exact hnc|
          rewrite (trans_whd_is_cofix t ht); exact hncf]).
    (* projection *)
    - have wfc : WfAst.wf Σ c := WfAst.wf_inv wft.
      destruct (whd_rel_wf wfΓ wfc All_nil wa) as [_ wfcargs].
      eapply whd_proj.
      + exact (IHa wfc All_nil).
      + now rewrite nth_error_map hnth.
      + exact (IHb (nth_error_all hnth wfcargs) wfargs).
    (* projection of a cofix *)
    - have wfc : WfAst.wf Σ c := WfAst.wf_inv wft.
      destruct (whd_rel_wf wfΓ wfc All_nil wa) as [wfcofix wfcargs].
      have wffn := unfold_cofix_wf _ _ _ _ _ hunf wfcofix.
      have wfproj : WfAst.wf Σ (S.tProj p (S.mkApps fn cargs)).
      { constructor. now apply WfAst.wf_mkApps. }
      have tw := IHb wfproj wfargs.
      cbn [trans] in tw. rewrite trans_mkApps in tw.
      eapply whd_proj_cofix.
      + exact (IHa wfc All_nil).
      + exact (trans_unfold_cofix _ _ _ _ (WfAst.wf_inv wfcofix) hunf).
      + exact tw.
    (* stuck projection *)
    - have wfc : WfAst.wf Σ c := WfAst.wf_inv wft.
      have ht := TemplateArityRed.whd_rel_out_napp wa.
      cbn [trans]. rewrite trans_mkApps.
      eapply whd_proj_stuck.
      + exact (IHa wfc All_nil).
      + rewrite (trans_whd_is_construct0 t ht). exact hnc.
      + rewrite (trans_whd_is_cofix t ht). exact hncf.
    (* the machine stops *)
    - apply whd_stop. now apply trans_whd_stop_head.
  Qed.

  Lemma trans_arity_red {Γ t Δ s} :
    All (WfAst.wf_decl Σ) Γ -> WfAst.wf Σ t ->
    ST.arity_red Σ Γ t Δ s ->
    arity_red Σ' (trans_local Σ' Γ) (trans Σ' t) (trans_local Σ' Δ) s.
  Proof.
    intros wfΓ wft ar. revert wfΓ wft.
    induction ar as [Γ t s w|Γ t na A B Δ s w ar IH|Γ t na b A B Δ s w ar IH
      |Γ t h l h' l' Δ s w ha w' hne ar IH]; intros wfΓ wft.
    - apply arity_red_sort. exact (trans_whd_rel wfΓ wft All_nil w).
    - destruct (whd_rel_wf wfΓ wft All_nil w) as [wfprod _].
      destruct (WfAst.wf_inv wfprod) as [wfA wfB].
      rewrite /trans_local map_app /=.
      eapply arity_red_prod; [exact (trans_whd_rel wfΓ wft All_nil w)|].
      exact (IH ltac:(constructor; [exact (tt, wfA)|exact wfΓ]) wfB).
    - destruct (whd_rel_wf wfΓ wft All_nil w) as [wflet _].
      destruct (WfAst.wf_inv wflet) as [[wfb wfA] wfB].
      rewrite /trans_local map_app /=.
      eapply arity_red_let; [exact (trans_whd_rel wfΓ wft All_nil w)|].
      exact (IH ltac:(constructor; [exact (wfb, wfA)|exact wfΓ]) wfB).
    - destruct (whd_rel_wf wfΓ wft All_nil w) as [wfh wfl].
      have wfhl := WfAst.wf_mkApps _ _ _ wfh wfl.
      destruct (whd_rel_wf wfΓ wfhl All_nil w') as [wfh' wfl'].
      have wfhl' := WfAst.wf_mkApps _ _ _ wfh' wfl'.
      have ht := TemplateArityRed.whd_rel_out_napp w.
      have tw := trans_whd_rel wfΓ wft All_nil w.
      have tw' := trans_whd_rel wfΓ wfhl All_nil w'.
      rewrite trans_mkApps in tw'.
      have haT : whd_arity_head (trans Σ' h) (map (trans Σ') l) = false.
      { rewrite (trans_whd_arity_head h l ht). exact ha. }
      have ta := IH wfΓ wfhl'. rewrite trans_mkApps in ta.
      (* the translation is not injective, but the target derivation [ta]
         itself gives the progress premise *)
      eapply arity_red_fallback;
        [exact tw|exact haT|exact tw'|exact (arity_red_fallback_progress tw haT tw' ta)|exact ta].
  Qed.
End Trans_Global.

Lemma global_levels_trans Σ
  : global_levels (trans_global_env Σ) = Ast.global_levels Σ.(Ast.Env.universes).
Proof.
  induction Σ; simpl; auto. cbn.
  induction declarations0; cbn; auto.
Qed.

Lemma global_constraints_trans Σ
  : global_constraints (trans_global_env Σ) = Ast.global_constraints Σ.
Proof.
  induction Σ; simpl; auto. cbn.
  induction declarations0; cbn; auto.
Qed.

Lemma global_ext_levels_trans Σ
  : global_ext_levels (trans_global Σ) = Ast.global_ext_levels Σ.
Proof.
  destruct Σ.
  unfold trans_global, Ast.global_ext_levels, global_ext_levels; simpl.
  now rewrite global_levels_trans.
Qed.

Lemma global_ext_constraints_trans Σ
  : global_ext_constraints (trans_global Σ) = Ast.global_ext_constraints Σ.
Proof.
  destruct Σ.
  unfold trans_global, Ast.global_ext_constraints, global_ext_constraints; simpl.
  now rewrite global_constraints_trans.
Qed.

Lemma trans_cumul_gen {cf} (Σ : Ast.Env.global_env_ext) pb Γ T U :
  Typing.wf Σ ->
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ T -> WfAst.wf Σ U -> ST.cumul_gen Σ Γ pb T U ->
  trans_global Σ ;;; trans_local Σ' Γ |- trans Σ' T <=[pb] trans Σ' U.
Proof.
  intros wfΣ Σ' wfΣ'.
  induction 4.
  - constructor.
    destruct pb.
    * eapply trans_eq_term in c; eauto.
      now rewrite global_ext_constraints_trans.
    * eapply trans_leq_term in c; eauto.
      now rewrite global_ext_constraints_trans.
  - eapply cumul_red_l; tea. eapply trans_red1; tea. apply IHX2.
    eapply wf_red1 in r; tea. now eapply typing_wf_sigma in wfΣ. auto.
  - eapply cumul_red_r; tea. 2:eapply trans_red1; tea.
    eapply IHX2. auto. eapply wf_red1 in r; tea. now eapply typing_wf_sigma; auto.
Qed.

Lemma trans_lift_typing_it {P Q} {tm tm'} {t t'} {u r} :
  forall tu: ST.lift_typing0 P (Judge tm t u r),
  let s := tu.2.π1 in
  match tm', tm with None, _ => unit | Some tm', Some tm => P tm t -> Q tm' t' | _, _ => False end ->
  (P t (Ast.tSort s) -> Q t' (tSort s)) ->
  lift_typing0 Q (Judge tm' t' u r).
Proof.
  intros (? & ? & Hs & e) s HPQc HPQs.
  split.
  - destruct tm, tm' => //=. now apply HPQc.
  - eexists. split; [now apply HPQs|].
    destruct u => //.
Qed.

Definition TTy_wf_local {cf : checker_flags} Σ Γ := ST.All_local_env (ST.lift_typing ST.typing Σ) Γ.

Lemma trans_wf_local {cf}:
  forall (Σ : Ast.Env.global_env_ext) (Γ : Ast.Env.context) (wfΓ : TTy_wf_local Σ Γ),
    let P :=
        (fun Γ0 _ (t T : Ast.term) _ =>
           let Σ' := trans_global Σ in
           wf Σ'.1 ->
           trans_global Σ;;; trans_local Σ' Γ0 |- trans Σ' t : trans Σ' T)
    in
    let Σ' := trans_global Σ in
    wf Σ' ->
    ST.All_local_env_over (ST.typing Σ) P Γ wfΓ ->
    wf_local (trans_global Σ) (trans_local Σ' Γ).
Proof.
  intros.
  induction X0.
  - simpl. constructor.
  - simpl. econstructor; auto.
    simpl. eapply trans_lift_typing_it with tu => //. eauto.
  - simpl. constructor; auto.
    simpl. eapply trans_lift_typing_it with tu => //. all: eauto.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun Σ Γ (b ty : Ast.term) =>
            let Σ' := trans_global Σ in
              ST.typing Σ Γ b ty × trans_global Σ;;; trans_local Σ' Γ |- trans Σ' b : trans Σ' ty) Σ)
        Γ ->
  wf_local (trans_global Σ) (trans_local (trans_global Σ) Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor; auto.
    simpl. eapply trans_lift_typing_it with t0 => // HT. now apply HT.
  - simpl. constructor; auto.
    simpl. eapply trans_lift_typing_it with t0 => // HT. all: now apply HT.
Qed.

#[global]
Hint Resolve trans_wf_local : trans.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    let Σ' := trans_global Σ in
    fix_guard Σ' (trans_local Σ' Γ) (map (map_def (trans Σ') (trans Σ')) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
    ST.cofix_guard Σ Γ mfix ->
    let Σ' := trans_global Σ in
    cofix_guard Σ' (trans_local Σ' Γ) (map (map_def (trans Σ') (trans Σ')) mfix).

Notation Swf_fix Σ def := (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)).

Lemma trans_decompose_app {Σ t ind u l} :
  WfAst.wf Σ t ->
  let Σ' := trans_global_env Σ in
  AstUtils.decompose_app t = (Ast.tInd ind u, l) ->
  ∑ l', decompose_app (trans Σ' t) = (tInd ind u, l').
Proof.
  intros wft. destruct (AstUtils.decompose_app t) eqn:da.
  pose proof (TypingWf.decompose_app_inv _ _ [] _ _ wft da) as [n [napp [eqsk ->]]].
  intros Σ'. intros [= -> ->].
  rewrite trans_mkApps.
  rewrite decompose_app_mkApps //. eexists _; eauto.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn ctx t ctx' t' :
  AstUtils.decompose_prod_assum ctx t = (ctx', t') ->
  Ast.Env.it_mkProd_or_LetIn ctx t = Ast.Env.it_mkProd_or_LetIn ctx' t'.
Proof.
  induction t in ctx, ctx', t' |- *; simpl; try intros [= -> <-]; auto.
  - intros H. now apply IHt2 in H.
  - intros H. now apply IHt3 in H.
Qed.

Lemma trans_decompose_prod_assum {Σ Σ'} ctx t :
  WfAst.wf Σ t ->
  let (ctx', t') := AstUtils.decompose_prod_assum ctx t in
  decompose_prod_assum (trans_local Σ' ctx) (trans Σ' t) =
    (trans_local Σ' ctx', trans Σ' t').
Proof.
  intros wft;
  induction wft in ctx |- * using WfAst.term_wf_forall_list_ind ; cbn; try intros [= <- <-]; auto.
  - apply IHwft0.
  - apply IHwft1.
  - rewrite mkApps_nonempty //.
    now destruct l => //.
  - cbn. destruct TransLookup.lookup_inductive as [[mdecl' idecl']| ]; cbn => //.
Qed.

Lemma wf_it_mkProd_or_LetIn Σ Γ t
  : WfAst.wf Σ (Ast.Env.it_mkProd_or_LetIn Γ t) <~> All (WfAst.wf_decl Σ) Γ * WfAst.wf Σ t.
Proof.
  revert t. induction Γ.
  - intros t. simpl. split => //; try split => //; trivial. now intros [].
  - intros t.
    destruct a as [na [b|] ty]; simpl in *. rewrite /Ast.Env.mkProd_or_LetIn /=.
    * etransitivity. eapply IHΓ. split; intros [].
      depelim w. intuition constructor; auto. split; auto.
      depelim a. red in w. simpl in w. split; auto with wf. constructor; intuition auto.
    * etransitivity. eapply IHΓ => /=. split; intros [].
      depelim w. simpl in w1. split; [constructor|];auto.
      split; simpl; auto.
      depelim a. destruct w as [_ wfty]. simpl in wfty.
      split; auto. constructor; simpl; auto.
Qed.

From MetaRocq.PCUIC Require Import PCUICClosed PCUICClosedTyp.

(** Reduction is translated step by step, and the Template well-formedness
    predicate is preserved along it. *)
Lemma trans_red {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {Γ T U} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ T ->
  ST.red Σ Γ T U ->
  WfAst.wf Σ U × red Σ' (trans_local Σ' Γ) (trans Σ' T) (trans Σ' U).
Proof.
  intros Σ' wfΣ' wfΓ wfT r.
  induction r as [|P N rr IH r1].
  - split; [exact wfT|]. apply refl_red.
  - destruct IH as [wfP redP]. split.
    * eapply wf_red1; tea. now eapply typing_wf_sigma.
    * eapply red_trans; [exact redP|].
      eapply red1_red. eapply trans_red1; tea.
Qed.

(** A Template reduction of a well-formed type gives, on the PCUIC side, a
    conversion to a well-scoped reduct: exactly the witness [fix_on_ind] and
    [cofix_on_ind] ask for. *)
Lemma trans_red_convSpec {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {Γ T U} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  is_closed_context (trans_local Σ' Γ) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' T) ->
  WfAst.wf Σ T ->
  ST.red Σ Γ T U ->
  WfAst.wf Σ U × is_open_term (trans_local Σ' Γ) (trans Σ' U)
    × (Σ' ;;; trans_local Σ' Γ |- trans Σ' T =s trans Σ' U).
Proof.
  intros Σ' wfΣ' wfΓ clΓ opT wfT r.
  have [wfU redU] : WfAst.wf Σ U × red Σ' (trans_local Σ' Γ) (trans Σ' T) (trans Σ' U).
  { eapply trans_red; tea. }
  have conv : Σ' ;;; trans_local Σ' Γ ⊢ trans Σ' T ≤[Conv] trans Σ' U.
  { eapply red_ws_cumul_pb; tea. split; tea. }
  split; [exact wfU|]. split.
  - eapply ws_cumul_pb_is_open_term_right; tea.
  - exact (@cumulAlgo_cumulSpec _ _ Conv _ _ _ conv).
Qed.

Lemma trans_has_rec_arg Σ d :
  let Σ' := trans_global_env Σ in
  WfAst.wf Σ (dtype d) ->
  ST.has_rec_arg d ->
  has_rec_arg (map_def (trans Σ') (trans Σ') d).
Proof.
  intros Σ'.
  unfold ST.has_rec_arg, has_rec_arg.
  case: d => [na ty bod arg] /= wfty.
  generalize (trans_decompose_prod_assum (Σ' := Σ') [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] => /= // ->.
  rewrite /trans_local context_assumptions_map //.
Qed.

Lemma trans_def_with_type Σ' d ty :
  map_def (trans Σ') (trans Σ') (ST.def_with_type d ty) =
  def_with_type (map_def (trans Σ') (trans Σ') d) (trans Σ' ty).
Proof. reflexivity. Qed.

Lemma trans_check_one_fix Σ mfix ind :
  let Σ' := trans_global_env Σ in
  Swf_fix Σ mfix ->
  ST.check_one_fix mfix = Some ind ->
  check_one_fix (map_def (trans Σ') (trans Σ') mfix) = Some ind.
Proof.
  intros Σ'.
  unfold ST.check_one_fix, check_one_fix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  generalize (trans_decompose_prod_assum (Σ' := Σ') [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  rewrite -(trans_smash_context Σ []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error eqn:hnth => /= //.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' eq] := (trans_decompose_app (Σ := Σ) _ da).
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    eapply wf_it_mkProd_or_LetIn in wfty as [wfctx _].
    eapply nth_error_all in hnth; cycle 1.
    eapply All_rev.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev // List.rev_involutive in hnth.
    now apply wf_smash_context. apply hnth. }
  destruct c => /=. rewrite eq /= //.
Qed.

Lemma trans_check_one_cofix Σ mfix ind :
  let Σ' := trans_global_env Σ in
  Swf_fix Σ mfix ->
  ST.check_one_cofix mfix = Some ind ->
  check_one_cofix (map_def (trans Σ') (trans Σ') mfix) = Some ind.
Proof.
  intros Σ'. unfold ST.check_one_cofix, check_one_cofix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  move: (trans_decompose_prod_assum (Σ := Σ) (Σ' := Σ') [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' ->] := (trans_decompose_app (Σ := Σ) _ da) => //.
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    now eapply wf_it_mkProd_or_LetIn in wfty as [_ wfp]. }
Qed.

Lemma trans_check_rec_kind {cf} {Σ} {wfΣ : Typing.wf Σ} {wfΣ' : wf (trans_global_env Σ)} {k f} :
  ST.check_recursivity_kind Σ k f = check_recursivity_kind (lookup_env (trans_global_env Σ)) k f.
Proof.
  unfold ST.check_recursivity_kind, check_recursivity_kind.
  rewrite trans_lookup.
  destruct Ast.Env.lookup_env as [[]|] => //.
Qed.

Lemma trans_check_rec_kind_impl {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {k f} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  ST.check_recursivity_kind Σ k f ->
  check_recursivity_kind (lookup_env Σ') k f.
Proof.
  intros Σ' wfΣ' h.
  now rewrite (@trans_check_rec_kind cf Σ wfΣ wfΣ' k f) in h.
Qed.

Lemma trans_fix_on_ind {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {Γ mind d} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  is_closed_context (trans_local Σ' Γ) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' (dtype d)) ->
  WfAst.wf Σ (dtype d) -> WfAst.wf Σ (dbody d) ->
  ST.fix_on_ind Σ Γ mind d ->
  fix_on_ind Σ' (trans_local Σ' Γ) mind (map_def (trans Σ') (trans Σ') d).
Proof.
  intros Σ' wfΣ' wfΓ clΓ opd wfty wfbod [hr [ty [hc hred]]].
  have [wfty' [opty conv]] :
    WfAst.wf Σ ty × is_open_term (trans_local Σ' Γ) (trans Σ' ty)
      × (Σ' ;;; trans_local Σ' Γ |- trans Σ' (dtype d) =s trans Σ' ty).
  { eapply trans_red_convSpec; tea. }
  split.
  { now eapply trans_has_rec_arg. }
  exists (trans Σ' ty). split; [|split].
  - rewrite -trans_def_with_type.
    eapply (trans_check_one_fix Σ); [|exact hc].
    split; cbn; [exact wfty'|exact wfbod].
  - exact opty.
  - exact conv.
Qed.

Lemma trans_cofix_on_ind {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {Γ mind d} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  is_closed_context (trans_local Σ' Γ) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' (dtype d)) ->
  WfAst.wf Σ (dtype d) -> WfAst.wf Σ (dbody d) ->
  ST.cofix_on_ind Σ Γ mind d ->
  cofix_on_ind Σ' (trans_local Σ' Γ) mind (map_def (trans Σ') (trans Σ') d).
Proof.
  intros Σ' wfΣ' wfΓ clΓ opd wfty wfbod [ty [hc hred]].
  have [wfty' [opty conv]] :
    WfAst.wf Σ ty × is_open_term (trans_local Σ' Γ) (trans Σ' ty)
      × (Σ' ;;; trans_local Σ' Γ |- trans Σ' (dtype d) =s trans Σ' ty).
  { eapply trans_red_convSpec; tea. }
  exists (trans Σ' ty). split; [|split].
  - rewrite -trans_def_with_type.
    eapply (trans_check_one_cofix Σ); [|exact hc].
    split; cbn; [exact wfty'|exact wfbod].
  - exact opty.
  - exact conv.
Qed.

Lemma trans_wf_fixpoint {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {Γ mfix} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  is_closed_context (trans_local Σ' Γ) ->
  All (fun def => (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def))) mfix ->
  All (fun def => is_open_term (trans_local Σ' Γ) (trans Σ' (dtype def))) mfix ->
  ST.wf_fixpoint Σ Γ mfix ->
  wf_fixpoint Σ' (trans_local Σ' Γ) (map (map_def (trans Σ') (trans Σ')) mfix).
Proof.
  intros Σ' wfΣ' wfΓ clΓ wfm opm [isl [mind [ne [hall hk]]]].
  split.
  { apply All_forallb. eapply All_map.
    eapply (All_impl (forallb_All _ _ isl)).
    intros d h. destruct d as [na ty bod arg]; cbn in h |- *.
    now destruct bod. }
  exists mind. split; [|split].
  - destruct mfix => //.
  - eapply All_map, (All_impl (All_prod _ _ _ _ (All_prod _ _ _ _ wfm opm) hall)).
    intros d [[[wfty wfbod] opd] hfix].
    eapply trans_fix_on_ind; tea.
  - now eapply trans_check_rec_kind_impl.
Qed.

Lemma trans_wf_cofixpoint {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {Γ mfix} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  is_closed_context (trans_local Σ' Γ) ->
  All (fun def => (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def))) mfix ->
  All (fun def => is_open_term (trans_local Σ' Γ) (trans Σ' (dtype def))) mfix ->
  ST.wf_cofixpoint Σ Γ mfix ->
  wf_cofixpoint Σ' (trans_local Σ' Γ) (map (map_def (trans Σ') (trans Σ')) mfix).
Proof.
  intros Σ' wfΣ' wfΓ clΓ wfm opm [mind [ne [hall hk]]].
  exists mind. split; [|split].
  - destruct mfix => //.
  - eapply All_map, (All_impl (All_prod _ _ _ _ (All_prod _ _ _ _ wfm opm) hall)).
    intros d [[[wfty wfbod] opd] hcofix].
    eapply trans_cofix_on_ind; tea.
  - now eapply trans_check_rec_kind_impl.
Qed.

Lemma trans_global_decl_universes Σ d :
  Ast.universes_decl_of_decl d =
  universes_decl_of_decl (trans_global_decl Σ d).
Proof.
  destruct d; reflexivity.
Qed.

Lemma trans_consistent_instance_ext {cf:checker_flags} Σ d u :
  let Σ' := trans_global Σ in
  Ast.consistent_instance_ext Σ (Ast.universes_decl_of_decl d) u ->
  consistent_instance_ext Σ' (universes_decl_of_decl (trans_global_decl Σ' d)) u.
Proof.
  intros Σ'.
  unfold Ast.consistent_instance_ext, consistent_instance_ext.
  rewrite global_ext_levels_trans global_ext_constraints_trans.
  rewrite (trans_global_decl_universes Σ').
  trivial.
Qed.

Lemma eq_annots_expand_lets_ctx (Γ : list aname) (Δ Δ' : context) :
  eq_annots Γ (expand_lets_ctx Δ Δ') <-> eq_annots Γ Δ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  etransitivity. eapply eq_annots_subst_context.
  eapply eq_annots_lift_context.
Qed.

Lemma eq_annots_ind_predicate_context ind mdecl idecl (pctx : list aname) :
  eq_annots pctx (ind_predicate_context ind mdecl idecl) ->
  eq_annots pctx (idecl_binder idecl :: ind_indices idecl).
Proof.
  rewrite /ind_predicate_context.
  intros eq. depelim eq; cbn in *.
  constructor => //.
  now eapply eq_annots_expand_lets_ctx.
Qed.

Lemma eq_annots_cstr_branch_context ind mdecl cdecl (pctx : list aname) :
  eq_annots pctx (cstr_branch_context ind mdecl cdecl) ->
  eq_annots pctx (cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context.
  intros eq.
  eapply eq_annots_subst_context.
  now eapply eq_annots_expand_lets_ctx.
Qed.

From MetaRocq.PCUIC Require Import PCUICValidity PCUICContexts PCUICInductives PCUICInductiveInversion.

Lemma isType_mkApps_Ind_inv_spine {cf:checker_flags} {Σ : global_env_ext} {Γ ind u args} {wfΣ : wf Σ} {mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  ∑ s, PCUICSpine.spine_subst Σ Γ args s (ind_params mdecl ,,, ind_indices idecl)@[u] ×
        consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> isdecl isty.
  pose proof (isType_wf_local isty).
  destruct isty as (_ & s & Hs & _).
  eapply invert_type_mkApps_ind in Hs as [sp cu]; tea.
  eapply (typing_spine_ind_type_inv isdecl) in sp; tea.
  rewrite subst_instance_it_mkProd_or_LetIn /= in sp.
  eapply PCUICSpine.arity_typing_spine in sp as [hle hs [insts sp]]; tea.
  exists insts. split => //.
Qed.

Lemma simpl_type_Case {H : checker_flags} {Σ : global_env_ext} {Γ} {ci : case_info} {p c brs ps mdecl idecl indices} {wfΣ : wf Σ} :
  declared_inductive Σ ci mdecl idecl ->
  ind_npars mdecl = ci_npar ci ->
  eq_context_upto_names (pcontext p)
  (ind_predicate_context ci mdecl idecl) ->
  let predctx := case_predicate_context ci mdecl idecl p in
  wf_predicate mdecl idecl p ->
  wf_local Σ (Γ,,, predctx) ->
  Σ;;; Γ,,, predctx |- preturn p : tSort ps ->
  is_allowed_elimination Σ (ind_kelim idecl) ps ->
  isSortRel ps ci.(ci_relevance) ->
  Σ;;; Γ |- c : mkApps (tInd ci (puinst p)) (pparams p ++ indices) ->
  isCoFinite (ind_finite mdecl) = false ->
  let ptm := it_mkLambda_or_LetIn predctx (preturn p) in
  wf_branches idecl brs ->
  All2i
  (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
  eq_context_upto_names (bcontext br)
  (cstr_branch_context ci mdecl cdecl) *
  (let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
    Σ;;; Γ,,, brctxty.1 |- bbody br : brctxty.2 ×
    Σ;;; Γ,,, brctxty.1 |- brctxty.2 : tSort ps)) 0
  (ind_ctors idecl) brs ->
  Σ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c]).
Proof.
  intros.
  assert (hty := validity X2).
  eapply isType_mkApps_Ind_inv_spine in hty as [inst [sp cu]]; tea.
  eapply type_Case; tea; split => //.
  - now eapply PCUICSpine.spine_subst_ctx_inst.
  - solve_all. now eapply typing_wf_local in a0.
Qed.

From MetaRocq.PCUIC Require Import PCUICOnFreeVars.

Lemma trans_cumulSpec {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {pb Γ T T'} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ T ->
  WfAst.wf Σ T' ->
  ST.cumul_gen Σ Γ pb T T' ->
  is_closed_context (trans_local Σ' Γ) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' T) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' T') ->
  Σ';;; trans_local Σ' Γ ⊢ trans Σ' T ≤s[pb] trans Σ' T'.
Proof.
  intros Σ' wfΣ' wfΓ wfT wfT' cum clΓ clT clT'.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (pb:=pb)).
  eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; eauto with fvs.
  eapply trans_cumul_gen; tea.
Qed.

Local Hint Resolve isType_is_open_term : fvs.

Global Instance wf_trans_env {cf} {Σ : global_env_ext_map} : wf Σ -> wf (global_env_ext_map_global_env_map Σ).
Proof. now cbn. Qed.
Global Hint Resolve wf_trans_env : fvs.

Lemma trans_cumulSpec_typed {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ} {pb Γ T T'} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ T ->
  WfAst.wf Σ T' ->
  ST.cumul_gen Σ Γ pb T T' ->
  isType Σ' (trans_local Σ' Γ) (trans Σ' T) ->
  isType Σ' (trans_local Σ' Γ) (trans Σ' T') ->
  Σ';;; trans_local Σ' Γ ⊢ trans Σ' T ≤s[pb] trans Σ' T'.
Proof.
  intros Σ' wfΣ' wfΓ wfT wfT' cum ist ist'.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (pb:=pb)).
  eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; eauto with fvs.
  eapply trans_cumul_gen; tea.
  eapply isType_wf_local in ist; fvs.
Qed.

Lemma trans_case_branch_type Σ (ci : case_info) mdecl idecl cdecl i p br :
  let Σ' := trans_global_env Σ in
  let bctx := Ast.case_predicate_context ci mdecl idecl p in
  let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
  let mdecl' := trans_minductive_body Σ' mdecl in
  let idecl' := trans_one_ind_body Σ' idecl in
  let cdecl' := trans_constructor_body Σ' cdecl in
  let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
  let br' := trans_branch ci mdecl' cdecl' br.(Ast.bcontext) (trans Σ' br.(Ast.bbody)) in
  let ptm := Ast.Env.it_mkLambda_or_LetIn bctx (Ast.preturn p) in
  let ptm' := it_mkLambda_or_LetIn (case_predicate_context ci mdecl' idecl' p') (preturn p') in
  WfAst.wf_nactx (Ast.pcontext p) (Ast.ind_predicate_context ci mdecl idecl) ->
  WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci mdecl cdecl) ->
  let brctxty := Ast.case_branch_type ci mdecl p ptm i cdecl br in
  let brctxty' := case_branch_type ci mdecl' idecl' p' br' ptm' i cdecl' in
  brctxty'.1 = trans_local Σ' brctxty.1 /\
  brctxty'.2 = trans Σ' brctxty.2.
Proof.
  intros.
  split.
  * rewrite /brctxty' /= /id.
    rewrite (trans_case_branch_context Σ ci mdecl idecl cdecl) //.
  * rewrite /brctxty' /brctxty.
    rewrite /case_branch_type /case_branch_type_gen /Ast.case_branch_type /Ast.case_branch_type_gen.
    cbv beta iota delta [snd].
    rewrite trans_mkApps trans_lift. f_equal.
    { rewrite /cdecl'; len. f_equal.
      rewrite /ptm' /ptm trans_it_mkLambda_or_LetIn // /p'0 /=. f_equal.
      rewrite /bctx.
      rewrite [map _ (Ast.case_predicate_context _ _ _ _)](trans_case_predicate_context Σ ci mdecl idecl p) //.
      eapply All2_length in X. len in X. }
    rewrite map_app /=. f_equal.
    { rewrite !map_map_compose. eapply map_ext => x.
      rewrite trans_subst map_rev; f_equal; len.
      rewrite trans_expand_lets_k. f_equal.
      rewrite trans_local_subst_instance //.
      rewrite trans_subst trans_inds; f_equal.
      now rewrite trans_subst_instance. }
    f_equal.
    rewrite trans_mkApps. f_equal.
    rewrite map_app. f_equal.
    rewrite !map_map_compose.
    apply map_ext => x. rewrite trans_lift. f_equal; len.
    rewrite trans_reln //.
Qed.

Lemma trans_wf_sort Σ u : S.wf_sort Σ u ->
  wf_sort (trans_global Σ) u.
Proof.
  unfold S.wf_sort, wf_sort, S.wf_universe, wf_universe.
  now rewrite global_ext_levels_trans.
Qed.

Lemma trans_env_retroknowledge Σ : retroknowledge (trans_global_env Σ) = S.Env.retroknowledge Σ.
Proof.
  destruct Σ as [univs decls retro].
  rewrite /trans_global_env /=.
  induction decls; cbn; auto.
Qed.

Local Hint Resolve trans_wf_sort : trans.
Local Hint Transparent Ast.Env.global_env_ext : trans.
Local Hint Transparent sort : trans.
Local Hint Variables Transparent : trans.
Ltac trans := try typeclasses eauto with trans.
(* bug in Rocq, typeclasses eauto tries exact with a quantified hypothesis starting with a let-in *)
Ltac simpl_let :=
  match goal with
  | [ H : let _ := _ in _ |- _ ] => progress (cbv zeta in H)
  end.
Local Hint Extern 4 => simpl_let : trans.

Theorem template_to_pcuic {cf} :
  ST.env_prop (fun Σ Γ t T =>
    let Σ' := trans_global Σ in
    wf Σ' ->
    typing Σ' (trans_local Σ' Γ) (trans Σ' t) (trans Σ' T))
    (fun Σ Γ j =>
      let Σ' := trans_global Σ in
      wf Σ' ->
      lift_typing typing Σ' (trans_local Σ' Γ) (judgment_map (trans Σ') j)
    )
    (fun Σ Γ _ =>
      let Σ' := trans_global Σ in
      wf Σ' ->
      wf_local Σ' (trans_local Σ' Γ)).
Proof.
  apply ST.typing_ind_env.
  all: intros.
  all: try solve [ econstructor; trans ].

  - destruct X as (Hb & s & (_ & Ht) & e). unfold judgment_map.
    split; cbn.
    + destruct j_term => //=. now eapply Hb.
    + exists s. split; tas. now eapply Ht.

  - eapply trans_wf_local; eauto.

  - rewrite trans_lift.
    eapply refine_type. eapply type_Rel; eauto.
    unfold trans_local. rewrite nth_error_map. rewrite H. reflexivity.
    f_equal.

  - (* Casts *)
    assert (lift_typing0 (typing Σ' (trans_local (trans_global_env Σ.1) Γ)) (TypUnivRel (trans (trans_global_env Σ.1) t) s rel_of_Type)).
    { repeat (eexists; eauto). }
    apply lift_sorting_forget_univ in X4 as X4'.
    eapply refine_type; cbn.
    * eapply type_App.
      2:{ eapply type_Lambda; eauto. eapply type_Rel. econstructor; eauto.
        eapply typing_wf_local; eauto. reflexivity. }
      eapply type_Prod. eauto.
      instantiate (1 := s). simpl.
      eapply (weakening _ _ [_] _ (tSort _)); eauto.
      constructor; eauto. eapply typing_wf_local; eauto.
      now eapply X2.
    * unfold subst1. rewrite simpl_subst; auto. now rewrite lift0_p.

  - cbn. econstructor; trans. 1: now eapply X1.
    cbn in *. trans. cbn in *; trans. now apply X3.

  - econstructor; eauto with trans.
  - econstructor; eauto with trans.

  - (* The interesting application case *)
    cbn; eapply type_mkApps; eauto.
    specialize (X0 X2).
    eapply typing_wf in X; eauto. destruct X.
    eapply PCUICValidity.validity in X0.
    clear H H0.
    induction X1.
    * econstructor; eauto. reflexivity.
    * simpl in p.
      destruct (TypingWf.typing_wf _ wfΣ _ _ _ typrod) as [wfAB _].
      econstructor; eauto.
      + now eapply has_sort_isType.
      + rewrite -/Σ'.
        change (tProd na (trans Σ' A) (trans _ B)) with (trans Σ' (Ast.tProd na A B)).
        eapply trans_cumulSpec_typed; tea.
        eapply TypingWf.typing_all_wf_decl; eauto.
        now eapply has_sort_isType.
      + eapply typing_wf in ty; eauto. destruct ty as [wfhd _].
        rewrite trans_subst in IHX1; eauto with wf.
        eapply IHX1; cycle 1.
        2:apply WfAst.wf_subst; try constructor; auto. 2:now inv wfAB.
        specialize (p X2). specialize (p0 X2).
        eapply PCUICInversion.inversion_Prod in p as [s1 [s2 [HA [HB Hs]]]]; auto.
        eapply (isType_subst (Δ := [vass na (trans Σ' A)])); eauto.
        eapply subslet_ass_tip. eauto with pcuic.
        now eapply has_sort_isType.

  - cbn; rewrite trans_subst_instance.
    pose proof (forall_decls_declared_constant _ _ _ _ _ H).
    rewrite -/Σ'.
    replace (trans _ (Ast.Env.cst_type decl)) with
        (cst_type (trans_constant_body Σ' decl)) by (destruct decl; reflexivity).
    econstructor; eauto with trans.
    now apply (trans_consistent_instance_ext Σ (Ast.Env.ConstantDecl decl)).

  - rewrite trans_subst_instance.
    pose proof (forall_decls_declared_inductive _ _ _ _ _ _ isdecl).
    rewrite -/Σ'.
    replace (trans _ (Ast.Env.ind_type idecl)) with
        (ind_type (trans_one_ind_body Σ' idecl)) by (destruct idecl; reflexivity).
    eapply type_Ind; eauto.
    now apply (trans_consistent_instance_ext Σ (Ast.Env.InductiveDecl mdecl)).

  - pose proof (forall_decls_declared_constructor _ _ _ _ _ _ _ isdecl).
    unfold ST.type_of_constructor in *.
    rewrite trans_subst.
    rewrite trans_subst_instance.
    rewrite trans_inds. simpl.
    eapply refine_type. econstructor; eauto with trans.
    now apply (trans_consistent_instance_ext Σ (Ast.Env.InductiveDecl mdecl)).
    reflexivity.

  - cbn; rewrite trans_mkApps; auto with wf trans.
    pose proof (forall_decls_declared_inductive _ _ _ _ _ _ isdecl).
    rewrite trans_lookup_inductive.
    rewrite (declared_inductive_lookup _ H5).
    rewrite trans_it_mkLambda_or_LetIn.
    rewrite -/(trans_local Σ' (Ast.case_predicate_context _ _ _ _)).
    have lenpctx : #|Ast.pcontext p| = S #|Ast.Env.ind_indices idecl|.
    { eapply All2_length in X1; len in X1. }
    rewrite (trans_case_predicate_context Σ) //.
    rewrite map_app.
    specialize (X6 X8).
    specialize (X4 X8).
    set (p' := trans_predicate _ _ _ _ _ _ _).
    eapply (simpl_type_Case (p:=p') (ps:=ps)) => //.
    + cbn. rewrite map2_map2_bias_left; len.
      eapply eq_binder_annots_eq.
      now eapply trans_ind_predicate_context.
    + cbn. split. cbn.
      { epose proof (declared_minductive_ind_npars (proj1 H5)).
        cbn in H4. len. rewrite -H0.
        now rewrite context_assumptions_map in H6. }
      cbn. rewrite map2_map2_bias_left.
      { rewrite PCUICCases.ind_predicate_context_length; len. }
      rewrite map_map2 /= map2_cst.
      rewrite PCUICCases.ind_predicate_context_length; len.
      eapply (trans_ind_predicate_context Σ) in X1.
      eapply (eq_annots_ind_predicate_context ci).
      eapply All2_Forall2 => //. exact X1.
    + clear X7.
      rewrite trans_local_app in X4.
      rewrite /predctx in X4.
      rewrite trans_case_predicate_context in X4 => //.
    + clear X7. cbn [preturn trans_predicate].
      specialize (X3 X8).
      rewrite trans_local_app in X3.
      rewrite /predctx in X3.
      rewrite trans_case_predicate_context in X3 => //.
    + now rewrite global_ext_constraints_trans.
    + cbn. clear X7.
      now rewrite trans_mkApps map_app in X6.
    + red. eapply All2_Forall2.
      eapply All2_map2_right.
      eapply All2_map.
      eapply All2i_All2; tea.
      cbv beta. intros i cdecl br.
      set (brctxty := Ast.case_branch_type _ _ _ _ _ _ _).
      move=> [] [] eqann [] Hbod IHbod [] Hty IHty.
      unfold wf_branch, wf_branch_gen.
      cbn [bcontext trans_branch].
      have lenctx : #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl|.
      { eapply All2_length in eqann; now len in eqann. }
      rewrite map2_map2_bias_left; len.
      rewrite /forget_types map_map2 map2_cst; len.
      eapply eq_annots_cstr_branch_context.
      eapply All2_Forall2. eapply trans_cstr_branch_context_alpha; tea.
    + eapply All2i_map2_right. eapply All2i_map.
      eapply All2i_impl; tea.
      cbv beta. intros i cdecl br.
      set (brctxty := Ast.case_branch_type _ _ _ _ _ _ _).
      move=> [] [] eqann [] Hbod IHbod [] Hty IHty.
      have lenctx : #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl|.
      { eapply All2_length in eqann; now len in eqann. }
      split.
      { cbn [bcontext trans_branch].
        rewrite map2_map2_bias_left; len.
        eapply eq_binder_annots_eq.
        eapply trans_cstr_branch_context_alpha; tea. }
      intros brctxty'.
      destruct (trans_case_branch_type Σ ci mdecl idecl cdecl i p br X1 eqann) as [eqctx eqbty].
      rewrite [brctxty'.2]eqbty.
      rewrite [brctxty'.1]eqctx.
      clear eqctx eqbty.
      specialize (IHbod X8). specialize (IHty X8).
      rewrite trans_local_app in IHbod.
      rewrite trans_local_app in IHty => //.

  - destruct pdecl as [arity relevance ty']. simpl in *.
    assert (wfproj := TypingWf.declared_projection_wf _ _ _ _ _ isdecl).
    simpl in wfproj.
    eapply forall_decls_declared_projection in isdecl => //.
    destruct (typing_wf _ wfΣ _ _ _ X1) as [wfc wfind].
    eapply WfAst.wf_mkApps_inv in wfind; auto.
    rewrite trans_subst; auto with wf.
    simpl. rewrite map_rev trans_subst_instance.
    eapply (type_Proj _ _ _ _ _ _ _ _ (Build_projection_body arity relevance (trans Σ' ty'))). eauto.
    rewrite trans_mkApps in X2; auto. rewrite length_map.
    destruct mdecl; auto.

  - eapply refine_type.
    assert (hfixctx : fix_context (map (map_def (trans Σ') (trans Σ')) mfix) =
            trans_local Σ' (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext; intros i x.
      simpl. rewrite /vass /trans_decl /=.
      rewrite trans_lift. reflexivity. }
    cbn. econstructor; eauto.
    eapply fix_guard_trans. assumption.
    now rewrite nth_error_map H0.
    -- eapply All_map, (All_impl X1).
       intros d tu. now apply tu.
    -- have wfΣ'0 : wf Σ' by assumption.
       apply All_map. eapply (All_impl X3).
       intros d tu. specialize (tu wfΣ'0).
       unfold on_def_body, types in *; cbn in *.
       rewrite hfixctx. rewrite /trans_local !length_map map_app in tu |- *.
       rewrite <- trans_lift.
       apply tu.
    -- have wfΣ'0 : wf Σ' by assumption.
       have hwfΓ' : wf_local Σ' (trans_local Σ' Γ) by (apply X; assumption).
       have hwfd : All (WfAst.wf_decl Σ) Γ by (eapply typing_all_wf_decl; tea).
       have hcl : is_closed_context (trans_local Σ' Γ)
         by (eapply wf_local_closed_context; tea).
       have hwfm : All (fun d => (WfAst.wf Σ (dtype d) * WfAst.wf Σ (dbody d))) mfix.
       { eapply (All_impl (All_prod _ _ _ _ X0 X2)).
         intros d [(_ & s & Hs & _) (Hs' & _)]. split.
         - now eapply TypingWf.typing_wf in Hs.
         - now eapply TypingWf.typing_wf in Hs'. }
       have hopm : All (fun d => is_open_term (trans_local Σ' Γ) (trans Σ' (dtype d))) mfix.
       { eapply (All_impl X1). intros d tu. specialize (tu wfΣ'0).
         eapply isType_is_open_term; tea.
         eapply isTypeRel_isType; exact tu. }
       eapply trans_wf_fixpoint; tea.
    -- destruct decl; reflexivity.

  - eapply refine_type.
    assert (hfixctx : fix_context (map (map_def (trans Σ') (trans Σ')) mfix) =
            trans_local Σ' (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext => i x.
      rewrite /vass /trans_decl /=. simpl. rewrite trans_lift. reflexivity. }
    cbn; econstructor; eauto.
    -- now eapply cofix_guard_trans.
    -- now rewrite nth_error_map H0.
    -- eapply All_map, (All_impl X1).
       intros d tu. now apply tu.
    -- have wfΣ'0 : wf Σ' by assumption.
       apply All_map. eapply (All_impl X3).
       intros d tu. specialize (tu wfΣ'0).
       unfold on_def_body, types in *; cbn in *.
       rewrite hfixctx. rewrite /trans_local !length_map map_app in tu |- *.
       rewrite <- trans_lift.
       apply tu.
    -- have wfΣ'0 : wf Σ' by assumption.
       have hwfΓ' : wf_local Σ' (trans_local Σ' Γ) by (apply X; assumption).
       have hwfd : All (WfAst.wf_decl Σ) Γ by (eapply typing_all_wf_decl; tea).
       have hcl : is_closed_context (trans_local Σ' Γ)
         by (eapply wf_local_closed_context; tea).
       have hwfm : All (fun d => (WfAst.wf Σ (dtype d) * WfAst.wf Σ (dbody d))) mfix.
       { eapply (All_impl (All_prod _ _ _ _ X0 X2)).
         intros d [(_ & s & Hs & _) (Hs' & _)]. split.
         - now eapply TypingWf.typing_wf in Hs.
         - now eapply TypingWf.typing_wf in Hs'. }
       have hopm : All (fun d => is_open_term (trans_local Σ' Γ) (trans Σ' (dtype d))) mfix.
       { eapply (All_impl X1). intros d tu. specialize (tu wfΣ'0).
         eapply isType_is_open_term; tea.
         eapply isTypeRel_isType; exact tu. }
       eapply trans_wf_cofixpoint; tea.
    -- destruct decl; reflexivity.

  - cbn. replace (tConst prim_ty []) with (prim_type (primInt; primIntModel p) prim_ty) by now simp prim_type.
    econstructor; cbn; eauto.
    + rewrite trans_env_retroknowledge //.
    + now apply forall_decls_declared_constant.
    + move: H1; rewrite /Ast.Env.primitive_invariants /primitive_invariants.
      intros []; split => //;
      destruct cdecl as [ty [?|] ?]; cbn in *; subst; auto => //.
    + constructor.
  - cbn. replace (tConst prim_ty []) with (prim_type (primFloat; primFloatModel p) prim_ty) by now simp prim_type.
    econstructor; cbn; eauto.
    + rewrite trans_env_retroknowledge //.
    + now apply forall_decls_declared_constant.
    + move: H1; rewrite /Ast.Env.primitive_invariants /primitive_invariants.
      intros []; split => //;
      destruct cdecl as [ty [?|] ?]; cbn in *; subst; auto => //.
    + constructor.
  - cbn. replace (tConst prim_ty []) with (prim_type (primString; primStringModel p) prim_ty) by now simp prim_type.
    econstructor; cbn; eauto.
    + rewrite trans_env_retroknowledge //.
    + now apply forall_decls_declared_constant.
    + move: H1; rewrite /Ast.Env.primitive_invariants /primitive_invariants.
      intros []; split => //;
      destruct cdecl as [ty [?|] ?]; cbn in *; subst; auto => //.
    + constructor.
  - cbn. set (a := {| array_level := _ |}).
    replace (tApp (tConst prim_ty [u]) (trans (trans_global_env Σ.1) ty)) with (prim_type (primArray; primArrayModel a) prim_ty) by now simp prim_type.
    econstructor; cbn; eauto.
    + rewrite trans_env_retroknowledge //.
    + now apply forall_decls_declared_constant.
    + move: H1; rewrite /Ast.Env.primitive_invariants /primitive_invariants.
      intros []; split => //; eauto.
      * apply forall_decls_declared_constant in H0; eauto.
        rewrite /trans_constant_body in H0 |- *.
        now rewrite H1 H2 H3 /= in H0 |- *.
      * rewrite /trans_constant_body in H0 |- *.
        now rewrite H1 H2 H3 /= in H0 |- *.
    + constructor; eauto. cbn [array_level a]. eapply validity in X1; eauto.
      eapply PCUICWfUniverses.isType_wf_universes in X1. cbn [trans PCUICWfUniverses.wf_universes] in X1.
      unfold PCUICWfUniverses.wf_universes in X1. cbn [PCUICWfUniverses.on_universes Sort.on_sort s] in X1.
      move: X1. case: PCUICWfUniverses.wf_universe_reflect => //; eauto. eauto.
      cbn [a array_value]. solve_all.
  - assert (WfAst.wf Σ B).
    { now apply typing_wf in X2. }
    eapply type_Cumul; eauto.
    eapply trans_cumulSpec_typed; eauto with trans.
    clear X. apply typing_all_wf_decl in wfΓ; auto.
    eapply typing_wf in X0; eauto. destruct X0. auto.
    specialize (X1 X5).
    now eapply validity in X1.
    specialize (X3 X5). now eapply has_sort_isType.
Qed.

Lemma Alli_map {A B} (P : nat -> B -> Type) n (f : A -> B) l :
  Alli (fun n x => P n (f x)) n l ->
  Alli P n (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma trans_arities_context Σ m :
  let Σ' := trans_global_env Σ in
  trans_local Σ' (Ast.Env.arities_context (Ast.Env.ind_bodies m)) =
  arities_context (map (trans_one_ind_body Σ') (Ast.Env.ind_bodies m)).
Proof.
  rewrite /trans_local /Ast.Env.arities_context rev_map_spec map_rev map_map_compose
    /PCUICEnvironment.arities_context rev_map_spec map_map_compose /= //.
Qed.

Lemma trans_subst_telescope Σ s k Γ :
  let Σ' := trans_global_env Σ in
  map (trans_decl Σ') (Ast.Env.subst_telescope s k Γ) =
  subst_telescope (map (trans Σ') s) k (map (trans_decl Σ') Γ).
Proof.
  rewrite /subst_telescope /Ast.Env.subst_telescope.
  rewrite map_mapi mapi_map.
  apply mapi_ext => n [na [b|] ty] /=;
  rewrite /map_decl /trans_decl /=; f_equal;
  now rewrite trans_subst.
Qed.

From MetaRocq.PCUIC Require Import PCUICInstDef PCUICInstConv.
From Stdlib Require Import ssrbool.
(* Lemma closed_ctx_map2_set_binder_name (n : nat) (bctx : list aname) (ctx : list context_decl) :
  closedn_ctx n ctx -> closedn_ctx n (map2_bias_left set_binder_name dummy_decl bctx ctx).
Proof.
  induction bctx in n, ctx |- *; cbn; auto.
  destruct ctx; auto.
  intros H.
  destruct ctx. cbn.
  rewrite IHbctx //.
  rewrite !closedn_ctx_snoc IHbctx.
  rewrite closedn_ctx_snoc in H. now move/andP: H=>[].
  cbn. rewrite map2_bias_left_length.
  rewrite closedn_ctx_snoc in H. move/andP: H=>[].

  cbn.
  specialize (IHbctx _ _ H).
  cbn in IHbctx.
  move/andP => [] clc clctx.
  rewrite IHbctx // /=.
  eapply closed_decl
  rewrite closedn_ctx_ *)

Lemma closed_ind_predicate_context {cf} {Σ ind mdecl idecl} :
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (ind_predicate_context ind mdecl idecl).
Proof.
  intros wfΣ decli.
  eapply PCUICClosed.closed_ind_predicate_context; tea.
  eapply PCUICClosedTyp.declared_minductive_closed. eapply decli.
Qed.

Lemma All2_All_map2 {A B C} {P : A -> Type} (f : B -> C -> A) l l' :
  All2 (fun x y => P (f x y)) l l' ->
  All P (map2 f l l').
Proof.
  induction 1; constructor; auto.
Qed.

Lemma wf_mkApps_head {Σ t args} :
  WfAst.wf Σ (Ast.mkApps t args) -> ~~ Ast.isApp t -> WfAst.wf Σ t.
Proof. intros w h. exact (WfAst.wf_mkApps_napp _ _ _ h w).1. Qed.

Lemma forallb_trans_closed {P : Ast.term -> Prop} {Pw : Ast.term -> Type} {f : Ast.term -> term} {l k} :
  Forall P l ->
  (forall x, P x -> Pw x -> Ast.closedn k x -> closedn k (f x)) ->
  All Pw l ->
  forallb (Ast.closedn k) l -> forallb (closedn k) (map f l).
Proof.
  intros hP hf. induction hP as [|x l hx hl IH]; cbn; auto.
  intros w; inversion_clear w as [|? ? wx wl].
  move/andP => [c1 c2]. apply/andP; split; [exact (hf x hx wx c1)|exact (IH wl c2)].
Qed.

Lemma forallb_test_def_trans_closed {P : Ast.term -> Prop} {Pt Pb : Ast.term -> Type}
  {f : Ast.term -> term} {mfix k k'} :
  tFixProp P P mfix ->
  (forall x, P x -> Pt x -> Ast.closedn k x -> closedn k (f x)) ->
  (forall x, P x -> Pb x -> Ast.closedn k' x -> closedn k' (f x)) ->
  All (fun d => Pt (dtype d) × Pb (dbody d)) mfix ->
  forallb (test_def (Ast.closedn k) (Ast.closedn k')) mfix ->
  forallb (test_def (closedn k) (closedn k')) (map (map_def f f) mfix).
Proof.
  intros hP ht hb. induction hP as [|d l [hd hd'] hl IH]; cbn; auto.
  intros w; inversion_clear w as [|? ? wd wl]. destruct wd as [wt wb].
  unfold test_def; cbn.
  move/andP => [/andP [c1 c2] c3].
  apply/andP; split; [apply/andP; split|]; [exact (ht _ hd wt c1)|exact (hb _ hd' wb c2)|exact (IH wl c3)].
Qed.

(** [trans] preserves closedness of a term of which only a substitution instance,
    applied to arguments, is known to be well formed.  Substitution leaves the case
    annotations unchanged, and [trans] flattens applications as [Ast.mkApps] does. *)
Lemma trans_closedn_subst {cf} {Σ} s :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  forall t n k args,
  WfAst.wf Σ (Ast.mkApps (Ast.subst s n t) args) ->
  Ast.closedn k t ->
  closedn k (trans (trans_global_env Σ) t).
Proof.
  intros wfΣ wfΣ'.
  apply (Template.Induction.term_forall_list_ind (fun t => forall n k args,
    WfAst.wf Σ (Ast.mkApps (Ast.subst s n t) args) ->
    Ast.closedn k t -> closedn k (trans (trans_global_env Σ) t))).
  - intros i m k args wft cl. exact cl.
  - intros; reflexivity.
  - intros ev l IH m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    exact (forallb_trans_closed IH (fun x hx wx => hx m k [] wx) (All_map_inv _ _ _ w) cl).
  - intros; reflexivity.
  - intros c IHc kind t IHt m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    destruct w as [wc wt]. move/andP: cl => [c1 c2].
    rewrite (IHt m k [] wt c2) (IHc m k [] wc c1). reflexivity.
  - intros na A IHA B IHB m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    destruct w as [wA wB]. move/andP: cl => [c1 c2].
    apply/andP; split; [exact (IHA m k [] wA c1)|exact (IHB (S m) (S k) [] wB c2)].
  - intros na A IHA B IHB m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    destruct w as [wA wB]. move/andP: cl => [c1 c2].
    apply/andP; split; [exact (IHA m k [] wA c1)|exact (IHB (S m) (S k) [] wB c2)].
  - intros na b IHb t IHt b' IHb' m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    destruct w as [[wb wt] wb']. move/andP: cl => [/andP [c1 c2] c3].
    apply/andP; split; [apply/andP; split|];
      [exact (IHb m k [] wb c1)|exact (IHt m k [] wt c2)|exact (IHb' (S m) (S k) [] wb' c3)].
  - intros f IHf l IHl m k args wft cl.
    change (Ast.subst s m (Ast.tApp f l)) with
      (Ast.mkApps (Ast.subst s m f) (map (Ast.subst s m) l)) in wft.
    rewrite -AstUtils.mkApps_app in wft.
    cbn in cl |- *. move/andP: cl => [c1 c2].
    rewrite PCUICClosed.closedn_mkApps. apply/andP; split.
    + exact (IHf m k _ wft c1).
    + have w := WfAst.wf_mkApps_inv _ _ _ wft. apply All_app in w as [w _].
      exact (forallb_trans_closed IHl (fun x hx wx => hx m k [] wx) (All_map_inv _ _ _ w) c2).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros ci p IHp c IHc0 brs IHbrs m k args wft.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w.
    destruct w as [mdecl [idecl [H H0 X H1 wpars wret wc wbrs]]].
    rewrite ?length_map in H1.
    have X0 :
      (All (fun t => forall k, Ast.closedn k t -> closedn k (trans (trans_global_env Σ) t))
        (Ast.pparams p) ×
       (forall k, Ast.closedn k (Ast.preturn p) ->
          closedn k (trans (trans_global_env Σ) (Ast.preturn p))))%type.
    { destruct IHp as [IHpars IHret]. split.
      - apply All_map_inv in wpars.
        eapply All_impl; [exact (All_mix IHpars wpars)|]. cbv beta.
        intros x [hx wx] k'. exact (hx m k' [] wx).
      - intros k'. exact (IHret _ k' [] wret). }
    have IHc : forall k, Ast.closedn k c -> closedn k (trans (trans_global_env Σ) c).
    { intros k'. exact (IHc0 m k' [] wc). }
    have X1 :
      All2 (fun cdecl br =>
        (WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci.(ci_ind) mdecl cdecl) ×
         (forall k, Ast.closedn k (Ast.bbody br) ->
            closedn k (trans (trans_global_env Σ) (Ast.bbody br))))%type)
        (Ast.Env.ind_ctors idecl) brs.
    { eapply All2_impl; [exact (All2_All_mix_right IHbrs (All2_map_right_inv wbrs))|]. cbv beta.
      intros cdecl br [[hn wb] hb]. split; [exact hn|].
      intros k'. exact (hb _ k' [] wb). }
    clear IHp IHc0 IHbrs wft wpars wret wc wbrs.
    cbn.
    eapply forall_decls_declared_inductive in H; tea.
    rewrite trans_lookup_inductive.
    rewrite (declared_inductive_lookup _ H).
    destruct X0.
    cbn.
    unfold test_predicate_k. cbn.
    unfold Ast.test_predicate. cbn.
    pose proof (All2_length X) as H2. len in H2.
    intros; rtoProp. intuition auto.
    * solve_all.
    * len. rewrite map2_map2_bias_left.
      { rewrite PCUICCases.ind_predicate_context_length. cbn. len. }
      eapply PCUICInstConv.closed_ctx_args.
      { rewrite PCUICCases.ind_predicate_context_length. cbn. len. }
      rewrite H1.
      relativize (Ast.Env.context_assumptions _).
      eapply (closed_ind_predicate_context wfΣ' H).
      cbn. now rewrite context_assumptions_map.
    * rewrite map2_map2_bias_left.
      rewrite PCUICCases.ind_predicate_context_length. cbn. len.
      rewrite map2_length.
      rewrite PCUICCases.ind_predicate_context_length. cbn. len.
      solve_all.
    * solve_all.
      eapply All2_All_map2, All2_map.
      eapply All2_nth_hyp in X1.
      solve_all.
      destruct X0 as [c' [hnth [[eqb IHb] hbr]]].
      assert (hlen := All2_length eqb). len in hlen.
      unfold test_branch_k. unfold Ast.test_branch in hbr.
      unfold trans_branch. cbn -[cstr_branch_context].
      rewrite map2_map2_bias_left. len.
      apply/andP; split.
      { eapply PCUICInstConv.closed_ctx_args; len.
        rewrite H1.
        relativize (Ast.Env.context_assumptions _).
        eapply (PCUICClosedTyp.closed_cstr_branch_context (Σ := trans_global (Ast.Env.empty_ext Σ)) (i:=c')); cbn; tea.
        split; cbn; tea. now rewrite nth_error_map hnth.
        cbn. now rewrite context_assumptions_map. }
      rewrite map2_length; len. eauto.
  - intros pr c IHc m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    exact (IHc m k [] w cl).
  - intros mfix idx IH m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    apply All_map_inv in w. rewrite length_map.
    exact (forallb_test_def_trans_closed IH (fun x hx wx => hx m k [] wx)
      (fun x hx wx => hx (#|mfix| + m) (#|mfix| + k) [] wx) w cl).
  - intros mfix idx IH m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl |- *.
    apply All_map_inv in w. rewrite length_map.
    exact (forallb_test_def_trans_closed IH (fun x hx wx => hx m k [] wx)
      (fun x hx wx => hx (#|mfix| + m) (#|mfix| + k) [] wx) w cl).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros u arr def ty IHarr IHdef IHty m k args wft cl.
    have w := WfAst.wf_inv (wf_mkApps_head wft isT). cbn in w, cl.
    destruct w as [[warr wdef] wty]. move/andP: cl => [/andP [c1 c2] c3].
    have h1 := forallb_trans_closed IHarr (fun x hx wx => hx m k [] wx) (All_map_inv _ _ _ warr) c1.
    exact (introT andP (conj (introT andP (conj h1 (IHdef m k [] wdef c2))) (IHty m k [] wty c3))).
Qed.

Lemma trans_closedn {cf} {Σ k t} :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  WfAst.wf Σ t ->
  Ast.closedn k t ->
  closedn k (trans (trans_global_env Σ) t).
Proof.
  intros wfΣ wfΣ' wf.
  apply (trans_closedn_subst [] wfΣ wfΣ' t 0 k []).
  change (WfAst.wf Σ (Ast.subst [] 0 t)).
  now rewrite (MetaRocq.Template.LiftSubst.subst_empty Σ).
Qed.

Definition trans_nested_inst (Σ : global_env_map) (e : ST.nested_inst) : nested_inst :=
  {| ni_level := ST.ni_level e;
     ni_npars := ST.ni_npars e;
     ni_args := map (trans Σ) (ST.ni_args e) |}.

Lemma trans_nested_inst_ok {cf} {Σ NI Γ x l} :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  All (WfAst.wf Σ) l ->
  ST.nested_inst_ok NI Γ x l ->
  nested_inst_ok
    (map (trans_nested_inst (trans_global_env Σ)) NI)
    (trans_local (trans_global_env Σ) Γ) x
    (map (trans (trans_global_env Σ)) l).
Proof.
  intros wfΣ wfΣ' wfl [j [e [hnth lt lev args closed]]].
  exists j, (trans_nested_inst (trans_global_env Σ) e).
  split.
  - now rewrite nth_error_map hnth.
  - now rewrite trans_local_length.
  - now rewrite trans_local_length lev.
  - rewrite firstn_map args !map_map.
    apply map_ext => a.
    rewrite trans_lift. f_equal. now rewrite trans_local_length.
  - rewrite skipn_map trans_local_length forallb_map.
    apply All_forallb.
    eapply All_impl; [exact (All_mix (forallb_All _ _ closed) (All_skipn (n := ST.ni_npars e) wfl))|].
    cbv beta. intros a [cla wfa]. now eapply trans_closedn.
Qed.

Lemma trans_nested_uniform {cf} {Σ mdecl idecl k} :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  All (fun c => WfAst.wf Σ (Ast.Env.cstr_type c)) (Ast.Env.ind_ctors idecl) ->
  ST.nested_uniform mdecl idecl k ->
  nested_uniform
    (trans_minductive_body (trans_global_env Σ) mdecl)
    (trans_one_ind_body (trans_global_env Σ) idecl) k.
Proof.
  intros wfΣ wfΣ' wfctors [bodies npars ctors].
  split.
  - cbn. now rewrite bodies.
  - cbn. now rewrite context_assumptions_map.
  - eapply All_map.
    eapply All_impl; [exact (All_mix ctors wfctors)|]. cbv beta.
    intros cdecl [uni wfc].
    destruct uni as [rest [rest1 [ctype rest_eq closed]]].
    have hlen :
      #|ind_params (trans_minductive_body (trans_global_env Σ) mdecl)| =
      #|Ast.Env.ind_params mdecl| := trans_local_length _.
    have wfrest : WfAst.wf Σ rest.
    { rewrite ctype in wfc.
      now eapply wf_it_mkProd_or_LetIn in wfc as [_ wfrest]. }
    have closed_trans_rest1 :
      closedn (S #|Ast.Env.ind_params mdecl|) (trans (trans_global_env Σ) rest1).
    { rewrite rest_eq in wfrest.
      exact (trans_closedn_subst _ wfΣ wfΣ' rest1 0 _ [] wfrest closed). }
    exists (trans (trans_global_env Σ) rest), (trans (trans_global_env Σ) rest1).
    split.
    + cbn. now rewrite ctype trans_it_mkProd_or_LetIn.
    + rewrite rest_eq trans_subst hlen. cbn [map]. f_equal. f_equal.
      rewrite trans_mkApps -firstn_map. do 2 f_equal.
      exact (trans_to_extended_list Σ (Ast.Env.ind_params mdecl) 0).
    + now rewrite hlen.
Qed.

Lemma wf_ind_arities Σ mdecl :
  All (wf_inductive_body Σ) (Ast.Env.ind_bodies mdecl) ->
  All (WfAst.wf_decl Σ) (Typing.ind_arities mdecl).
Proof.
  rewrite /Typing.ind_arities.
  rewrite /Ast.Env.arities_context.
  intros.
  rewrite rev_map_spec. eapply All_rev. eapply All_map.
  induction X; constructor; auto.
  unfold WfAst.wf_decl; cbn. split => //.
  eapply p.
Qed.

(** Weak-head reduction in the context of the arities and the positivity context
    commutes with the translation. *)
Lemma trans_whd_rel_arities {cf} {Σ mdecl Γ ty h l} :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  All (wf_inductive_body Σ) (Ast.Env.ind_bodies mdecl) ->
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ ty ->
  ST.whd_rel true Σ (Ast.Env.arities_context (Ast.Env.ind_bodies mdecl) ,,, Γ) ty [] h l ->
  (WfAst.wf Σ h × All (WfAst.wf Σ) l) ×
  whd_rel true (trans_global_env Σ)
    (arities_context (ind_bodies (trans_minductive_body (trans_global_env Σ) mdecl)) ,,,
      trans_local (trans_global_env Σ) Γ)
    (trans (trans_global_env Σ) ty) [] (trans (trans_global_env Σ) h)
    (map (trans (trans_global_env Σ)) l).
Proof.
  intros wfΣ wfΣ' wfbodies wfΓ wfty w.
  have wfΓr : All (WfAst.wf_decl Σ) (Ast.Env.arities_context (Ast.Env.ind_bodies mdecl) ,,, Γ).
  { apply All_app_inv; [exact wfΓ|]. exact (wf_ind_arities Σ mdecl wfbodies). }
  split.
  - eapply whd_rel_wf; tea. constructor.
  - eapply trans_whd_rel in w; tea; [|constructor].
    move: w. rewrite trans_local_app trans_arities_context. cbn. exact id.
Qed.

Lemma trans_positive_cstr_arg {cf} {Σ mdecl NI Γ t} :
  Typing.wf Σ ->
  wf (trans_global_env Σ) ->
  All (wf_inductive_body Σ) (Ast.Env.ind_bodies mdecl) ->
  ST.positive_cstr_arg Σ mdecl NI Γ t ->
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ t ->
  positive_cstr_arg (trans_global_env Σ)
    (trans_minductive_body (trans_global_env Σ) mdecl)
    (map (trans_nested_inst (trans_global_env Σ)) NI)
    (trans_local (trans_global_env Σ) Γ)
    (trans (trans_global_env Σ) t).
Proof.
  intros wfΣ wfΣ' wfbodies p.
  revert NI Γ t p.
  apply (ST.positive_cstr_arg_mrect Σ mdecl
    (fun NI Γ t _ => All (WfAst.wf_decl Σ) Γ -> WfAst.wf Σ t ->
      positive_cstr_arg (trans_global_env Σ)
        (trans_minductive_body (trans_global_env Σ) mdecl)
        (map (trans_nested_inst (trans_global_env Σ)) NI)
        (trans_local (trans_global_env Σ) Γ)
        (trans (trans_global_env Σ) t))
    (fun NI Γ l _ => All (WfAst.wf_decl Σ) Γ -> All (WfAst.wf Σ) l ->
      positive_args (trans_global_env Σ)
        (trans_minductive_body (trans_global_env Σ) mdecl)
        (map (trans_nested_inst (trans_global_env Σ)) NI)
        (trans_local (trans_global_env Σ) Γ)
        (map (trans (trans_global_env Σ)) l))
    (fun NI Γ ps nskip cs _ =>
      All (WfAst.wf_decl Σ) Γ -> All (WfAst.wf Σ) ps -> All (WfAst.wf Σ) cs ->
      positive_nested_ctors (trans_global_env Σ)
        (trans_minductive_body (trans_global_env Σ) mdecl)
        (map (trans_nested_inst (trans_global_env Σ)) NI)
        (trans_local (trans_global_env Σ) Γ)
        (map (trans (trans_global_env Σ)) ps) nskip
        (map (trans (trans_global_env Σ)) cs))
    (fun NI Γ ps nskip c _ =>
      All (WfAst.wf_decl Σ) Γ -> All (WfAst.wf Σ) ps -> WfAst.wf Σ c ->
      positive_nested_cstr (trans_global_env Σ)
        (trans_minductive_body (trans_global_env Σ) mdecl)
        (map (trans_nested_inst (trans_global_env Σ)) NI)
        (trans_local (trans_global_env Σ) Γ)
        (map (trans (trans_global_env Σ)) ps) nskip
        (trans (trans_global_env Σ) c))).
  - intros NI0 Γ0 ty closed _ wfty.
    constructor. rewrite trans_local_length.
    now eapply trans_closedn.
  - intros NI0 Γ0 l k i real closed ati _ wfty.
    rewrite trans_mkApps.
    move/WfAst.wf_mkApps_inv: wfty => wfl.
    destruct ati as [le [lt nth]].
    eapply pos_arg_concl with (i := trans_one_ind_body (trans_global_env Σ) i).
    + rewrite length_map real /ind_realargs /ST.ind_realargs. cbn.
      try unfold app_context. try unfold trans_local.
      rewrite -map_app. symmetry. apply context_assumptions_map.
    + rewrite trans_local_length.
      eapply All_map.
      eapply All_impl; [exact (All_mix closed wfl)|].
      cbv beta. intros a [cla wfa]. now eapply trans_closedn.
    + repeat split; rewrite ?trans_local_length ?length_map //.
      rewrite -map_rev nth_error_map nth //.
  - intros NI0 Γ0 x l inst _ wfty.
    rewrite trans_mkApps.
    move/WfAst.wf_mkApps_inv: wfty => wfl.
    econstructor 3. now eapply trans_nested_inst_ok.
  - intros NI0 Γ0 ind u args mdecl' idecl' k na decl uniform variance lenargs
      closed pargs IHargs nctors IHctors wfΓ wfty.
    rewrite trans_mkApps.
    move/WfAst.wf_mkApps_inv: wfty => wfargs.
    have wfind : wf_inductive_body Σ idecl'.
    { destruct (TypingWf.declared_minductive_wf (wfΣ := wfΣ) (proj1 decl))
        as [_ wfinds].
      exact (nth_error_all (proj2 decl) wfinds). }
    econstructor 4.
    + now eapply forall_decls_declared_inductive.
    + eapply trans_nested_uniform; tea. exact (wf_ind_ctors _ _ wfind).
    + exact variance.
    + now rewrite length_map.
    + rewrite skipn_map trans_local_length.
      eapply All_map.
      eapply All_impl; [exact (All_mix closed (All_skipn (n := k) wfargs))|].
      cbv beta. intros a [cla wfa]. now eapply trans_closedn.
    + rewrite firstn_map. apply IHargs; [exact wfΓ|]. now apply All_firstn.
    + have e6 :
        mkApps (tInd ind u) (map (trans (trans_global_env Σ)) (firstn k args)) =
        trans (trans_global_env Σ) (Ast.mkApps (Ast.tInd ind u) (firstn k args)).
      { now rewrite trans_mkApps. }
      have e3 :
        map (lift0 1) (map (trans (trans_global_env Σ)) (firstn k args)) =
        map (trans (trans_global_env Σ)) (map (Ast.lift0 1) (firstn k args)).
      { rewrite !map_map. apply map_ext => a. now rewrite trans_lift. }
      have e4 :
        map (fun c => subst_instance u (cstr_type c))
          (ind_ctors (trans_one_ind_body (trans_global_env Σ) idecl')) =
        map (trans (trans_global_env Σ))
          (map (fun c => subst_instance u (Ast.Env.cstr_type c)) (Ast.Env.ind_ctors idecl')).
      { rewrite /= !map_map. apply map_ext => c. now rewrite trans_subst_instance. }
      have e5 :
        context_assumptions (ind_params (trans_minductive_body (trans_global_env Σ) mdecl')) =
        Ast.Env.context_assumptions (Ast.Env.ind_params mdecl').
      { cbn. now rewrite context_assumptions_map. }
      rewrite firstn_map trans_local_length e6 e3 e4 e5.
      apply IHctors; [constructor; [refine (tt, _); apply WfAst.wf_mkApps;
        [constructor|now apply All_firstn]|exact wfΓ]| |].
      * eapply All_map. eapply All_impl; [exact (All_firstn (n := k) wfargs)|].
        cbv beta. intros a wfa. now eapply WfAst.wf_lift.
      * eapply All_map. eapply All_impl; [exact (wf_ind_ctors _ _ wfind)|].
        cbv beta. intros c wfc. now eapply WfAst.wf_subst_instance.
  - intros NI0 Γ0 na b ty ty' pos IHpos wfΓ wfty.
    move/WfAst.wf_inv: wfty => /= [[wfb wfty] wft].
    constructor 5. rewrite trans_subst in IHpos.
    apply IHpos; [exact wfΓ|]. eapply WfAst.wf_subst; auto.
  - intros NI0 Γ0 na ty ty' closed pos IHpos wfΓ wfty.
    move/WfAst.wf_inv: wfty => /= [wfty wft].
    constructor 6.
    + rewrite trans_local_length. now eapply trans_closedn.
    + cbn. apply IHpos; [constructor; [exact (tt, wfty)|exact wfΓ]|exact wft].
  - intros NI0 Γ0 ty h l w pos IHpos wfΓ wfty.
    destruct (trans_whd_rel_arities wfΣ wfΣ' wfbodies wfΓ wfty w) as [[wfh wfl] tw].
    econstructor 7; [exact tw|].
    rewrite -trans_mkApps. apply IHpos; [exact wfΓ|].
    apply WfAst.wf_mkApps; [exact wfh|exact wfl].
  - intros NI0 Γ0 na ty ty' h l w closed pos IHpos wfΓ wfprod.
    move/WfAst.wf_inv: wfprod => /= [wfty wft].
    destruct (trans_whd_rel_arities wfΣ wfΣ' wfbodies wfΓ wfty w) as [[wfh wfl] tw].
    econstructor 8; [exact tw| |].
    + rewrite trans_local_length -trans_mkApps. eapply trans_closedn; tea.
      apply WfAst.wf_mkApps; [exact wfh|exact wfl].
    + cbn. apply IHpos; [constructor; [exact (tt, wfty)|exact wfΓ]|exact wft].
  - intros NI0 Γ0 k l l' a pos IHpos wfΓ wfty.
    rewrite trans_mkApps.
    move/WfAst.wf_mkApps_inv: wfty => wfl.
    have hl' : All (WfAst.wf Σ) l' ×
      All2 (arg_whd (trans_global_env Σ)
        (arities_context (ind_bodies (trans_minductive_body (trans_global_env Σ) mdecl)) ,,,
          trans_local (trans_global_env Σ) Γ0))
        (map (trans (trans_global_env Σ)) l) (map (trans (trans_global_env Σ)) l').
    { clear pos IHpos.
      induction a as [|x y xs ys r a IHa]; [split; constructor|].
      inversion wfl as [|? ? wx wxs]; subst.
      destruct (IHa wxs) as [w1 w2]. cbn [map].
      destruct r as [->|[h0 [l0 [w e]]]].
      - split; constructor; auto. left; reflexivity.
      - subst y.
        destruct (trans_whd_rel_arities wfΣ wfΣ' wfbodies wfΓ wx w) as [[wfh wfl0] tw].
        split; constructor; auto.
        + apply WfAst.wf_mkApps; [exact wfh|exact wfl0].
        + right. exists (trans (trans_global_env Σ) h0), (map (trans (trans_global_env Σ)) l0).
          split; [exact tw|]. now rewrite trans_mkApps. }
    destruct hl' as [wfl' a'].
    econstructor 9; [exact a'|].
    have e : mkApps (tRel k) (map (trans (trans_global_env Σ)) l') =
      trans (trans_global_env Σ) (Ast.mkApps (Ast.tRel k) l') by now rewrite trans_mkApps.
    rewrite e. apply IHpos; [exact wfΓ|].
    apply WfAst.wf_mkApps; [constructor|exact wfl'].
  - intros NI0 Γ0 _ _. constructor.
  - intros NI0 Γ0 t0 l pos IHpos poss IHposs wfΓ wfl.
    depelim wfl. constructor; auto.
  - intros NI0 Γ0 ps nskip _ _ _. constructor.
  - intros NI0 Γ0 ps nskip t0 l pos IHpos poss IHposs wfΓ wfps wfcs.
    depelim wfcs. constructor; eauto.
  - intros NI0 Γ0 p0 ps nskip na ty t0 pos IHpos wfΓ wfps wfty.
    move/WfAst.wf_inv: wfty => /= [wfty wft].
    depelim wfps. constructor 1. rewrite trans_subst in IHpos.
    apply IHpos; auto. eapply WfAst.wf_subst; auto.
  - intros NI0 Γ0 ps nskip na b ty t0 pos IHpos wfΓ wfps wfty.
    move/WfAst.wf_inv: wfty => /= [[wfb wfty] wft].
    constructor 2. rewrite trans_subst in IHpos.
    apply IHpos; auto. eapply WfAst.wf_subst; auto.
  - intros NI0 Γ0 nskip na ty t0 pos IHpos wfΓ _ wfty.
    move/WfAst.wf_inv: wfty => /= [wfty wft].
    constructor 3. apply IHpos; [constructor; [exact (tt, wfty)|exact wfΓ]|constructor|exact wft].
  - intros NI0 Γ0 na ty t0 pos IHarg ncstr IHcstr wfΓ _ wfty.
    move/WfAst.wf_inv: wfty => /= [wfty wft].
    constructor 4.
    + now apply IHarg.
    + apply IHcstr; [constructor; [exact (tt, wfty)|exact wfΓ]|constructor|exact wft].
  - intros NI0 Γ0 x l inst _ _ wfty.
    rewrite trans_mkApps.
    move/WfAst.wf_mkApps_inv: wfty => wfl.
    constructor 5. now eapply trans_nested_inst_ok.
Qed.

From MetaRocq.PCUIC Require Import PCUICOnFreeVars.

Lemma trans_cumul_ctx_rel {cf} {Σ : Ast.Env.global_env_ext} Γ Δ Δ' :
  let Σ' := trans_global Σ in
  Typing.wf Σ -> wf Σ' ->
  ST.TemplateConversion.cumul_ctx_rel Typing.cumul_gen Σ Γ Δ Δ' ->
  closed_ctx (trans_local Σ' (Γ ,,, Δ)) ->
  closed_ctx (trans_local Σ' (Γ ,,, Δ')) ->
  All (WfAst.wf_decl Σ) (Γ ,,, Δ) ->
  All (WfAst.wf_decl Σ) (Γ ,,, Δ') ->
  cumul_ctx_rel cumulSpec0 Σ' (trans_local Σ' Γ) (trans_local Σ' Δ) (trans_local Σ' Δ').
Proof.
  intros Σ' wfΣ wfΣ'.
  induction 1; cbn; constructor; auto.
  inv_on_free_vars.
  apply IHX => //. now depelim X0. now depelim X1.
  rewrite - !trans_local_app.
  move/andP: H => [] cl0 cl1.
  move/andP: H0 => [] cl0' cl1'. len in cl1. len in cl1'.
  destruct p; constructor; cbn; auto; depelim X0; depelim X1; destruct w as []; destruct w0 as [].

  eapply trans_cumul_gen in eqt; tea.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (pb:=Cumul)).
  eapply PCUICWellScopedCumulativity.into_ws_cumul_pb => //.
  now eapply closed_ctx_on_free_vars in cl0.
  1-2:cbn in cl1, cl1'.
  1-2:rewrite closedn_on_free_vars //; len.
  now rewrite (All2_fold_length X).

  eapply trans_cumul_gen in eqb; tea.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (pb:=Conv)).
  eapply PCUICWellScopedCumulativity.into_ws_cumul_pb => //.
  now eapply closed_ctx_on_free_vars in cl0.
  1-2:move/andP: cl1 => [] /= clb cbt.
  1-2:move/andP: cl1' => [] /= clb' cbt'.
  1-2:rewrite closedn_on_free_vars //; len.
  now rewrite (All2_fold_length X).

  eapply trans_cumul_gen in eqt; tea.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (pb:=Cumul)).
  eapply PCUICWellScopedCumulativity.into_ws_cumul_pb => //.
  now eapply closed_ctx_on_free_vars in cl0.
  1-2:move/andP: cl1 => [] /= clb cbt.
  1-2:move/andP: cl1' => [] /= clb' cbt'.
  1-2:rewrite closedn_on_free_vars //; len.
  now rewrite (All2_fold_length X).
Qed.

Lemma wf_expand_lets Σ Γ t :
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ t ->
  WfAst.wf Σ (Ast.Env.expand_lets Γ t).
Proof.
  intros.
  rewrite /Ast.Env.expand_lets /Ast.Env.expand_lets_k.
  eapply WfAst.wf_subst, WfAst.wf_lift => //.
  now eapply wf_extended_subst.
Qed.

Lemma wf_expand_lets_ctx Σ Γ Δ :
  All (WfAst.wf_decl Σ) Γ ->
  All (WfAst.wf_decl Σ) Δ ->
  All (WfAst.wf_decl Σ) (Ast.Env.expand_lets_ctx Γ Δ).
Proof.
  intros.
  rewrite /Ast.Env.expand_lets_ctx /Ast.Env.expand_lets_k_ctx.
  eapply wf_subst_context => //.
  eapply wf_lift_context => //.
  eapply wf_extended_subst => //.
Qed.

Lemma All2_refl_inv {A} {P : A -> A -> Type} l :
  All2 P l l -> All (fun x => P x x) l.
Proof.
  intros H; depind H; constructor; auto.
Qed.

Lemma All_All2_refl {A} {P : A -> A -> Type} l :
  All (fun x => P x x) l -> All2 P l l.
Proof.
  intros H; depind H; constructor; auto.
Qed.

Lemma trans_ind_arities {cf} Σ mdecl :
  let Σ' := trans_global_env Σ in
  let mdecl' := trans_minductive_body Σ' mdecl in
  ind_arities mdecl' = trans_local Σ' (ST.ind_arities mdecl).
Proof.
  intros. rewrite /ind_arities.
  rewrite trans_arities_context //.
Qed.

Lemma trans_cstr_respects_variance {cf} Σ mdecl v cdecl :
  let Σ' := trans_global_env Σ in
  let mdecl' := trans_minductive_body Σ' mdecl in
  let cdecl' := trans_constructor_body Σ' cdecl in
  Typing.wf Σ ->
  wf Σ' ->
  All (wf_inductive_body Σ) (Ast.Env.ind_bodies mdecl) ->
  All (WfAst.wf_decl Σ) (Ast.Env.ind_params mdecl) ->
  All (WfAst.wf_decl Σ) (Ast.Env.cstr_args cdecl) ->
  All (WfAst.wf Σ) (Ast.Env.cstr_indices cdecl) ->
  (closed_ctx
    (trans_local (trans_global_env Σ)
     (ST.ind_arities mdecl ,,, Ast.Env.smash_context [] (Ast.Env.ind_params mdecl) ,,,
        (Ast.Env.expand_lets_ctx (Ast.Env.ind_params mdecl)
           (Ast.Env.smash_context [] (Ast.Env.cstr_args cdecl)))))) ->
  All (fun x : Ast.term =>
    closedn (Ast.Env.context_assumptions (Ast.Env.cstr_args cdecl) +
      Ast.Env.context_assumptions (Ast.Env.ind_params mdecl) + #|ST.ind_arities mdecl|)
    (trans Σ' (Ast.Env.expand_lets
      (Ast.Env.ind_params mdecl ,,, Ast.Env.cstr_args cdecl) x)))
      (Ast.Env.cstr_indices cdecl) ->
  ST.cstr_respects_variance Typing.cumul_gen Σ mdecl v cdecl ->
  cstr_respects_variance cumulSpec0 Σ' mdecl' v cdecl'.
Proof.
  intros Σ' mdecl' cdecl' wfΣ wfΣ' wfb wfp wfa wfi clctx clidx.
  unfold ST.cstr_respects_variance, cstr_respects_variance.
  change (variance_universes (ind_universes mdecl') v) with
    (ST.variance_universes (Ast.Env.ind_universes mdecl) v).
  destruct variance_universes as [[[udecl inst] inst']|] => //.
  intros []. split.
  * apply (trans_cumul_ctx_rel (Σ := (Σ, udecl))) in c; tea.
    rewrite !trans_local_subst_instance trans_expand_lets_ctx in c.
    rewrite !trans_smash_context in c.
    rewrite trans_local_app trans_smash_context in c.
    change (trans_global_env (Σ, udecl).1) with Σ' in c.
    now rewrite trans_arities_context in c.
    { rewrite !trans_local_app /= !trans_local_subst_instance.
      rewrite -PCUICUnivSubstitutionConv.subst_instance_app_ctx.
      rewrite PCUICClosed.closedn_subst_instance_context -trans_local_app //. }
    { rewrite !trans_local_app /= !trans_local_subst_instance.
      rewrite PCUICClosed.closedn_ctx_app /=.
      rewrite !PCUICClosed.closedn_subst_instance_context.
      rewrite subst_instance_length.
      rewrite -PCUICClosed.closedn_ctx_app -trans_local_app //. }
    { eapply All_app_inv.
      eapply wf_subst_instance_context.
      eapply wf_expand_lets_ctx => //.
      eapply wf_smash_context => //.
      eapply wf_subst_instance_context.
      eapply All_app_inv. eapply wf_smash_context => //.
      now eapply wf_ind_arities. }
    { eapply All_app_inv.
      eapply wf_subst_instance_context.
      eapply wf_expand_lets_ctx => //.
      eapply wf_smash_context => //.
      eapply wf_subst_instance_context.
      eapply All_app_inv. eapply wf_smash_context => //.
      now eapply wf_ind_arities. }
  * clear c.
    eapply All2_map. eapply All2_map_inv in a.
    eapply All2_refl_inv in a. eapply All_All2_refl.
    eapply All_map. solve_all.
    eapply trans_cumul_gen in b0; tea.
    { move:b0; rewrite !trans_local_subst_instance !trans_local_app trans_arities_context.
      rewrite !trans_smash_context !trans_subst_instance !trans_expand_lets !trans_local_app //.
      intros h. simpl in h.
      eapply (PCUICConversion.cumulAlgo_cumulSpec _ (pb:=Conv)).
      eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; tea.
      { move: clctx.
        rewrite smash_context_app_expand.
        rewrite -!(trans_smash_context _ []).
        rewrite -trans_expand_lets_ctx trans_ind_arities.
        rewrite -!trans_local_app.
        move/(closed_ctx_on_free_vars xpred0).
        rewrite !app_context_assoc.
        now rewrite on_free_vars_ctx_subst_instance. }
      { eapply closedn_on_free_vars. len. move: a0.
        rewrite /ST.ind_arities; len.
        rewrite !context_assumptions_map.
        rewrite trans_expand_lets trans_local_app.
        rewrite PCUICClosed.closedn_subst_instance //. }
      { eapply closedn_on_free_vars. len. move: a0.
        rewrite /ST.ind_arities; len.
        rewrite !context_assumptions_map.
        rewrite trans_expand_lets trans_local_app.
        rewrite PCUICClosed.closedn_subst_instance //. } }
    { eapply wf_subst_instance_context.
      eapply All_app_inv => //; [|now eapply wf_ind_arities].
      eapply wf_smash_context => //.
      eapply All_app_inv => //. }
    { eapply WfAst.wf_subst_instance.
      eapply wf_expand_lets => //.
      eapply All_app_inv => //. }
    { eapply WfAst.wf_subst_instance.
      eapply wf_expand_lets => //.
      eapply All_app_inv => //. }
Qed.

Lemma trans_ind_respects_variance {cf} Σ mdecl v idecl :
  let Σ' := trans_global_env Σ in
  let mdecl' := trans_minductive_body Σ' mdecl in
  let idecl' := trans_one_ind_body Σ' idecl in
  Typing.wf Σ ->
  wf Σ' ->
  wf_inductive_body Σ idecl ->
  All (WfAst.wf_decl Σ) (Ast.Env.ind_params mdecl) ->
  closed_ctx (trans_local (trans_global_env Σ)
    (Ast.Env.ind_params mdecl ,,, Ast.Env.ind_indices idecl)) ->
  ST.ind_respects_variance Typing.cumul_gen Σ mdecl v (Ast.Env.ind_indices idecl) ->
  ind_respects_variance cumulSpec0 Σ' mdecl' v (ind_indices idecl').
Proof.
  intros Σ' mdecl' idecl' wfΣ wfΣ' wfb wfp clctx.
  unfold ST.ind_respects_variance, ind_respects_variance.
  change (variance_universes (ind_universes mdecl') v) with
    (ST.variance_universes (Ast.Env.ind_universes mdecl) v).
  destruct variance_universes as [[[udecl inst] inst']|] => //.
  intros c. apply (trans_cumul_ctx_rel (Σ := (Σ, udecl))) in c; tea.
  { rewrite !trans_local_subst_instance trans_expand_lets_ctx in c.
    rewrite !trans_smash_context in c => //. }
  { rewrite !trans_local_app !trans_local_subst_instance.
    rewrite -PCUICUnivSubstitutionConv.subst_instance_app_ctx.
    rewrite closedn_subst_instance_context.
    rewrite trans_expand_lets_ctx !trans_smash_context -smash_context_app_expand.
    apply closedn_smash_context. rewrite -trans_local_app //. }
  { rewrite !trans_local_app !trans_local_subst_instance.
    rewrite closedn_ctx_app subst_instance_length.
    rewrite !PCUICClosed.closedn_subst_instance_context -closedn_ctx_app.
    rewrite trans_expand_lets_ctx !trans_smash_context -smash_context_app_expand.
    apply PCUICClosed.closedn_smash_context. rewrite -trans_local_app //. }
  { eapply All_app_inv.
    eapply wf_subst_instance_context.
    eapply wf_expand_lets_ctx => //.
    eapply wf_smash_context => //. apply wfb.
    eapply wf_subst_instance_context.
    eapply wf_smash_context => //. }
  { eapply All_app_inv.
    eapply wf_subst_instance_context.
    eapply wf_expand_lets_ctx => //.
    eapply wf_smash_context => //. apply wfb.
    eapply wf_subst_instance_context.
    eapply wf_smash_context => //. }
Qed.

Lemma trans_type_local_ctx {cf} {Σ : Ast.Env.global_env_ext} Γ cs s (Σ' := trans_global Σ) :
  (forall (Σ : Ast.Env.global_env_ext) (Γ : Ast.Env.context) j,
  Typing.wf Σ ->
  Typing.lift_typing Typing.typing Σ Γ j ->
  wf (trans_global_env Σ) ->
  lift_typing typing (trans_global Σ)
  (trans_local (trans_global_env Σ) Γ)
  (judgment_map (trans (trans_global_env Σ)) j)) ->
  Typing.wf Σ ->
  wf Σ' ->
  ST.type_local_ctx (Typing.TemplateEnvTyping.lift_typing Typing.typing) Σ Γ cs s ->
  type_local_ctx (PCUICEnvTyping.lift_typing typing)
    (trans_global Σ)
  (trans_local Σ' Γ)
  (trans_local Σ' cs) s.
Proof.
  intros IH wfΣ wfΣ'. induction cs; simpl; auto.
  { now intros; eapply trans_wf_sort. }
  destruct a as [na [b|] ty] => //;
  intros [? ?]; cbn.
  all: split; auto.
  - eapply (IH _ _ (TermTypRel _ _ _)) in l; auto.
    rewrite -trans_local_app //.
  - eapply (IH _ _ (TypUnivRel _ _ _)) in l => //.
    rewrite -trans_local_app //.
Qed.

Lemma trans_check_ind_sorts {cf} Σ udecl kn mdecl n idecl
  (Σ' := trans_global_env Σ)
  (mdecl' := trans_minductive_body Σ' mdecl)
  (idecl' := trans_one_ind_body Σ' idecl) :
  Typing.wf Σ ->
  wf Σ' ->
  (forall (Σ : Ast.Env.global_env_ext)
    (Γ : Ast.Env.context) j,
  Typing.wf Σ ->
  Typing.lift_typing Typing.typing Σ Γ j ->
  wf (trans_global_env Σ) ->
  lift_typing typing (trans_global Σ)
    (trans_local (trans_global_env Σ) Γ)
    (judgment_map (trans (trans_global_env Σ)) j)) ->
  forall (oni: Typing.on_ind_body Typing.cumul_gen (Typing.TemplateEnvTyping.lift_typing Typing.typing)
        (Σ, udecl) kn mdecl n idecl),
  ST.check_ind_sorts
  (Typing.TemplateEnvTyping.lift_typing Typing.typing)
  (Σ, Ast.Env.ind_universes mdecl) (Ast.Env.ind_params mdecl) (Ast.Env.ind_kelim idecl)
  (Ast.Env.ind_indices idecl) (ST.ind_cunivs oni)
  (Ast.Env.ind_sort idecl) ->
  check_ind_sorts (PCUICEnvTyping.lift_typing typing)
  ((trans_global_env Σ, Ast.Env.ind_universes mdecl) : global_env_ext_map)
  (ind_params mdecl')
  (ind_kelim idecl')
  (ind_indices idecl')
  (ST.ind_cunivs oni)
  (ind_sort idecl').
Proof.
  intros wfΣ wfΣ' IH oni.
  unfold ST.check_ind_sorts, check_ind_sorts. cbn.
  destruct Sort.to_family => //.
  intros []. split => //.
  now rewrite -global_ext_constraints_trans in c.
  destruct indices_matter => //.
  now eapply trans_type_local_ctx in y.
Qed.

Lemma on_global_decl_wf {cf} {Σ : Ast.Env.global_env_ext} {kn d} :
  Typing.wf Σ ->
  Typing.on_global_decl Typing.cumul_gen (Typing.TemplateEnvTyping.lift_typing Typing.typing) Σ kn d ->
  Typing.on_global_decl Typing.cumul_gen (fun Σ => WfAst.wf_decl_pred Σ) Σ kn d.
Proof.
  intros. eapply TypingWf.on_global_decl_impl; tea.
  intros.
  apply lift_typing_wf_pred. cbn in X2.
  eapply Typing.lift_typing_impl with (1 := X2).
  now eapply typing_wf.
Qed.

Lemma Alli_All_mix {A} {P : nat -> A -> Type} {Q} {n l} :
  Alli P n l -> All Q l -> Alli (fun n x => P n x × Q x) n l.
Proof.
  induction 1; intros H; depelim H; constructor; intuition auto.
Qed.

Lemma trans_projs Σ kn n i mdecl  :
  map (trans (trans_global_env Σ))
    (Ast.Env.projs {| inductive_mind := kn; inductive_ind := n |} (Ast.Env.ind_npars mdecl) i) =
  projs {| inductive_mind := kn; inductive_ind := n |} (Ast.Env.ind_npars mdecl) i.
Proof.
  induction i; cbn; auto. f_equal; auto.
Qed.

Lemma closed_arities_context {cf} Σ m :
  wf (trans_global_env Σ) ->
  All (fun idecl => on_type (PCUICEnvTyping.lift_typing typing)
  ((trans_global_env Σ, Ast.Env.ind_universes m) : global_env_ext_map) []
  (ind_type (trans_one_ind_body (trans_global_env Σ) idecl))) (Ast.Env.ind_bodies m) ->
  closed_ctx (trans_local (trans_global_env Σ) (ST.ind_arities m)).
Proof.
  intros wfΣ.
  rewrite /ST.ind_arities /Ast.Env.arities_context rev_map_spec.
  induction 1. cbn. auto.
  cbn. rewrite map_app closedn_ctx_app /=. len.
  apply/andP; split.
  rewrite /test_decl /trans_decl /=.
  destruct p as (_ & s & hs & _). now eapply subject_closed in hs.
  eapply closedn_ctx_upwards; tea. lia.
Qed.

Lemma trans_env_env_universes {Σ : Ast.Env.global_env} : universes (trans_env_env (trans_global_env Σ)) = Ast.Env.universes Σ.
Proof.
  destruct Σ as [univs Σ] .
  unfold trans_global_env; cbn -[trans_global_decls].
  induction Σ => /= //.
Qed.

Lemma trans_env_env_retroknowledge {Σ : Ast.Env.global_env} :
  retroknowledge (trans_env_env (trans_global_env Σ)) = Ast.Env.retroknowledge Σ.
Proof.
  destruct Σ as [univs Σ] .
  unfold trans_global_env; cbn -[trans_global_decls].
  induction Σ => /= //.
Qed.

Lemma env_eq (g g' : global_env) :
  g.(universes) = g'.(universes) ->
  g.(declarations) = g'.(declarations) ->
  g.(retroknowledge) = g'.(retroknowledge) ->
  g = g'.
Proof.
  destruct g, g'; cbn. congruence.
Qed.

Lemma trans_consistent_instance_ext_gen {cf:checker_flags} Σ udecl u :
  let Σ' := trans_global Σ in
  Ast.consistent_instance_ext Σ udecl u ->
  consistent_instance_ext Σ' udecl u.
Proof.
  intros Σ'.
  unfold Ast.consistent_instance_ext, consistent_instance_ext.
  rewrite global_ext_levels_trans global_ext_constraints_trans.
  trivial.
Qed.

Lemma trans_on_global_env `{checker_flags} Σ :
  (forall (Σ : Ast.Env.global_env_ext) Γ j, Typing.wf Σ ->
    Typing.lift_typing Typing.typing Σ Γ j ->
    let Σ' := trans_global_env Σ in
    wf Σ' ->
    lift_typing typing (trans_global Σ) (trans_local Σ' Γ) (judgment_map (trans Σ') j)) ->
  Typing.wf Σ -> wf (trans_global_env Σ).
Proof.
  intros X X0.
  simpl in *.
  destruct Σ as [univs Σ retro].
  destruct X0 as [onu ond]. split => //.
  { now rewrite trans_env_env_universes. }
  cbn -[trans_global_env] in *.
  rewrite trans_env_env_universes /= /trans_global_env /=.
  induction ond; simpl; constructor; auto. destruct o. constructor; auto.
  - red in kn_fresh |- *. clear -kn_fresh.
    induction kn_fresh; cbn; constructor; auto.
  - simpl. subst udecl.
    clear -on_udecl_udecl.
    now erewrite trans_global_decl_universes in on_udecl_udecl.
  - simpl.
    set (Σg := {| Ast.Env.universes := univs; Ast.Env.declarations := Σ; Ast.Env.retroknowledge := retro |}).
    set (X0 := (onu, ond) : Typing.wf Σg).
    assert (trans_env_env (trans_global_env Σg) =
       {| universes := univs;
          declarations := declarations (trans_global_decls (empty_trans_env univs retro) Σ) |}) as <-.
    { apply env_eq.
      now rewrite trans_env_env_universes. reflexivity.
      now rewrite trans_env_env_retroknowledge. }
    assert (wfΣg : PCUICTyping.wf (trans_global_env Σg)).
    { split; rewrite trans_env_env_universes //. }
    have wfdecl := on_global_decl_wf (Σ := (Σg, udecl)) X0 on_global_decl_d.
    destruct d eqn:eqd.
    * eapply (X (Σg, _) [] (TermoptTypRel _ _ _)); auto.
    * destruct on_global_decl_d as [onI onP onNP].
      simpl.
      change (trans_env_env (trans_global_env Σg), Ast.Env.ind_universes m) with (global_env_ext_map_global_env_ext (trans_global (Σg, Ast.Env.ind_universes m))) in *.
      change (trans_global_decls (empty_trans_env univs retro) Σ) with (global_env_ext_map_global_env_map (trans_global (Σg, Ast.Env.ind_universes m))).
      constructor; auto.
      -- have wfpars := on_global_inductive_wf_params wfdecl.
        eapply on_global_inductive_wf_bodies in wfdecl.
        have clars: closed_ctx (trans_local (trans_global_env Σg) (ST.ind_arities m)).
        { eapply closed_arities_context => //. clear -onu wfΣg X0 IHond X onI.
          eapply Alli_All; tea; cbv beta.
          move=> n x /Typing.onArity => o.
          eapply isTypeRel_isType.
          apply (X (Σg, Ast.Env.ind_universes m) [] _ X0 o) => //. }
        eapply Alli_All_mix in onI; tea.
        eapply Alli_map. eapply Alli_impl. exact onI. eauto. intros n idecl [oni wf].
        have onarity : on_type_rel (PCUICEnvTyping.lift_typing typing)
          (trans_global (Σg, Ast.Env.ind_universes m)) []
          (ind_type (trans_one_ind_body (trans_global_env Σg) idecl)) rel_of_Type.
        { apply ST.onArity in oni. unfold on_type_rel in *; simpl in *.
          now apply (X (Σg, Ast.Env.ind_universes m) [] (TypRel (Ast.Env.ind_type idecl) _)). }
        have onarityred : on_type_rel (PCUICEnvTyping.lift_typing typing)
          (trans_global (Σg, Ast.Env.ind_universes m)) []
          (it_mkProd_or_LetIn (ind_params (trans_minductive_body (trans_global_env Σg) m))
            (it_mkProd_or_LetIn (ind_indices (trans_one_ind_body (trans_global_env Σg) idecl))
              (tSort (ind_sort (trans_one_ind_body (trans_global_env Σg) idecl))))) rel_of_Type.
        { apply ST.onArityRed in oni. unfold on_type_rel in *; simpl in *.
          change (tSort (Ast.Env.ind_sort idecl)) with
            (trans (trans_global_env Σg) (Ast.tSort (Ast.Env.ind_sort idecl))).
          rewrite -!trans_it_mkProd_or_LetIn.
          now apply (X (Σg, Ast.Env.ind_universes m) [] (TypRel _ rel_of_Type)). }
        unshelve refine {| ind_cunivs := oni.(ST.ind_cunivs) |}; tea.
        --- cbn -[trans_global_env].
            destruct oni.(ST.ind_arity_red) as [U [eqU arU]].
            exists (trans (trans_global_env Σg) U). split.
            { rewrite eqU. now rewrite trans_it_mkProd_or_LetIn. }
            have wfU : WfAst.wf Σg U.
            { have h := wf_ind_type _ _ wf. rewrite eqU in h.
              exact (TypingWf.wf_it_mkProd_or_LetIn _ _ _ h).2. }
            exact (trans_arity_red Σg X0 wfΣg wfpars wfU arU).
        --- pose proof oni.(ST.onConstructors) as X11. red in X11.
            red. eapply All2_map_left.
            destruct wf. solve_all.
            simpl.
            rename b into onc. rename y into cs.
            rename a0 into wfctype. rename a into wfcargs. rename b1 into wfcindices.
            destruct onc.
            have onty : on_type_rel (PCUICEnvTyping.lift_typing typing)
              (trans_global (Σg, Ast.Env.ind_universes m))
              (arities_context
              (ind_bodies (trans_minductive_body (trans_global_env Σg) m)))
              (cstr_type (trans_constructor_body (trans_global_env Σg) x)) (Ast.Env.ind_relevance idecl).
            { unfold cstr_type, Ast.Env.cstr_type in on_ctype |- *; simpl in *. red.
              move: (X (Σg, Ast.Env.ind_universes m) (Ast.Env.arities_context (Ast.Env.ind_bodies m))
                (TypRel (Ast.Env.cstr_type x) (Ast.Env.ind_relevance idecl))).
              rewrite trans_arities_context.
              intros H'. apply H' => //. }
            have ceq : cstr_type (trans_constructor_body (trans_global_env Σg) x) =
            it_mkProd_or_LetIn
              (ind_params (trans_minductive_body (trans_global_env Σg) m))
              (it_mkProd_or_LetIn
                 (cstr_args (trans_constructor_body (trans_global_env Σg) x))
                 (cstr_concl (trans_minductive_body (trans_global_env Σg) m) n
                    (trans_constructor_body (trans_global_env Σg) x))).
            { simpl; unfold cstr_type, Ast.Env.cstr_type in cstr_eq |- *; simpl in *.
              rewrite cstr_eq. rewrite !trans_it_mkProd_or_LetIn.
              autorewrite with len. f_equal. f_equal.
              rewrite !trans_mkApps /cstr_concl /cstr_concl_head /= //.
              f_equal; auto. simpl.
              now rewrite /trans_local !length_map.
              rewrite map_app /=. f_equal.
              rewrite /trans_local !length_map.
              unfold to_extended_list_k.
              now rewrite trans_reln. }
            unshelve econstructor; eauto.
            + simpl. unfold trans_local. rewrite context_assumptions_map.
              now rewrite cstr_args_length.
            + clear -X0 wfΣg onu IHond X on_cargs. revert on_cargs. simpl.
              have foo := (X (Σg, udecl) _ _ X0).
              rewrite -trans_arities_context.
              clear X.
              induction (Ast.Env.cstr_args x) in cs |- *; destruct cs; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
              split; intuition eauto;
              specialize (foo
                (Ast.Env.arities_context (Ast.Env.ind_bodies m) ,,, Ast.Env.ind_params m ,,, c));
              rewrite /trans_local !map_app in foo.
              now apply (foo (TermTypRel b ty _)).
              now apply (foo (TermTypRel b ty _)).
              now apply (foo (TypUnivRel ty _ _)).
            + clear -X0 onu wfΣg IHond X on_cindices.
              revert on_cindices.
              rewrite -trans_lift_context /trans_local -map_rev.
              simpl. rewrite {2}/trans_local length_map.
              generalize (List.rev (Ast.Env.lift_context #|Ast.Env.cstr_args x| 0 (Ast.Env.ind_indices idecl))).
              rewrite -trans_arities_context.
              induction 1; simpl; constructor; auto;
              have foo := (X (Σg, Ast.Env.ind_universes m) _ _ X0);
              specialize (foo
                (Ast.Env.arities_context (Ast.Env.ind_bodies m) ,,, Ast.Env.ind_params m ,,, Ast.Env.cstr_args x));
              rewrite /trans_local !map_app in foo.
              now apply (foo (TermTyp i t)).
              now rewrite (trans_subst_telescope _ [i] 0) in IHon_cindices.
              now rewrite (trans_subst_telescope _ [b] 0) in IHon_cindices.
            + cbn -[trans_global_env] in *.
              clear -onI wfΣg wfctype X0 onu IHond on_ctype_positive.
              set (Σ' := trans_global_env Σg) in *.
              change [] with (map (trans_decl Σ') []).
              have wfnil : All (WfAst.wf_decl Σg) (@nil Ast.Env.context_decl) := All_nil.
              revert on_ctype_positive wfctype wfnil.
              generalize (@nil Ast.Env.context_decl). induction 1; simpl.
              rewrite trans_mkApps. simpl.
              subst headrel.
              assert (#|PCUICEnvironment.ind_bodies (trans_minductive_body Σ' m)| = #|Ast.Env.ind_bodies m|) as <-.
              now rewrite /trans_minductive_body /= length_map.
              assert (#|Γ| = #|map (trans_decl Σ') Γ|) as ->. now rewrite length_map.
              move/WfAst.wf_mkApps_inv => wfindices _.
              eapply pos_concl.
              rewrite length_map.
              eapply All_map. solve_all. now eapply trans_closedn.
              move/WfAst.wf_inv => /= [[wfb wfty] wft] wfΓ.
              constructor. rewrite -(trans_subst _ [b]).
              apply IHon_ctype_positive; [eapply WfAst.wf_subst; auto|exact wfΓ].
              move/WfAst.wf_inv => /= [wfty wft] wfΓ.
              constructor.
              have wfbodies : All (wf_inductive_body Σg) (Ast.Env.ind_bodies m).
              { eapply Alli_All; [exact onI|]. intros n0 idecl0 [_ w]. exact w. }
              exact (trans_positive_cstr_arg X0 wfΣg wfbodies p wfΓ wfty).
              cbn. apply IHon_ctype_positive; [exact wft|constructor; [exact (tt, wfty)|exact wfΓ]].
            + intros v indv.
              specialize (on_ctype_variance _ indv).
              cbn -[Σg].
              eapply trans_cstr_respects_variance => //.
              { do 2 red in onty. destruct onty as (_ & s & hs & _).
                rewrite ceq in hs. eapply PCUICClosedTyp.subject_closed in hs.
                len in hs.
                rewrite -it_mkProd_or_LetIn_app in hs.
                rewrite closedn_it_mkProd_or_LetIn in hs.
                move/andP: hs => [] cl _. move: cl.
                rewrite -app_context_assoc.
                rewrite !trans_local_app !trans_smash_context trans_expand_lets_ctx /=.
                rewrite !trans_smash_context.
                rewrite -(smash_context_app_expand []).
                rewrite closedn_ctx_app /=; len => h.
                apply/andP; split => //.
                now apply closedn_smash_context. }
              { rewrite ceq in onty.
                rewrite /cstr_concl in onty.
                destruct onty as (_ & s & hs & _).
                rewrite -it_mkProd_or_LetIn_app in hs.
                eapply PCUICSpine.type_it_mkProd_or_LetIn_inv in hs as [Δs [us []]].
                eapply typing_expand_lets in t. eapply subject_closed in t; move: t.
                len. rewrite PCUICSigmaCalculus.expand_lets_mkApps.
                rewrite closedn_mkApps => /andP[] _.
                rewrite map_app forallb_app => /andP[] _.
                move/forallb_All. solve_all.
                rewrite trans_expand_lets trans_local_app.
                now rewrite !context_assumptions_map in b. }
            + destruct lets_in_constructor_types.
              ++ eauto.
              ++ red in on_lets_in_type. red. rewrite <- on_lets_in_type.
                 destruct x. clear. cbn.
                 induction cstr_args0.
                 +++ reflexivity.
                 +++ cbn. destruct (decl_body a); cbn; eauto.
        --- simpl; intros. have onp := oni.(ST.onProjections).
            destruct (Ast.Env.ind_projs idecl) => //.
            destruct (Ast.Env.ind_ctors idecl) as [|? []] eqn:hctors => //.
            cbn -[Σg]. destruct onp; split; auto.
            cbn -[Σg]. now len. now len. len. rewrite on_projs_all.
            now rewrite context_assumptions_map.
            cbn -[Σg]. eapply Alli_map, Alli_impl; tea.
            intros i [pname pdecl].
            unfold ST.on_projection, on_projection. cbn -[inds Σg].
            rewrite context_assumptions_map.
            rewrite -[trans_local _ _ ++ _]trans_local_app -(trans_smash_context _ []) nth_error_map.
            rewrite /app_context. destruct nth_error => // /=.
            rewrite /trans_projection_body /=.
            move=> [] /= hb -> ->. cbn -[Σg]. split => //.
            rewrite trans_subst trans_inds. cbn -[Σg]. f_equal.
            rewrite trans_subst trans_lift. f_equal. now rewrite trans_projs.
        --- have inds := oni.(ST.ind_sorts).
            eapply trans_check_ind_sorts in inds; tea.
        --- have compat := oni.(ST.ind_relevance_compat).
            apply compat.
        --- have inds := oni.(ST.onIndices).
            simpl.
            destruct Ast.Env.ind_variance => //.
            eapply trans_ind_respects_variance; tea.
            move: onarityred; cbn -[Σg].
            move=> [] _ [] s [] /subject_closed. rewrite -it_mkProd_or_LetIn_app closedn_it_mkProd_or_LetIn /=.
            rewrite andb_true_r trans_local_app //.
      -- red in onP. red.
          epose proof (Typing.env_prop_wf_local template_to_pcuic (Σg, Ast.Env.ind_universes m) X0 _ onP).
          cbv beta in X1. apply X1 => //.
      -- cbn -[trans_global]. rewrite context_assumptions_map //.
      -- simpl.
          clear -onVariance. move: onVariance.
          unfold on_variance, Typing.on_variance.
          destruct Ast.Env.ind_universes => //.
          destruct Ast.Env.ind_variance => //.
          move=> [univs' [i [i' []]]] vu cu cu' hl.
          exists univs', i, i'; split => //.
          all:change (trans_env_env (trans_global_env Σg), univs') with (global_env_ext_map_global_env_ext (trans_global (Σg, univs')));
            now eapply trans_consistent_instance_ext_gen.
Qed.

Lemma template_to_pcuic_env {cf} Σ :Template.Typing.wf Σ -> wf (trans_global_env Σ).
Proof.
  intros Hu.
  eapply trans_on_global_env; eauto. simpl; intros.
  epose proof (ST.env_prop_typing template_to_pcuic _ X Γ).
  forward X2. { destruct X0 as (_ & s & X0 & _). now eapply ST.typing_wf_local. }
  destruct X0 as (Hb & s & Ht & e). unfold judgment_map.
  repeat (eexists; tea); cbn.
  - destruct j_term => //. eapply X2; eauto.
  - eapply (X2 _ (Ast.tSort s)); eauto.
Qed.

Lemma template_to_pcuic_env_ext {cf} Σ :Template.Typing.wf_ext Σ -> wf_ext (trans_global Σ).
Proof.
  intros [u Hu].
  split. now apply template_to_pcuic_env.
  rewrite trans_env_env_universes.
  now destruct Σ as [Σ udecl]; cbn in *.
Qed.

Theorem template_to_pcuic_typing {cf} {Σ : Ast.Env.global_env_ext} Γ t T :
  ST.wf Σ ->
  ST.typing Σ Γ t T ->
  let Σ' := trans_global Σ in
  typing Σ' (trans_local Σ' Γ) (trans Σ' t) (trans Σ' T).
Proof.
  intros wf ty.
  apply (ST.env_prop_typing template_to_pcuic); auto.
  now eapply ST.typing_wf_local.
  now apply template_to_pcuic_env.
Qed.
