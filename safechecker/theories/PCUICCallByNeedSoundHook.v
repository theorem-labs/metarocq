(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICUnivSubst
  PCUICWeakeningEnvTyp.
From MetaRocq.SafeChecker Require Import PCUICCallByNeedSoundMemo.

(** * The instance condition of the delta rule

  [PCUICCallByNeedSoundMemo.delta_red1] reduces [tConst kn ui] to the code the machine's
  [delta] hands back, for every instance, under one premise that only bites when [ui] is
  empty: [kn]'s universe context must have no variable. [inst_code []] is the identity where
  [red_delta] substitutes the empty instance, so the two differ on a polymorphic constant
  applied to [[]], in any environment. This file defines the property [consts_okb] that
  gives the premise ([inst_okb_nil]) and proves it of well-typed terms and of constant
  bodies. [PCUICCallByNeedSoundEval.machine_sound] discharges the premise with it, and the
  hook establishes it for the let-bodies of the context in
  [PCUICCallByNeedSoundHookFrame.eval_section_instance].

  [consts_okb Σ t] says that every constant the *machine* can reach from [t] carries an
  instance of the right length: at [tConst kn u], that [lookup_env Σ kn] is a constant
  whose universe context has exactly [#|u|] variables. It recurses through at least the
  subterms [code_inv]'s [step] takes (application, the two sides of a binder, the three
  of a let, a case's parameters, return clause, discriminee and branch bodies, a
  projection's argument, and a (co)fixpoint's types and bodies); it also enters the
  arguments of a [tEvar]. The machine never makes a child code at a [tPrim] or inside a
  case's [pcontext]/[bcontext], so [consts_okb] is [true] there.
  [PCUICCallByNeedSoundEval.code_inv_consts_okb] carries it along the machine's codes.

  [typing_consts_okb] proves it of every well-typed term, by [typing_ind_env] with the
  property that ignores the type, so no substitution lemma is needed: the conclusion term
  of every typing rule is built from the premises' terms, never from their types. The
  [tConst] case is exactly [type_Const]'s own [consistent_instance_ext] premise, through
  [consistent_instance_length].

  [declared_constant_consts_okb] does the same for the body of a declared constant — the
  case the evaluator really needs, because [delta] unfolds a body and keeps evaluating
  inside it, so the constants the run reaches are not only subterms of the hook's [t] and
  [u]. A well-formed environment types each constant body in its own universes
  ([on_declared_constant]), and [consts_okb] does not mention the universe declaration at
  all — it is about [lookup_env] and lengths — so the same statement transfers. *)

(** ** The instance condition as a boolean on terms *)

Definition inst_okb (Σ : global_env) (kn : kername) (u : Instance.t) : bool :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      Nat.eqb #|polymorphic_instance cb.(cst_universes)| #|u|
  | _ => false
  end.

Fixpoint consts_okb (Σ : global_env) (t : term) : bool :=
  match t with
  | tConst kn u => inst_okb Σ kn u
  | tEvar _ args => forallb (consts_okb Σ) args
  | tProd _ A B
  | tLambda _ A B => consts_okb Σ A && consts_okb Σ B
  | tLetIn _ b B u => consts_okb Σ b && consts_okb Σ B && consts_okb Σ u
  | tApp f a => consts_okb Σ f && consts_okb Σ a
  | tCase _ p c brs =>
      forallb (consts_okb Σ) p.(pparams) && consts_okb Σ p.(preturn)
      && consts_okb Σ c && forallb (fun br => consts_okb Σ br.(bbody)) brs
  | tProj _ c => consts_okb Σ c
  | tFix mfix _
  | tCoFix mfix _ =>
      forallb (fun d => consts_okb Σ d.(dtype) && consts_okb Σ d.(dbody)) mfix
  | _ => true
  end.

(** What the premise of [delta_red1] asks for, read off [consts_okb]. *)
Lemma inst_okb_spec (Σ : global_env) (kn : kername) (u : Instance.t) (cb : constant_body) :
  inst_okb Σ kn u -> lookup_env Σ kn = Some (ConstantDecl cb) ->
  #|polymorphic_instance cb.(cst_universes)| = #|u|.
Proof.
  unfold inst_okb. intros h hl. rewrite hl in h. now apply PeanoNat.Nat.eqb_eq in h.
Qed.

Lemma inst_okb_nil (Σ : global_env) (kn : kername) (cb : constant_body) :
  inst_okb Σ kn [] -> lookup_env Σ kn = Some (ConstantDecl cb) ->
  #|polymorphic_instance cb.(cst_universes)| = 0.
Proof. intros h hl. exact (inst_okb_spec Σ kn [] cb h hl). Qed.

(** ** Every well-typed term satisfies it *)

Lemma ctx_inst_consts_okb {cf : checker_flags} (Σ : global_env_ext) (Γ : context)
    (l : list term) (Δ : context) :
  ctx_inst (Prop_conj typing (fun Σ _ t _ => consts_okb Σ.1 t) Σ) Γ l Δ ->
  All (fun t => consts_okb Σ.1 t) l.
Proof.
  induction 1 as [|na t i inst Δ ty hc IH|na b t inst Δ hc IH].
  - constructor.
  - constructor; [exact (snd ty) | exact IH].
  - exact IH.
Qed.

Lemma typing_consts_okb {cf : checker_flags} :
  env_prop (fun Σ _ t _ => consts_okb Σ.1 t)
    (fun Σ _ j => option_default (consts_okb Σ.1) (j_term j) true
                  && consts_okb Σ.1 (j_typ j))
    (fun _ _ => True).
Proof.
  apply typing_ind_env.
  - (* judgments *)
    intros Σ wfΣ Γ j X. destruct j as [tm ty univ r]; cbn in *.
    destruct X as [h1 [s [h2 _]]].
    apply andb_true_iff. split.
    + destruct tm as [tm|]; cbn in h1 |- *; [exact (snd h1) | reflexivity].
    + exact (snd h2).
  - (* contexts *) intros. exact I.
  - (* tRel *) intros. reflexivity.
  - (* tSort *) intros. reflexivity.
  - (* tProd *) intros Σ wfΣ Γ wfΓ na t b s1 s2 _ _ hj _ hb.
    cbn in hj |- *. now rewrite hj, hb.
  - (* tLambda *) intros Σ wfΣ Γ wfΓ na t b bty _ _ hj _ hb.
    cbn in hj |- *. now rewrite hj, hb.
  - (* tLetIn *) intros Σ wfΣ Γ wfΓ na b b_ty b' b'_ty _ _ hj _ hb'.
    cbn in hj |- *. apply andb_true_iff in hj as [h1 h2].
    now rewrite h1, h2, hb'.
  - (* tApp *) intros Σ wfΣ Γ wfΓ t na A B u s _ _ _ _ ht _ hu.
    cbn. now rewrite ht, hu.
  - (* tConst *) intros Σ wfΣ Γ wfΓ cst u decl _ _ hdecl hcons.
    cbn. unfold inst_okb.
    unshelve eapply declared_constant_to_gen in hdecl; eauto.
    unfold declared_constant_gen in hdecl. rewrite hdecl.
    apply PeanoNat.Nat.eqb_eq. rewrite poly_instance_abstract.
    now rewrite <- (consistent_instance_length (Σ := Σ) (univs := decl.(cst_universes)) hcons).
  - (* tInd *) intros. reflexivity.
  - (* tConstruct *) intros. reflexivity.
  - (* tCase *)
    intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl _ _ _ _ predctx
      wfp hcons wfpctx pret hpret _ _ _ hctxi hc hcc _ ptm wfbrs hbrs.
    cbn. apply andb_true_iff; split; [apply andb_true_iff; split;
      [apply andb_true_iff; split|]|].
    + apply All_forallb.
      pose proof (ctx_inst_consts_okb Σ Γ _ _ hctxi) as hall.
      now eapply All_app in hall as [hall _].
    + exact hpret.
    + exact hcc.
    + apply All_forallb.
      clear -hbrs. induction hbrs as [|n' x y l r hd _ IH]; constructor; [|exact IH].
      destruct hd as [_ [_ [[_ hbody] _]]]. exact hbody.
  - (* tProj *) intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args _ _ _ hc _.
    cbn. exact hc.
  - (* tFix *) intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth _ _ hty _ hbody _.
    cbn. apply All_forallb. eapply All_impl; [exact (All_mix hty hbody)|].
    intros d [ht hb]. apply andb_true_iff. split.
    + unfold on_def_type in ht. cbn in ht. exact ht.
    + unfold on_def_body in hb. cbn in hb. now apply andb_true_iff in hb as [h _].
  - (* tCoFix *) intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth _ _ hty _ hbody _.
    cbn. apply All_forallb. eapply All_impl; [exact (All_mix hty hbody)|].
    intros d [ht hb]. apply andb_true_iff. split.
    + unfold on_def_type in ht. cbn in ht. exact ht.
    + unfold on_def_body in hb. cbn in hb. now apply andb_true_iff in hb as [h _].
  - (* tPrim *) intros. reflexivity.
  - (* cumulativity *) intros Σ wfΣ Γ wfΓ t A B s _ _ ht _ _ _. exact ht.
Qed.

Lemma typing_consts_okb' {cf : checker_flags} (Σ : global_env_ext) (Γ : context)
    (t T : term) :
  wf Σ -> Σ ;;; Γ |- t : T -> consts_okb Σ.1 t.
Proof. intros wfΣ ty. exact (snd (snd (typing_consts_okb Σ wfΣ Γ t T ty))). Qed.

(** ** The constants reached inside an unfolded body

    The evaluator does not only reach constants that are subterms of the hook's [t] and
    [u]: [delta] unfolds a constant's body and keeps evaluating inside it. But in a
    well-formed environment that body is itself well-typed, in the constant's own
    universes ([on_declared_constant]), and [consts_okb] does not read the universe
    declaration at all — only [lookup_env] and instance lengths — so the same property
    holds of it. This is the case the bridge really needs. *)

Lemma declared_constant_consts_okb {cf : checker_flags} (Σ : global_env)
    (kn : kername) (cb : constant_body) (body : term) :
  wf Σ -> declared_constant Σ kn cb -> cb.(cst_body) = Some body ->
  consts_okb Σ body.
Proof.
  intros wfΣ hdecl hb.
  pose proof (on_declared_constant wfΣ hdecl) as hon.
  unfold on_constant_decl in hon. rewrite hb in hon. cbn in hon.
  destruct hon as [hck _].
  exact (typing_consts_okb' (Σ, cst_universes cb) [] body (cst_type cb) wfΣ hck).
Qed.
