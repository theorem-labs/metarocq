(* Distributed under the terms of the MIT license. *)
(** * Parallel eta-contraction and strong commutation with beta (BET-315, lane eta, row C3)

  This file is owned by C3Prover2.  It adds, BESIDE [eta1] (which is defined elsewhere and is
  never redefined here), a PARALLEL eta-contraction relation, and the infrastructure the
  commutation proof needs on the [red1] side.

  Part 1 (uses no eta relation at all): inversion of [red1] through a lift, i.e. strengthening,
  and the inversion of [red1] on the body of an eta-redex. *)

From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICReduction PCUICCases
     PCUICTyping PCUICOnFreeVars PCUICSigmaCalculus PCUICClosed
     PCUICRenameDef PCUICRenameConv PCUICInstDef PCUICInstConv
     PCUICOnFreeVarsConv PCUICClosedTyp BDStrengthening PCUICEtaDefs
     PCUICEquality PCUICPrimitive.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

(** ** The "variable 0 does not occur" predicate

  [on_free_vars xpredT t] is NOT trivially true in this AST: the case predicate and branch
  contexts of [t] must be closed with respect to the parameters ([closedP]).  It is implied by
  the plan's scoping premise [is_open_term Γ t] and is carried explicitly below.
  [on_ctx_free_vars_nondep] is proved in [PCUICSR.v:1486]; it is reproved here so that this
  file does not depend on the subject-reduction file. *)

Lemma on_ctx_free_vars_nondep' ctx :
  on_ctx_free_vars xpredT ctx -> on_ctx_free_vars (strengthenP 0 1 xpredT) ctx.
Proof.
  rewrite /on_ctx_free_vars.
  enough (h : forall n,
    alli (fun k d => xpredT k ==> on_free_vars_decl (addnP (S k) xpredT) d) n ctx ->
    alli (fun k d => strengthenP 0 1 xpredT k ==>
      on_free_vars_decl (addnP (S k) (strengthenP 0 1 xpredT)) d) n ctx) by apply h.
  induction ctx as [|d ctx ih] => n //=.
  move/andP => [hd hctx]. apply/andP; split; [|now apply ih].
  apply/implyP => _. eapply (on_free_vars_decl_impl (addnP (S n) xpredT)); [|exact hd].
  intros i _. rewrite /addnP PCUICOnFreeVars.strengthenP01.
  apply/negP => /Nat.eqb_eq. lia.
Qed.

Lemma on_ctx_free_vars_nondep_ctx ctx :
  on_free_vars_ctx xpredT ctx -> on_ctx_free_vars (strengthenP 0 1 xpredT) ctx.
Proof.
  intros h. apply on_ctx_free_vars_nondep'. now rewrite on_ctx_free_vars_xpredT.
Qed.

(** ** Strengthening for [red1]

  A [red1] step of a lifted term, in a context extended by one declaration, is the lift of a
  [red1] step of the term.  Proved through [red1_rename] with the unlifting renaming.  Premises:
  [wf Σ] (needed for [red_delta]: the body of a constant is closed) and the scoping premises. *)

Section Strengthening.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma unlift_lift0 t : unlift 1 0 (lift0 1 t) = t.
  Proof using Type. apply lift_unlift_term. Qed.

  Lemma lift0_unlift_nondep t :
    on_free_vars (strengthenP 0 1 xpredT) t ->
    lift0 1 (unlift 1 0 t) = t.
  Proof using Type.
    intros h.
    rewrite /unlift lift_rename rename_compose.
    transitivity (rename ren_id t); [|now rewrite rename_ren_id].
    eapply rename_ext_cond; [|exact h].
    intros i hi.
    destruct i as [|i].
    { move: hi. now rewrite PCUICOnFreeVars.strengthenP01. }
    cbn. rewrite /lift_renaming /unlift_renaming /ren_id /=. lia.
  Qed.

  Lemma red1_strengthen Γ d s q :
    on_free_vars xpredT s ->
    on_free_vars_ctx xpredT (Γ ,, d) ->
    red1 Σ (Γ ,, d) (lift0 1 s) q ->
    ∑ s', red1 Σ Γ s s' × q = lift0 1 s'.
  Proof using cf wfΣ.
    intros hs0 hctx0 r.
    have hs : on_free_vars (strengthenP 0 1 xpredT) (lift0 1 s).
    { now rewrite on_free_vars_lift. }
    have hq : on_free_vars (strengthenP 0 1 xpredT) q.
    { exact (@red1_on_free_vars cf _ Σ _ _ _ wfΣ r hs (on_ctx_free_vars_nondep_ctx _ hctx0)). }
    have hu : urenaming (strengthenP 0 1 xpredT) (Γ ,, d) Γ (unlift_renaming 1 0).
    { have h := urenaming_strengthen xpredT Γ [d] [].
      cbn in h. now rewrite /app_context /= in h. }
    have rr := red1_rename _ _ _ _ _ _ _ wfΣ hu hs r.
    exists (unlift 1 0 q). split.
    - rewrite -{1}(unlift_lift0 s). exact rr.
    - now rewrite lift0_unlift_nondep.
  Qed.

  (** ** Inversion of [red1] on the body of an eta-redex

    The body of an eta-redex is [tApp (lift0 1 s) (tRel 0)] under one assumption.  Its [red1]
    steps are: a step of [s] through the lift, or the beta step that the redex
    [tApp (lift0 1 (tLambda _ _ b)) (tRel 0)] exposes, whose result is [b] itself.  The
    argument [tRel 0] is never reducible, the declaration being an assumption. *)

  Lemma mkApps_tFix_neq_tRel mfix idx args n : mkApps (tFix mfix idx) args = tRel n -> False.
  Proof using Type.
    destruct args as [|a args _] using rev_ind; cbn.
    - intros h; noconf h.
    - rewrite mkApps_app /=. intros h; noconf h.
  Qed.

  Lemma red1_tRel0_vass Γ na A N : red1 Σ (Γ ,, vass na A) (tRel 0) N -> False.
  Proof using Type.
    intros r. depelim r.
    - match goal with H : _ = Some (Some _) |- _ => simpl in H; noconf H end.
    - match goal with H : tRel 0 = _ |- _ =>
        symmetry in H; now eapply mkApps_tFix_neq_tRel end.
  Qed.

  Lemma red1_eta_body Γ na A s M' :
    on_free_vars xpredT s ->
    on_free_vars_ctx xpredT (Γ ,, vass na A) ->
    red1 Σ (Γ ,, vass na A) (tApp (lift0 1 s) (tRel 0)) M' ->
      (∑ s', red1 Σ Γ s s' × M' = tApp (lift0 1 s') (tRel 0))
    + (∑ nb B b, s = tLambda nb B b × M' = b).
  Proof using cf wfΣ.
    intros hs hctx r. depelim r.
    - (* beta *)
      right. destruct s => //. cbn in H. noconf H.
      do 3 eexists; split; [reflexivity|].
      change (subst [tRel 0] 0 (lift 1 1 s2) = s2).
      rewrite (subst_reli_lift_id 0 0 s2 (le_n 0)). apply lift0_id.
    - (* fix: the fix redex is inside [lift0 1 s], the last argument [tRel 0] not being
         a constructor application *)
      left.
      destruct args as [|a args _] using rev_ind.
      { cbn in H. noconf H. }
      rewrite mkApps_app /= in H.
      assert (h1 : lift0 1 s = mkApps (tFix mfix idx) args) by (now noconf H).
      assert (h2 : a = tRel 0) by (now noconf H).
      subst a.
      assert (hic : is_constructor narg args = true).
      { move: e0. rewrite /is_constructor.
        destruct (Nat.ltb_spec narg #|args|) as [hlt|hge].
        - now rewrite nth_error_app_lt.
        - rewrite nth_error_app_ge //.
          destruct (narg - #|args|) as [|k] eqn:he; cbn.
          + rewrite /isConstruct_app /= //.
          + rewrite nth_error_nil //. }
      have rs : red1 Σ (Γ ,, vass na A) (lift0 1 s) (mkApps fn args).
      { rewrite h1. now econstructor. }
      destruct (red1_strengthen _ _ _ _ hs hctx rs) as [s' [rs' eq]].
      exists s'. split => //. rewrite mkApps_app /=. now rewrite eq.
    - (* app_red_l *)
      left. destruct (red1_strengthen _ _ _ _ hs hctx r) as [s' [rs' eq]].
      exists s'. split => //. now subst.
    - (* app_red_r *)
      exfalso. now eapply red1_tRel0_vass.
  Qed.

End Strengthening.

(** * Part 2: eta congruences, mkApps inversion, and the four β-head cases of C3

  All of Part 2 uses the shared [eta1]/[eta]/[upto_domain] of [PCUICEtaDefs], never a private
  copy. *)

Lemma eta_refl t : eta t t.
Proof. apply rt_refl. Qed.

Lemma eta_step {t u} : eta1 t u -> eta t u.
Proof. apply rt_step. Qed.

Lemma eta_trans {t u v} : eta t u -> eta u v -> eta t v.
Proof. apply rt_trans. Qed.

Lemma eta_App_l a a' b : eta a a' -> eta (tApp a b) (tApp a' b).
Proof.
  induction 1.
  - apply eta_step. now constructor.
  - apply eta_refl.
  - eapply eta_trans; eauto.
Qed.

Lemma eta_App_r a b b' : eta b b' -> eta (tApp a b) (tApp a b').
Proof.
  induction 1.
  - apply eta_step. now constructor.
  - apply eta_refl.
  - eapply eta_trans; eauto.
Qed.

Lemma eta_Proj p c c' : eta c c' -> eta (tProj p c) (tProj p c').
Proof.
  induction 1.
  - apply eta_step. now constructor.
  - apply eta_refl.
  - eapply eta_trans; eauto.
Qed.

Lemma eta_mkApps_f h h' l : eta h h' -> eta (mkApps h l) (mkApps h' l).
Proof.
  intros e. revert h h' e. induction l as [|a l ih] using rev_ind; intros h h' e.
  - exact e.
  - rewrite !mkApps_app /=. apply eta_App_l. now apply ih.
Qed.

(** Stepping the function of an application propagates through a spine. *)
Lemma eta1_mkApps_head g g' l :
  eta1 g g' -> eta1 (mkApps g l) (mkApps g' l).
Proof.
  intros e. induction l as [|c l ih] in g, g', e |- *.
  - exact e.
  - cbn. apply ih. now apply app_eta_l.
Qed.

(** One [OnOne2 eta1] step on the argument list is one [eta1] step on the application. *)
Lemma eta1_mkApps_arg h l1 a a' l2 :
  eta1 a a' ->
  eta1 (mkApps h (l1 ++ a :: l2)) (mkApps h (l1 ++ a' :: l2)).
Proof.
  intros e.
  replace (l1 ++ a :: l2) with ((l1 ++ [a]) ++ l2) by now rewrite -app_assoc.
  replace (l1 ++ a' :: l2) with ((l1 ++ [a']) ++ l2) by now rewrite -app_assoc.
  rewrite !mkApps_app /=. apply eta1_mkApps_head. now apply app_eta_r.
Qed.

Lemma eta1_OnOne2_mkApps h l l' :
  OnOne2 eta1 l l' -> eta1 (mkApps h l) (mkApps h l').
Proof.
  intros o. apply OnOne2_split in o as [a [a' [u [v [e [-> ->]]]]]].
  now apply eta1_mkApps_arg.
Qed.

Lemma eta_OnOne2_mkApps h l l' :
  OnOne2 eta1 l l' -> eta (mkApps h l) (mkApps h l').
Proof. intros o. apply eta_step. now apply eta1_OnOne2_mkApps. Qed.

(** ** Inversion of [eta1] on an application with a rigid (non-[tApp]) head *)
Lemma eta1_mkApps_inv h l u :
  ~~ isApp h ->
  eta1 (mkApps h l) u ->
  (∑ h', eta1 h h' × u = mkApps h' l) +
  (∑ l', OnOne2 eta1 l l' × u = mkApps h l').
Proof.
  intros nih. revert u. induction l as [|a l ih] using rev_ind; intros u e.
  - left. exists u. split => //.
  - rewrite mkApps_app /= in e. depelim e.
    + destruct (ih _ e) as [[h' [eh ->]]|[l' [ol ->]]].
      * left. exists h'. split => //. now rewrite mkApps_app.
      * right. exists (l' ++ [a]). split; [now apply OnOne2_app_r|now rewrite mkApps_app].
    + right. exists (l ++ [N2]). split.
      * apply OnOne2_app. now constructor.
      * now rewrite mkApps_app.
Qed.

(** [eta1] preserves a constructor head. *)
Lemma eta1_isConstruct_app a a' :
  eta1 a a' -> isConstruct_app a -> isConstruct_app a'.
Proof.
  intros e. unfold isConstruct_app.
  destruct (decompose_app a) as [hd args] eqn:da.
  destruct hd; try discriminate. intros _.
  apply decompose_app_inv in da. subst a.
  assert (nih : ~~ isApp (tConstruct ind n ui)) by reflexivity.
  destruct (eta1_mkApps_inv _ _ _ nih e) as [[h' [eh ->]]|[l' [ol ->]]].
  - depelim eh.
  - now rewrite decompose_app_mkApps.
Qed.

(** [is_constructor] at any index is preserved by one [eta1] step in the spine. *)
Lemma is_constructor_OnOne2_eta1 narg l l' :
  OnOne2 eta1 l l' -> is_constructor narg l -> is_constructor narg l'.
Proof.
  intros o. unfold is_constructor.
  destruct (nth_error l narg) as [t|] eqn:hn => //.
  intros hc.
  destruct (OnOne2_nth_error _ _ _ _ _ o hn) as [t' [hn' [<-|et]]].
  - now rewrite hn'.
  - rewrite hn'. eapply eta1_isConstruct_app; eauto.
Qed.

(** ** [All2 eta] on the fixpoint/cofixpoint substitutions

  If every [tFix mfix j] (resp. [tCoFix]) [eta]-steps to [tFix mfix1 j], then the whole
  [fix_subst] (resp. [cofix_subst]) is [All2 eta]-related. *)
Lemma All2_eta_fix_subst mfix mfix1 :
  #|mfix| = #|mfix1| ->
  (forall j, eta (tFix mfix j) (tFix mfix1 j)) ->
  All2 eta (fix_subst mfix) (fix_subst mfix1).
Proof.
  intros len he. unfold fix_subst. rewrite len.
  generalize (#|mfix1|) as n. intros n.
  induction n as [|n ih]; cbn.
  - constructor.
  - constructor; [apply he|exact ih].
Qed.

Lemma All2_eta_cofix_subst mfix mfix1 :
  #|mfix| = #|mfix1| ->
  (forall j, eta (tCoFix mfix j) (tCoFix mfix1 j)) ->
  All2 eta (cofix_subst mfix) (cofix_subst mfix1).
Proof.
  intros len he. unfold cofix_subst. rewrite len.
  generalize (#|mfix1|) as n. intros n.
  induction n as [|n ih]; cbn.
  - constructor.
  - constructor; [apply he|exact ih].
Qed.

Lemma eta_Case_discr ci p c c' brs : eta c c' -> eta (tCase ci p c brs) (tCase ci p c' brs).
Proof.
  induction 1.
  - apply eta_step. now constructor.
  - apply eta_refl.
  - eapply eta_trans; eauto.
Qed.

(** * The four unlocking β-head cases of C3 (plan §3 row C3, §6 rank 1)

  These are the four cases where η-postponement died (red_fix needs only
  [is_constructor] on the head).  For the *commutation* form, the β-redex already fires
  on [t], so the firing condition holds before the η step; the η step is either in the
  fix/cofix body (propagated through unfolding by [eta], hence the [clos_refl_trans eta1]
  on the β side) or inside a constructor argument (which keeps the constructor head).
  No counterexample arises.

  Carried hypotheses (named; U2 rows of the plan, to be discharged separately):
  - [eta1_subst0], [eta_subst_terms] : U2 closure of η under substitution. *)

(** [upto_domain] reflexivity (plan U1), ported from the 2020 proof
    [origin/eta_postpo:PCUICEquality.v:1503-1508] to the 9.2 AST (adds the [tPrim]/array
    and record-[tCase] clauses). *)
Lemma upto_domain_refl t : upto_domain t t.
Proof.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. now apply All_All2 with (1 := X).
  - destruct X as [hpar [_ hpret]]. constructor.
    + now apply All_All2 with (1 := hpar).
    + reflexivity.
    + reflexivity.
    + exact hpret.
    + exact IHt.
    + eapply All_All2; [exact X0|]. intros x [_ hbody]. split; [reflexivity|exact hbody].
  - constructor. eapply All_All2; [exact X|]. intros x [? ?]. repeat split; assumption.
  - constructor. eapply All_All2; [exact X|]. intros x [? ?]. repeat split; assumption.
  - constructor. destruct p as [tag m]; destruct m; cbn in X.
    + apply onPrimsInt.
    + apply onPrimsFloat.
    + apply onPrimsString.
    + destruct X as [ht [hd hv]]. apply onPrimsArray.
      * reflexivity.
      * exact hd.
      * exact ht.
      * now apply All_All2 with (1 := hv).
Qed.

(** [eta1] is closed under substitution (plan U2), ported from
    [origin/eta_postpo:PCUICSubstitution.v:2159] to the 9.2 AST (adds the split
    [case_eta_param]/[case_eta_return], [case_eta_brs] with contexts, and the [array_eta_*]
    primitive-array congruences). *)
Lemma eta1_subst s k u v :
  eta1 u v -> eta1 (subst s k u) (subst s k v).
Proof.
  induction 1 in k |- * using eta1_ind_all; cbn;
    try (constructor; eauto; fail).
  - refine (transport (fun x => eta1 x _) _ (eta_red _ _ _)). do 2 f_equal.
    symmetry; apply commut_lift_subst.
  - replace (map_predicate_k id (subst s) k (set_pparams p params'))
      with (set_pparams (map_predicate_k id (subst s) k p) (map (subst s k) params'))
      by reflexivity.
    apply case_eta_param.
    eapply OnOne2_map, OnOne2_impl; tea; cbn. intros x y [h1 h2]. exact (h2 k).
  - replace (map_predicate_k id (subst s) k (set_preturn p preturn'))
      with (set_preturn (map_predicate_k id (subst s) k p)
              (subst s (#|p.(pcontext)| + k) preturn'))
      by reflexivity.
    apply case_eta_return. cbn. eauto.
  - apply case_eta_brs.
    eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros [bc bb] [bc' bb'] [[h1 h2] h3]; cbn in *. unfold on_Trel; cbn.
    noconf h3. split; [exact (h2 _)|reflexivity].
  - constructor. eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros x y [h1 h2]. exact (h2 k).
  - constructor. apply OnOne2_length in X as e. rewrite e.
    eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros [] [] [[h1 h2] e0]; cbn in *. noconf e0; split; [exact (h2 _)|reflexivity].
  - apply fix_eta_body. apply OnOne2_length in X as e. rewrite e.
    eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros [] [] [[h1 h2] e0]; cbn in *. noconf e0; split; [exact (h2 _)|reflexivity].
  - constructor. apply OnOne2_length in X as e. rewrite e.
    eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros [] [] [[h1 h2] e0]; cbn in *. noconf e0; split; [exact (h2 _)|reflexivity].
  - apply cofix_eta_body. apply OnOne2_length in X as e. rewrite e.
    eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros [] [] [[h1 h2] e0]; cbn in *. noconf e0; split; [exact (h2 _)|reflexivity].
  - replace (map_array_model (subst s k) (set_array_value arr value))
      with (set_array_value (map_array_model (subst s k) arr) (map (subst s k) value))
      by reflexivity.
    apply array_eta_val. eapply OnOne2_map, OnOne2_impl; tea; cbn.
    intros x y [h1 h2]. exact (h2 k).
  - replace (map_array_model (subst s k) (set_array_default arr d))
      with (set_array_default (map_array_model (subst s k) arr) (subst s k d))
      by reflexivity.
    apply array_eta_def. cbn. eauto.
  - replace (map_array_model (subst s k) (set_array_type arr ty))
      with (set_array_type (map_array_model (subst s k) arr) (subst s k ty))
      by reflexivity.
    apply array_eta_type. cbn. eauto.
Qed.

Section FourCases.
  Context {cf : checker_flags}.
  Context {Σ : global_env} {wfΣ : wf Σ}.

  (* eta1_subst0 is now DISCHARGED (eta1_subst at level 0), not a hypothesis. *)
  Let eta1_subst0 s M M' (h : eta1 M M') : eta1 (subst0 s M) (subst0 s M') :=
    eta1_subst s 0 M M' h.
  Hypothesis eta_subst_terms :
    forall s s' M, All2 eta s s' -> eta (subst0 s M) (subst0 s' M).

  Definition C3_concl Γ u v :=
    ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.

  (** eta commutes with fixpoint unfolding (dtype step). *)
  Lemma unfold_fix_eta_ty mfix mfix1 idx narg fn :
    OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix1 ->
    unfold_fix mfix idx = Some (narg, fn) ->
    ∑ fn1, unfold_fix mfix1 idx = Some (narg, fn1) × eta fn fn1.
  Proof using eta_subst_terms.
    intros o hf.
    have len := OnOne2_length o.
    unfold unfold_fix in *.
    destruct (nth_error mfix idx) as [d|] eqn:hn => //. noconf hf.
    destruct (OnOne2_nth_error _ _ _ _ _ o hn) as [d1 [hn1 hd]].
    assert (rarg d1 = rarg d /\ dbody d1 = dbody d) as [hr hb].
    { destruct hd as [<-|[_ heq]]; [split; reflexivity|].
      injection heq. intros -> -> _. split; reflexivity. }
    rewrite hn1. eexists; split.
    - now rewrite hr.
    - rewrite hb. apply eta_subst_terms.
      apply All2_eta_fix_subst; [exact len|].
      intros j. apply eta_step. now apply fix_eta_ty.
  Qed.

  (** eta commutes with fixpoint unfolding (dbody step). *)
  Lemma unfold_fix_eta_body mfix mfix1 idx narg fn :
    OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix mfix1 ->
    unfold_fix mfix idx = Some (narg, fn) ->
    ∑ fn1, unfold_fix mfix1 idx = Some (narg, fn1) × eta fn fn1.
  Proof using eta1_subst0 eta_subst_terms.
    intros o hf.
    have len := OnOne2_length o.
    unfold unfold_fix in *.
    destruct (nth_error mfix idx) as [d|] eqn:hn => //. noconf hf.
    destruct (OnOne2_nth_error _ _ _ _ _ o hn) as [d1 [hn1 hd]].
    have hsub : All2 eta (fix_subst mfix) (fix_subst mfix1).
    { apply All2_eta_fix_subst; [exact len|].
      intros j. apply eta_step. now apply fix_eta_body. }
    rewrite hn1.
    assert ((rarg d1 = rarg d) × eta (dbody d) (dbody d1)) as [hr hb].
    { destruct hd as [<-|[eb heq]].
      - split; [reflexivity|apply eta_refl].
      - injection heq. intros -> _ _. split; [reflexivity|now apply eta_step]. }
    eexists; split.
    - now rewrite hr.
    - eapply eta_trans.
      + apply (eta_subst_terms _ _ (dbody d) hsub).
      + clear -hb eta1_subst0. induction hb.
        * apply eta_step. now apply eta1_subst0.
        * apply eta_refl.
        * eapply eta_trans; eauto.
  Qed.

  (** eta commutes with cofixpoint unfolding (dtype step). *)
  Lemma unfold_cofix_eta_ty mfix mfix1 idx narg fn :
    OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix1 ->
    unfold_cofix mfix idx = Some (narg, fn) ->
    ∑ fn1, unfold_cofix mfix1 idx = Some (narg, fn1) × eta fn fn1.
  Proof using eta_subst_terms.
    intros o hf.
    have len := OnOne2_length o.
    unfold unfold_cofix in *.
    destruct (nth_error mfix idx) as [d|] eqn:hn => //. noconf hf.
    destruct (OnOne2_nth_error _ _ _ _ _ o hn) as [d1 [hn1 hd]].
    assert (rarg d1 = rarg d /\ dbody d1 = dbody d) as [hr hb].
    { destruct hd as [<-|[_ heq]]; [split; reflexivity|].
      injection heq. intros -> -> _. split; reflexivity. }
    rewrite hn1. eexists; split.
    - now rewrite hr.
    - rewrite hb. apply eta_subst_terms.
      apply All2_eta_cofix_subst; [exact len|].
      intros j. apply eta_step. now apply cofix_eta_ty.
  Qed.

  (** eta commutes with cofixpoint unfolding (dbody step). *)
  Lemma unfold_cofix_eta_body mfix mfix1 idx narg fn :
    OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix mfix1 ->
    unfold_cofix mfix idx = Some (narg, fn) ->
    ∑ fn1, unfold_cofix mfix1 idx = Some (narg, fn1) × eta fn fn1.
  Proof using eta1_subst0 eta_subst_terms.
    intros o hf.
    have len := OnOne2_length o.
    unfold unfold_cofix in *.
    destruct (nth_error mfix idx) as [d|] eqn:hn => //. noconf hf.
    destruct (OnOne2_nth_error _ _ _ _ _ o hn) as [d1 [hn1 hd]].
    have hsub : All2 eta (cofix_subst mfix) (cofix_subst mfix1).
    { apply All2_eta_cofix_subst; [exact len|].
      intros j. apply eta_step. now apply cofix_eta_body. }
    rewrite hn1.
    assert ((rarg d1 = rarg d) × eta (dbody d) (dbody d1)) as [hr hb].
    { destruct hd as [<-|[eb heq]].
      - split; [reflexivity|apply eta_refl].
      - injection heq. intros -> _ _. split; [reflexivity|now apply eta_step]. }
    eexists; split.
    - now rewrite hr.
    - eapply eta_trans.
      + apply (eta_subst_terms _ _ (dbody d) hsub).
      + clear -hb eta1_subst0. induction hb.
        * apply eta_step. now apply eta1_subst0.
        * apply eta_refl.
        * eapply eta_trans; eauto.
  Qed.

  (** *** red_proj ∘ eta1 *)
  Lemma C3_red_proj Γ p ui args arg u :
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    eta1 (tProj p (mkApps (tConstruct p.(proj_ind) 0 ui) args)) u ->
    C3_concl Γ u arg.
  Proof using Type.
    intros hn e. depelim e.
    assert (nih : ~~ isApp (tConstruct (proj_ind p) 0 ui)) by reflexivity.
    destruct (eta1_mkApps_inv _ _ _ nih e) as [[h' [eh ->]]|[l' [ol ->]]].
    - depelim eh.
    - destruct (OnOne2_nth_error _ _ _ _ _ ol hn) as [arg' [hn' harg]].
      exists arg', arg'. split; [|split].
      + constructor. now econstructor.
      + destruct harg as [<-|ea]; [apply rt_refl|apply rt_step; exact ea].
      + apply upto_domain_refl.
  Qed.

  (** *** red_fix ∘ eta1 *)
  Lemma C3_red_fix Γ mfix idx args narg fn u :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    eta1 (mkApps (tFix mfix idx) args) u ->
    C3_concl Γ u (mkApps fn args).
  Proof using eta1_subst0 eta_subst_terms.
    intros hf hc e.
    assert (nih : ~~ isApp (tFix mfix idx)) by reflexivity.
    destruct (eta1_mkApps_inv _ _ _ nih e) as [[h' [eh ->]]|[l' [ol ->]]].
    - (* η in the fix itself *)
      depelim eh.
      + destruct (unfold_fix_eta_ty _ _ _ _ _ o hf) as [fn1 [hf1 efn]].
        exists (mkApps fn1 args), (mkApps fn1 args). split; [|split].
        * constructor. now econstructor.
        * now apply eta_mkApps_f.
        * apply upto_domain_refl.
      + destruct (unfold_fix_eta_body _ _ _ _ _ o hf) as [fn1 [hf1 efn]].
        exists (mkApps fn1 args), (mkApps fn1 args). split; [|split].
        * constructor. now econstructor.
        * now apply eta_mkApps_f.
        * apply upto_domain_refl.
    - (* η in an argument *)
      exists (mkApps fn l'), (mkApps fn l'). split; [|split].
      + constructor. econstructor; [exact hf|].
        eapply is_constructor_OnOne2_eta1; eauto.
      + now apply eta_OnOne2_mkApps.
      + apply upto_domain_refl.
  Qed.

  (** *** red_cofix_proj ∘ eta1 *)
  Lemma C3_red_cofix_proj Γ p mfix idx args narg fn u :
    unfold_cofix mfix idx = Some (narg, fn) ->
    eta1 (tProj p (mkApps (tCoFix mfix idx) args)) u ->
    C3_concl Γ u (tProj p (mkApps fn args)).
  Proof using eta1_subst0 eta_subst_terms.
    intros hf e. depelim e.
    assert (nih : ~~ isApp (tCoFix mfix idx)) by reflexivity.
    destruct (eta1_mkApps_inv _ _ _ nih e) as [[h' [eh ->]]|[l' [ol ->]]].
    - depelim eh.
      + destruct (unfold_cofix_eta_ty _ _ _ _ _ o hf) as [fn1 [hf1 efn]].
        exists (tProj p (mkApps fn1 args)), (tProj p (mkApps fn1 args)). split; [|split].
        * constructor. now econstructor.
        * apply eta_Proj. now apply eta_mkApps_f.
        * apply upto_domain_refl.
      + destruct (unfold_cofix_eta_body _ _ _ _ _ o hf) as [fn1 [hf1 efn]].
        exists (tProj p (mkApps fn1 args)), (tProj p (mkApps fn1 args)). split; [|split].
        * constructor. now econstructor.
        * apply eta_Proj. now apply eta_mkApps_f.
        * apply upto_domain_refl.
    - exists (tProj p (mkApps fn l')), (tProj p (mkApps fn l')). split; [|split].
      + constructor. now econstructor.
      + apply eta_Proj. now apply eta_OnOne2_mkApps.
      + apply upto_domain_refl.
  Qed.

  (** *** red_cofix_case ∘ eta1 *)
  Lemma C3_red_cofix_case Γ ci p mfix idx args narg fn brs u :
    unfold_cofix mfix idx = Some (narg, fn) ->
    eta1 (tCase ci p (mkApps (tCoFix mfix idx) args) brs) u ->
    C3_concl Γ u (tCase ci p (mkApps fn args) brs).
  Proof using eta1_subst0 eta_subst_terms.
    intros hf e. depelim e.
    - (* case_eta_param *)
      eexists _, _. split; [|split].
      + constructor. now econstructor.
      + apply eta_step. now apply case_eta_param.
      + apply upto_domain_refl.
    - (* case_eta_return *)
      eexists _, _. split; [|split].
      + constructor. now econstructor.
      + apply eta_step. now apply case_eta_return.
      + apply upto_domain_refl.
    - (* case_eta_discr *)
      assert (nih : ~~ isApp (tCoFix mfix idx)) by reflexivity.
      destruct (eta1_mkApps_inv _ _ _ nih e) as [[h' [eh ->]]|[l' [ol ->]]].
      + depelim eh.
        * destruct (unfold_cofix_eta_ty _ _ _ _ _ o hf) as [fn1 [hf1 efn]].
          exists (tCase ci p (mkApps fn1 args) brs), (tCase ci p (mkApps fn1 args) brs).
          split; [|split].
          -- constructor. eapply red_cofix_case; exact hf1.
          -- apply eta_Case_discr. apply eta_mkApps_f. exact efn.
          -- apply upto_domain_refl.
        * destruct (unfold_cofix_eta_body _ _ _ _ _ o hf) as [fn1 [hf1 efn]].
          exists (tCase ci p (mkApps fn1 args) brs), (tCase ci p (mkApps fn1 args) brs).
          split; [|split].
          -- constructor. eapply red_cofix_case; exact hf1.
          -- apply eta_Case_discr. apply eta_mkApps_f. exact efn.
          -- apply upto_domain_refl.
      + exists (tCase ci p (mkApps fn l') brs), (tCase ci p (mkApps fn l') brs).
        split; [|split].
        * constructor. now econstructor.
        * apply eta_Case_discr. now apply eta_OnOne2_mkApps.
        * apply upto_domain_refl.
    - (* case_eta_brs *)
      eexists _, _. split; [|split].
      + constructor. now econstructor.
      + apply eta_step. now apply case_eta_brs.
      + apply upto_domain_refl.
  Qed.

End FourCases.
