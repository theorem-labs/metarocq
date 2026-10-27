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
     PCUICOnFreeVarsConv PCUICClosedTyp BDStrengthening.

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
