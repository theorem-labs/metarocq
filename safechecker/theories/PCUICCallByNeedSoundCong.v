(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses CMorphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst
     PCUICTyping PCUICEquality PCUICCumulativity PCUICOnFreeVars PCUICClosed
     PCUICSubstitution PCUICContexts PCUICWfUniverses
     PCUICWellScopedCumulativity PCUICConversion.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICCallByNeed.

Set Default Goal Selector "1".

(** * The PCUIC congruences the call-by-need comparison needs

  The call-by-need comparison of [PCUICCallByNeed] ([cbn_conv_term], [cbn_conv_same_code],
  [cbn_case_cong], [cbn_conv_value], [cbn_conv_rows]) answers "convertible" in three ways: the two
  sides are the *same code* under two environments whose slots are pairwise convertible;
  the two values have the same head and pairwise convertible arguments; or a stuck
  [tCase]/[tProj] has convertible scrutinees, parameters, return clauses and branches.

  This file holds the facts about [Σ ;;; Γ ⊢ t ≤[le] u] ([ws_cumul_pb], the well-scoped
  cumulativity of [PCUICWellScopedCumulativity]) that each of those answers needs. It
  speaks only of [PCUICAst] terms and MetaRocq's own cumulativity: no machine structure
  appears in any statement, so it is independent of the machine theorem. The one machine
  definition it mentions is [cbn_case_ctx_ok] (a predicate on two [context]s), for which it
  proves the reflection the stuck-match row needs.

  Where MetaRocq already has the fact, this file names it and restates it in the shape the
  comparison uses; where it does not, the fact is proved here. The header of each section
  says which is which. Every hypothesis in these statements is one the comparison proof has
  to discharge; §1 says exactly what the "closed enough" hypothesis of the same-code rule
  is, in terms of a bound on the free variables of the code and the length of the slot
  list. *)

(** ** A context of fresh assumptions

  The reading of a suspension is [subst ts 0 (lift N m t)] with [#|ts| = m] ([cbn_rb_susp]).
  To use MetaRocq's substitution lemma we need a context for the substitution to be an
  [untyped_subslet] of. Nothing about that context matters except that it is made of [m]
  assumptions and is closed, so we take [m] copies of one closed assumption. *)

Definition cbn_fresh_decl : context_decl :=
  vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort Sort.type0).

Fixpoint cbn_fresh_context (n : nat) : context :=
  match n with
  | 0 => []
  | S n => cbn_fresh_context n ,, cbn_fresh_decl
  end.

Lemma cbn_fresh_context_length n : #|cbn_fresh_context n| = n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|]. now rewrite IH.
Qed.

Lemma cbn_fresh_context_on_free_vars P n : on_free_vars_ctx P (cbn_fresh_context n).
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite on_free_vars_ctx_snoc IH /=. reflexivity.
Qed.

Lemma cbn_untyped_subslet_fresh_context Γ s : untyped_subslet Γ s (cbn_fresh_context #|s|).
Proof.
  induction s as [|t s IH]; simpl.
  - constructor.
  - constructor. exact IH.
Qed.

Section Congruence.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext} {wfΣ : wf Σ}.

  (** ** 1. Substitution congruence (proved here)

    The same-code rule compares two suspensions of *one* code under two environments. The
    reading of a suspension is [subst ts 0 (lift N m t)] with [N = lvl - nctx + goff] and
    [m = #|ts| = nvals] ([cbn_rb_susp] of [PCUICCallByNeed]), so the rule is sound as soon as
    substituting two pairwise convertible lists in one term gives convertible results. *)

  (** The general form: the lifted code must be an open term of [Γ] extended by [#|ts1|]
    assumptions, which is exactly "its free variables are the [#|ts1|] slots and the
    variables of [Γ]". *)
  Lemma cbn_ws_cumul_pb_subst_open {pb Γ ts1 ts2 b} :
    is_closed_context Γ ->
    ws_cumul_pb_terms Σ Γ ts1 ts2 ->
    is_open_term (Γ ,,, cbn_fresh_context #|ts1|) b ->
    Σ ;;; Γ ⊢ subst ts1 0 b ≤[pb] subst ts2 0 b.
  Proof using wfΣ.
    intros clΓ eqs opb.
    apply ws_cumul_eq_pb.
    assert (cl1 : is_closed_context (Γ ,,, cbn_fresh_context #|ts1|)).
    { rewrite on_free_vars_ctx_app clΓ /=. apply cbn_fresh_context_on_free_vars. }
    assert (cl2 : is_closed_context (Γ ,,, cbn_fresh_context #|ts2|)).
    { rewrite on_free_vars_ctx_app clΓ /=. apply cbn_fresh_context_on_free_vars. }
    exact (untyped_substitution_ws_cumul_pb_subst_conv (Γ' := []) eqs cl1 cl2
             (cbn_untyped_subslet_fresh_context Γ ts1)
               (cbn_untyped_subslet_fresh_context Γ ts2) opb).
  Qed.

  (** ** 2. Spine congruence

    [PCUICConversion.ws_cumul_pb_mkApps] is MetaRocq's rule for a head that is already
    convertible. [ws_cumul_pb_Ind] and [ws_cumul_pb_Construct] are MetaRocq's rules for an
    inductive or constructor head compared with variance at [napp = #|args|]. The machine,
    however, compares heads with [cbn_cmp_term pb #|sp|], a *syntactic* test at [napp] = the
    spine length, for every head shape; [cbn_ws_cumul_pb_mkApps_napp] below is that rule,
    proved here. *)

  Lemma cbn_ws_cumul_pb_mkApps_napp {pb Γ hd hd' args args'} :
    is_closed_context Γ ->
    is_open_term Γ hd ->
    is_open_term Γ hd' ->
    compare_term_napp Σ Σ pb #|args| hd hd' ->
    ws_cumul_pb_terms Σ Γ args args' ->
    Σ ;;; Γ ⊢ mkApps hd args ≤[pb] mkApps hd' args'.
  Proof using wfΣ.
    intros clΓ oh oh' cmp eqs.
    assert (oargs : forallb (is_open_term Γ) args).
    { now eapply ws_cumul_pb_terms_open_terms_left. }
    etransitivity.
    - instantiate (1 := mkApps hd' args).
      constructor.
      + exact clΓ.
      + rewrite on_free_vars_mkApps oh oargs //.
      + rewrite on_free_vars_mkApps oh' oargs //.
      + apply eq_term_upto_univ_mkApps; [exact cmp|].
        apply All2_refl. intros x. reflexivity.
    - apply ws_cumul_eq_pb. eapply ws_cumul_pb_mkApps; [|exact eqs].
      apply ws_cumul_pb_refl; tea.
  Qed.

  (** ** 3. Case congruence

    [PCUICConversion.ws_cumul_pb_Case] is MetaRocq's own. [cbn_ws_cumul_pb_tCase] below is the
    same rule with its [ws_cumul_pb_predicate] and [ws_cumul_pb_brs] hypotheses spelled out
    component by component, and with the openness hypothesis in the form the machine has it
    (openness of the whole [tCase] term, which is what the state invariant carries). *)

  Lemma cbn_ws_cumul_pb_tCase {pb Γ ci p p' c c' brs brs'} :
    is_open_term Γ (tCase ci p c brs) ->
    is_open_term Γ (tCase ci p' c' brs') ->
    ws_cumul_pb_terms Σ Γ p.(pparams) p'.(pparams) ->
    cmp_universe_instance (eq_universe Σ) p.(puinst) p'.(puinst) ->
    eq_context_upto_names p.(pcontext) p'.(pcontext) ->
    Σ ;;; Γ ,,, inst_case_predicate_context p ⊢ p.(preturn) = p'.(preturn) ->
    Σ ;;; Γ ⊢ c = c' ->
    All2 (fun br br' =>
            eq_context_upto_names br.(bcontext) br'.(bcontext) ×
            Σ ;;; Γ ,,, inst_case_branch_context p br ⊢ br.(bbody) = br'.(bbody)) brs brs' ->
    Σ ;;; Γ ⊢ tCase ci p c brs ≤[pb] tCase ci p' c' brs'.
  Proof using wfΣ.
    intros on on' hpars hinst hctx hret hc hbrs.
    apply ws_cumul_eq_pb.
    eapply ws_cumul_pb_Case.
    5: exact hbrs.
    1: exact on.
    1: exact on'.
    2: exact hc.
    split; assumption.
  Qed.

  (** ** 4. Syntactic equality

    The test the machine runs before anything else ([eqb_term_upto_univ_napp] at [napp = 0],
    from [PCUICEqualityDec]). [cbn_ws_cumul_pb_compare_term] is MetaRocq's constructor
    [ws_cumul_pb_compare] read as a rule. *)

  Lemma cbn_ws_cumul_pb_compare_term {pb Γ t u} :
    is_closed_context Γ ->
    is_open_term Γ t ->
    is_open_term Γ u ->
    compare_term Σ Σ pb t u ->
    Σ ;;; Γ ⊢ t ≤[pb] u.
  Proof using Type. intros; now constructor. Qed.

  (** ** 5. Transitivity in the shape the comparison uses

    The [Transitive] instance of [ws_cumul_pb], [red_ws_cumul_pb_left] and
    [red_ws_cumul_pb_right] are MetaRocq's ([PCUICWellScopedCumulativity]).
    [cbn_ws_cumul_pb_closed_red] packs the last two into the one step every row of the
    comparison takes: the evaluator reduces both sides to the terms the two values read
    back to, and a congruence compares those. *)

  Lemma cbn_ws_cumul_pb_conv_trans_r {pb Γ t u v} :
    Σ ;;; Γ ⊢ t ≤[pb] u -> Σ ;;; Γ ⊢ u = v -> Σ ;;; Γ ⊢ t ≤[pb] v.
  Proof using wfΣ.
    intros h1 h2. etransitivity; [exact h1|]. now apply ws_cumul_eq_pb.
  Qed.

  Lemma cbn_ws_cumul_pb_closed_red {pb Γ t t' u u'} :
    Σ ;;; Γ ⊢ t ⇝ t' ->
    Σ ;;; Γ ⊢ u ⇝ u' ->
    Σ ;;; Γ ⊢ t' ≤[pb] u' ->
    Σ ;;; Γ ⊢ t ≤[pb] u.
  Proof using wfΣ.
    intros rt ru h.
    eapply red_ws_cumul_pb_left; [exact rt|].
    eapply red_ws_cumul_pb_right; [exact ru|exact h].
  Qed.

End Congruence.

(** ** The branch contexts the machine checks with [cbn_case_ctx_ok]

  [PCUICCallByNeed.cbn_case_ctx_ok ctx1 ctx2] is the machine's run-time check on the
  [pcontext]s and [bcontext]s of a stuck match: both are let-free and they are equal up to
  names. These are the two facts [ws_cumul_pb_Case] and the read-back of a branch body ask
  for; the machine gives up on any context with a let-in, so there is nothing weaker to
  prove here. *)

Lemma cbn_case_ctx_ok_spec ctx1 ctx2 :
  cbn_case_ctx_ok ctx1 ctx2 ->
  [× eq_context_upto_names ctx1 ctx2,
     assumption_context ctx1 & assumption_context ctx2].
Proof.
  unfold cbn_case_ctx_ok.
  induction ctx1 as [|d1 ctx1 IH] in ctx2 |- *; destruct ctx2 as [|d2 ctx2]; simpl.
  - intros _. split; constructor.
  - intros h. discriminate h.
  - intros h. discriminate h.
  - move=> /andP[] /andP[] /andP[] ha1 ha2 heq hrest.
    destruct (IH _ hrest) as [he a1 a2].
    destruct d1 as [na1 [b1|] ty1]; simpl in ha1; [discriminate ha1|].
    destruct d2 as [na2 [b2|] ty2]; simpl in ha2; [discriminate ha2|].
    move: heq.
    destruct (reflect_eq_decl_upto_names
                {| decl_name := na1; decl_body := None; decl_type := ty1 |}
                {| decl_name := na2; decl_body := None; decl_type := ty2 |}) as [hd|hd].
    + intros _. split; constructor; assumption.
    + intros hf. discriminate hf.
Qed.
