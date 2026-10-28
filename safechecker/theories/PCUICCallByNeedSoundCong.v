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

(** * BET-298 step 2c: the PCUIC congruences the call-by-need comparison needs

  The call-by-need comparison of [PCUICCallByNeed] ([conv_term], [conv_same_code],
  [case_cong], [conv_value], [conv_rows]) answers "convertible" in three ways: the two
  sides are the *same code* under two environments whose slots are pairwise convertible;
  the two values have the same head and pairwise convertible arguments; or a stuck
  [tCase]/[tProj] has convertible scrutinees, parameters, return clauses and branches.

  This file holds the facts about [Σ ;;; Γ ⊢ t ≤[le] u] ([ws_cumul_pb], the well-scoped
  cumulativity of [PCUICWellScopedCumulativity]) that each of those answers needs. It
  speaks only of [PCUICAst] terms and MetaRocq's own cumulativity: no machine structure
  appears in any statement, so it is independent of the machine theorem. The one machine
  definition it mentions is [case_ctx_ok] (a predicate on two [context]s), for which it
  proves the reflection the stuck-match row needs.

  Where MetaRocq already has the fact, this file names it and restates it in the shape the
  comparison uses; where it does not, the fact is proved here. The header of each section
  says which is which. Every hypothesis in these statements is one the comparison proof has
  to discharge; §1 says exactly what the "closed enough" hypothesis of the same-code rule
  is, in terms of a bound on the free variables of the code and the length of the slot
  list. *)

(** ** A context of fresh assumptions

  The reading of a suspension is [subst ts 0 (lift N m t)] with [#|ts| = m] ([rb_susp]).
  To use MetaRocq's substitution lemma we need a context for the substitution to be an
  [untyped_subslet] of. Nothing about that context matters except that it is made of [m]
  assumptions and is closed, so we take [m] copies of one closed assumption. *)

Definition fresh_decl : context_decl :=
  vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort Sort.type0).

Fixpoint fresh_context (n : nat) : context :=
  match n with
  | 0 => []
  | S n => fresh_context n ,, fresh_decl
  end.

Lemma fresh_context_length n : #|fresh_context n| = n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|]. now rewrite IH.
Qed.

Lemma fresh_context_assumption_context n : assumption_context (fresh_context n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor.
  - constructor. exact IH.
Qed.

Lemma fresh_context_on_free_vars P n : on_free_vars_ctx P (fresh_context n).
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite on_free_vars_ctx_snoc IH /=. reflexivity.
Qed.

Lemma untyped_subslet_fresh_context Γ s : untyped_subslet Γ s (fresh_context #|s|).
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
    [m = #|ts| = nvals] ([rb_susp] of [PCUICCallByNeed]), so the rule is sound as soon as
    substituting two pairwise convertible lists in one term gives convertible results. *)

  (** The general form: the lifted code must be an open term of [Γ] extended by [#|ts1|]
    assumptions, which is exactly "its free variables are the [#|ts1|] slots and the
    variables of [Γ]". *)
  Lemma ws_cumul_pb_subst_open {pb Γ ts1 ts2 b} :
    is_closed_context Γ ->
    ws_cumul_pb_terms Σ Γ ts1 ts2 ->
    is_open_term (Γ ,,, fresh_context #|ts1|) b ->
    Σ ;;; Γ ⊢ subst ts1 0 b ≤[pb] subst ts2 0 b.
  Proof using wfΣ.
    intros clΓ eqs opb.
    apply ws_cumul_eq_pb.
    assert (cl1 : is_closed_context (Γ ,,, fresh_context #|ts1|)).
    { rewrite on_free_vars_ctx_app clΓ /=. apply fresh_context_on_free_vars. }
    assert (cl2 : is_closed_context (Γ ,,, fresh_context #|ts2|)).
    { rewrite on_free_vars_ctx_app clΓ /=. apply fresh_context_on_free_vars. }
    exact (untyped_substitution_ws_cumul_pb_subst_conv (Γ' := []) eqs cl1 cl2
             (untyped_subslet_fresh_context Γ ts1) (untyped_subslet_fresh_context Γ ts2) opb).
  Qed.

  (** The form the machine can supply. [N] is the shift [lvl - nctx + goff] and [m] the
    number of slots [nvals]; the context [Γ] is the one that holds at level [lvl], so
    [#|Γ| = lvl]. The closedness hypothesis is a bound on the free variables of the code's
    own term: every free variable of [t] is below [m + (#|Γ| - N)], which for the top-level
    call ([m = 0], [N = 0]) is "closed in [Γ]", and under one pushed binder ([m = 1],
    [N = 1], [#|Γ| = nctx + 1]) is "closed in [Γ]" again. *)
  Lemma ws_cumul_pb_subst_lift {pb Γ ts1 ts2 N m t} :
    is_closed_context Γ ->
    ws_cumul_pb_terms Σ Γ ts1 ts2 ->
    #|ts1| = m ->
    N <= #|Γ| ->
    on_free_vars (shiftnP (m + (#|Γ| - N)) xpred0) t ->
    Σ ;;; Γ ⊢ subst ts1 0 (lift N m t) ≤[pb] subst ts2 0 (lift N m t).
  Proof using wfΣ.
    intros clΓ eqs hm hN ont.
    eapply ws_cumul_pb_subst_open; tea.
    rewrite hm app_context_length fresh_context_length.
    assert (h : on_free_vars (strengthenP m N (shiftnP (m + (#|Γ| - N)) xpred0)) (lift N m t)).
    { now rewrite on_free_vars_lift. }
    eapply on_free_vars_impl; [|exact h].
    intros i. unfold strengthenP, shiftnP; cbv beta.
    destruct (Nat.ltb_spec i m) as [hi|hi].
    - intros _. destruct (Nat.ltb_spec i (m + #|Γ|)) as [|hle]; [reflexivity|].
      exfalso; lia.
    - destruct (Nat.ltb_spec i (m + N)) as [h2|h2]; [intros hf; discriminate hf|].
      destruct (Nat.ltb_spec (i - N) (m + (#|Γ| - N))) as [h3|h3];
        [|simpl; intros hf; discriminate hf].
      intros _. destruct (Nat.ltb_spec i (m + #|Γ|)) as [|hle]; [reflexivity|].
      exfalso; lia.
  Qed.

  (** A whole slot list is convertible with itself; the "same address" row of the rule
    table is this plus reflexivity. *)
  Lemma ws_cumul_pb_terms_refl {Γ l} :
    is_closed_context Γ -> forallb (is_open_term Γ) l -> ws_cumul_pb_terms Σ Γ l l.
  Proof using wfΣ.
    intros clΓ. induction l as [|t l IH]; simpl.
    - intros _. constructor.
    - move=> /andP[] ot ol. constructor; [|now apply IH].
      now apply ws_cumul_pb_refl.
  Qed.

  (** ** 2. Spine congruence

    [ws_cumul_pb_mkApps] is MetaRocq's own (pcuic/theories/PCUICConversion.v:1672); it is
    the rule for a head that is already convertible. [ws_cumul_pb_Ind] (:3851) and
    [ws_cumul_pb_Construct] (:3875) are MetaRocq's rules for an inductive or constructor
    head compared with variance at [napp = #|args|]. The machine, however, compares heads
    with [cmp_term pb #|sp|], a *syntactic* test at [napp] = the spine length, for every
    head shape; [ws_cumul_pb_mkApps_napp] below is that rule, proved here. *)

  Lemma ws_cumul_pb_spine {pb Γ hd hd' args args'} :
    Σ ;;; Γ ⊢ hd ≤[pb] hd' ->
    ws_cumul_pb_terms Σ Γ args args' ->
    Σ ;;; Γ ⊢ mkApps hd args ≤[pb] mkApps hd' args'.
  Proof using wfΣ.
    intros h hargs. now eapply ws_cumul_pb_mkApps.
  Qed.

  Lemma ws_cumul_pb_mkApps_napp {pb Γ hd hd' args args'} :
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

  (** ** 3. Case and projection congruence

    [ws_cumul_pb_Case] is MetaRocq's own (PCUICConversion.v:2324) and
    [ws_cumul_pb_Proj_c] (:1905). [ws_cumul_pb_tCase] below is the same rule with its
    [ws_cumul_pb_predicate] and [ws_cumul_pb_brs] hypotheses spelled out component by
    component, and with the openness hypothesis in the form the machine has it (openness of
    the whole [tCase] term, which is what the state invariant carries). *)

  Lemma is_open_case_tCase {Γ ci p c brs} :
    is_open_term Γ (tCase ci p c brs) -> is_open_case Γ p c brs.
  Proof using Type. intros h. exact h. Qed.

  Lemma ws_cumul_pb_tCase {pb Γ ci p p' c c' brs brs'} :
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

  Lemma ws_cumul_pb_tProj {pb Γ pr c c'} :
    Σ ;;; Γ ⊢ c = c' ->
    Σ ;;; Γ ⊢ tProj pr c ≤[pb] tProj pr c'.
  Proof using wfΣ.
    intros h. now eapply ws_cumul_pb_Proj_c.
  Qed.

  (** ** 4. Syntactic equality

    The test the machine runs before anything else ([eqb_term_upto_univ_napp] at [napp = 0],
    from [PCUICEqualityDec]). The first lemma is MetaRocq's constructor [ws_cumul_pb_compare]
    read as a rule; the second adds the reflection, with exactly the hypotheses of
    [reflect_eq_term_upto_univ] (PCUICEqualityDec.v:452) — these are the ones the hook's
    existing fast path discharges through [cmpb_term_correct]. *)

  Lemma ws_cumul_pb_compare_term {pb Γ t u} :
    is_closed_context Γ ->
    is_open_term Γ t ->
    is_open_term Γ u ->
    compare_term Σ Σ pb t u ->
    Σ ;;; Γ ⊢ t ≤[pb] u.
  Proof using Type. intros; now constructor. Qed.

  Lemma ws_cumul_pb_eqb_term_upto_univ
    {pb Γ t u} {p : Universe.t -> bool} {q : nat -> term -> bool}
    {cmpu : conv_pb -> Universe.t -> Universe.t -> bool}
    {cmps : conv_pb -> sort -> sort -> bool}
    {gen : conv_pb -> global_reference -> nat -> list Level.t -> list Level.t -> bool} :
    (forall u u', p u -> p u' -> reflect (compare_universe Σ Conv u u') (cmpu Conv u u')) ->
    (forall u u', p u -> p u' -> reflect (compare_universe Σ pb u u') (cmpu pb u u')) ->
    (forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' ->
                  reflect (compare_sort Σ Conv s s') (cmps Conv s s')) ->
    (forall s s', Sort.on_sort p true s -> Sort.on_sort p true s' ->
                  reflect (compare_sort Σ pb s s') (cmps pb s s')) ->
    (forall gr napp ui ui',
        forallb p (map Universe.make' ui) -> forallb p (map Universe.make' ui') ->
        reflect (cmp_global_instance Σ (compare_universe Σ) Conv gr napp ui ui')
          (gen Conv gr napp ui ui')) ->
    (forall gr napp ui ui',
        forallb p (map Universe.make' ui) -> forallb p (map Universe.make' ui') ->
        reflect (cmp_global_instance Σ (compare_universe Σ) pb gr napp ui ui')
          (gen pb gr napp ui ui')) ->
    on_universes p q t ->
    on_universes p q u ->
    is_closed_context Γ ->
    is_open_term Γ t ->
    is_open_term Γ u ->
    eqb_term_upto_univ_napp cmpu cmps gen pb 0 t u ->
    Σ ;;; Γ ⊢ t ≤[pb] u.
  Proof using Type.
    intros h1 h2 h3 h4 h5 h6 wt wu clΓ opt opu heq.
    constructor; tea.
    unfold compare_term.
    destruct (reflect_eq_term_upto_univ _ p q cmpu cmps _ _ gen pb 0
                h1 h2 h3 h4 h5 h6 t u wt wu) as [he|he].
    - exact he.
    - discriminate heq.
  Qed.

  (** ** 5. Reflexivity and transitivity in the shape the comparison uses

    [ws_cumul_pb_refl] and the [Transitive] instance are MetaRocq's
    (PCUICWellScopedCumulativity.v:319 and :178), as are [red_ws_cumul_pb_left] (:338) and
    [red_ws_cumul_pb_right] (:346). [ws_cumul_pb_closed_red] packs the last two into the
    one step every row of the comparison takes: the evaluator reduces both sides to the
    terms the two values read back to, and a congruence compares those. *)

  Lemma ws_cumul_pb_refl_open {pb Γ t} :
    is_closed_context Γ -> is_open_term Γ t -> Σ ;;; Γ ⊢ t ≤[pb] t.
  Proof using Type. apply ws_cumul_pb_refl. Qed.

  Lemma ws_cumul_pb_trans' {pb Γ t u v} :
    Σ ;;; Γ ⊢ t ≤[pb] u -> Σ ;;; Γ ⊢ u ≤[pb] v -> Σ ;;; Γ ⊢ t ≤[pb] v.
  Proof using wfΣ. intros h1 h2. etransitivity; tea. Qed.

  Lemma ws_cumul_pb_conv_trans_l {pb Γ t u v} :
    Σ ;;; Γ ⊢ t = u -> Σ ;;; Γ ⊢ u ≤[pb] v -> Σ ;;; Γ ⊢ t ≤[pb] v.
  Proof using wfΣ.
    intros h1 h2. etransitivity; [|exact h2]. now apply ws_cumul_eq_pb.
  Qed.

  Lemma ws_cumul_pb_conv_trans_r {pb Γ t u v} :
    Σ ;;; Γ ⊢ t ≤[pb] u -> Σ ;;; Γ ⊢ u = v -> Σ ;;; Γ ⊢ t ≤[pb] v.
  Proof using wfΣ.
    intros h1 h2. etransitivity; [exact h1|]. now apply ws_cumul_eq_pb.
  Qed.

  Lemma ws_cumul_pb_closed_red {pb Γ t t' u u'} :
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

(** ** The branch contexts the machine checks with [case_ctx_ok]

  [case_ctx_ok ctx1 ctx2] (PCUICCallByNeed.v:2786) is the machine's run-time check on the
  [pcontext]s and [bcontext]s of a stuck match: both are let-free and they are equal up to
  names. These are the two facts [ws_cumul_pb_Case] and the read-back of a branch body ask
  for; the machine gives up on any context with a let-in, so there is nothing weaker to
  prove here. *)

Lemma case_ctx_ok_eqb_context ctx1 ctx2 :
  case_ctx_ok ctx1 ctx2 -> eqb_context_upto_names ctx1 ctx2.
Proof.
  unfold case_ctx_ok.
  induction ctx1 as [|d1 ctx1 IH] in ctx2 |- *; destruct ctx2 as [|d2 ctx2]; simpl.
  - intros _. reflexivity.
  - intros h. discriminate h.
  - intros h. discriminate h.
  - move=> /andP[] /andP[] /andP[] _ _ -> /= h. now apply IH.
Qed.

Lemma case_ctx_ok_spec ctx1 ctx2 :
  case_ctx_ok ctx1 ctx2 ->
  [× eq_context_upto_names ctx1 ctx2,
     assumption_context ctx1 & assumption_context ctx2].
Proof.
  unfold case_ctx_ok.
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

Lemma assumption_context_map_context f ctx :
  assumption_context ctx -> assumption_context (map_context f ctx).
Proof.
  induction 1; simpl.
  - constructor.
  - constructor. assumption.
Qed.

Lemma assumption_context_inst_case_context pars u ctx :
  assumption_context ctx -> assumption_context (inst_case_context pars u ctx).
Proof.
  intros h. unfold inst_case_context.
  apply assumption_context_fold.
  change (subst_instance u ctx) with (map_context (subst_instance u) ctx).
  now apply assumption_context_map_context.
Qed.

Lemma assumption_context_inst_case_branch_context p br :
  assumption_context br.(bcontext) ->
  assumption_context (inst_case_branch_context p br).
Proof.
  intros h. unfold inst_case_branch_context.
  now apply assumption_context_inst_case_context.
Qed.

Lemma assumption_context_inst_case_predicate_context p :
  assumption_context p.(pcontext) ->
  assumption_context (inst_case_predicate_context p).
Proof.
  intros h. unfold inst_case_predicate_context.
  now apply assumption_context_inst_case_context.
Qed.
