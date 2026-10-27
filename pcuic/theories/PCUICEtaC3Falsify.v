(* Distributed under the terms of the MIT license. *)

(** * C3 falsification: the 9.2 [tCase] reduction rows

  C3Falsifier, BET-315 eta lane. This file is a FALSIFICATION TEST, not a proof of C3.

  C3 (plan §3, row C3):
    [red1 Σ Γ t v -> eta1 t u ->
     ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'].

  The lane lead's question (2026-10-27): the 9.2 [tCase] reduction rows —
  [case_red_param], [case_red_return], [case_red_brs] and [red_iota] — are the only
  places in 9.2 where a reduction's CONTEXT is computed from the term being reduced
  ([inst_case_predicate_context p], [inst_case_branch_context p br]), or where the
  predicate's parameters are substituted into a context and then [expand_lets]-ed
  ([iota_red]). So an η step in [pparams] moves the context in which the other side's
  step must be replayed. If any of those squares cannot be closed inside C3's budget,
  that is the counterexample the lane needs. They are all closed below.

  Method. Each row is stated as its own square: the premises of that [red1]
  constructor, an arbitrary [eta1] step on the same term, and the C3 conclusion. The
  induction hypothesis is assumed in its STRONGEST form (full C3, [IH] below). That
  is sound for a feasibility test — if a square cannot close even with the strongest
  IH, the obstruction is real — but it is NOT a proof of C3, and nothing here is
  reported as proving C3. No [Admitted], no [Axiom]: every square below is closed
  from the Section hypotheses.

  [eta1] and [upto_domain] are the lane's shared definitions, [PCUICEtaDefs.v]
  (C3Prover1, fork branch wip/eta-c3-defs-2026-10-27), not retyped here. The
  context-move lemma [red1_eta_ctx_strong] and [eta_ctx] are now L2's REAL GREEN
  lemmas from [PCUICEtaConfluence.v] (frac/eta-l2 @ e05415aa), DISCHARGED here (see
  [red1_eta_ctx_le]), not assumed; the remaining U-row closures stay as [Context]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICPrimitive
     PCUICCases PCUICClosed PCUICTactics PCUICEquality PCUICReduction
     PCUICEtaDefs PCUICEtaConfluence.

Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope type_scope.

(** ** The two legs of C3, and the square *)

Notation eta_rt := (clos_refl_trans eta1).
Notation eta_rt_l := (clos_refl_trans (OnOne2 eta1)).

Definition red_le Σ Γ := clos_refl (red1 Σ Γ).

(** [joinable Σ Γ u v]: [u] is the η-reduct (at most one β/ι step allowed from it),
    [v] is the β-reduct (η steps only from it). *)
Definition joinable {cf:checker_flags} (Σ : global_env) (Γ : context) (u v : term) : Type :=
  ∑ w w', red_le Σ Γ u w × eta_rt v w' × upto_domain w w'.

Definition C3 {cf:checker_flags} (Σ : global_env) : Type :=
  forall Γ t u v, red1 Σ Γ t v -> eta1 t u -> joinable Σ Γ u v.

(** ** η on contexts.
    [eta_ctx] and [red1_eta_ctx_strong] are now the REAL lemmas from
    [PCUICEtaConfluence.v] (L2, frac/eta-l2 @ e05415aa), not a local hypothesis:
    [eta_ctx := All2 (All_decls eta)], and
    [red1_eta_ctx_strong : red1 Σ Γ t u -> eta_ctx Γ Δ -> ∑ u', red1 Σ Δ t u' × eta u u'].
    [eta] there is [clos_refl_trans eta1] = our [eta_rt]. *)

Section Falsify.
  Context {cf : checker_flags} (Σ : global_env).

  (** *** Assumed lemmas. Every one is listed in the report. *)

  (** U1 (equivalence): reflexivity of the two syntactic comparisons. *)
  Context (upto_domain_refl : forall t, upto_domain t t).
  Context (eq_context_upto_names_refl : forall Δ : context, eq_context_upto_names Δ Δ).

  (** U3/U4 (syntactic inversion), = upstream [eta1_mkApps_inv]
      ([origin/eta_postpo:PCUICEtaReduction.v:1223-1225], PROVED there). *)
  Context (eta1_mkApps_inv : forall M l N, eta1 (mkApps M l) N ->
             (∑ M', eta1 M M' × (N = mkApps M' l)) +
             (∑ l', OnOne2 eta1 l l' × (N = mkApps M l'))).

  (** U2 (η closure under substitution): an η step inside the substitution list. *)
  Context (eta_rt_subst_list : forall s s' k b, OnOne2 eta1 s s' ->
             eta_rt (subst s k b) (subst s' k b)).
  (** U2: an η step inside the substituted term. *)
  Context (eta_rt_subst_term : forall s k b b', eta_rt b b' ->
             eta_rt (subst s k b) (subst s k b')).

  (** U2, context form, stated on [inst_case_context] (the only shape the [tCase]
      rows need): an η step in one parameter moves the instantiated case context
      declaration-wise by η-star. *)
  Context (eta_ctx_inst_case_context : forall params params' u pctx,
             OnOne2 eta1 params params' ->
             eta_ctx (inst_case_context params u pctx)
                     (inst_case_context params' u pctx)).

  (** U2, [expand_lets] form: declaration-wise η-star contexts give η-star-related
      [expand_lets], and the shape data a reduction premise reads is equal. *)
  Context (eta_rt_expand_lets : forall Δ Δ' b, eta_ctx Δ Δ' ->
             eta_rt (expand_lets Δ b) (expand_lets Δ' b)).
  Context (eta_rt_expand_lets_body : forall Δ b b', eta_rt b b' ->
             eta_rt (expand_lets Δ b) (expand_lets Δ b')).
  Context (eta_ctx_assumptions : forall Δ Δ', eta_ctx Δ Δ' ->
             context_assumptions Δ = context_assumptions Δ').

  (** The induction hypothesis, in its strongest form (see the header). *)
  Context (IH : C3 Σ).

  (** *** Plumbing *)

  (** The C3-budget context-move lemma, now DERIVED from L2's real
      [red1_eta_ctx_strong] (red1 + eta) by weakening its red1 to [red_le]. *)
  Lemma red1_eta_ctx_le Γ Δ t u :
    eta_ctx Γ Δ -> red1 Σ Γ t u -> ∑ u', red_le Σ Δ t u' × eta_rt u u'.
  Proof.
    intros hc hr.
    destruct (red1_eta_ctx_strong Σ Γ Δ t u hr hc) as [u' [hstep heta]].
    exists u'. split; [now constructor|exact heta].
  Qed.

  (** left-fixed prepend (the imported [eta_ctx_app] appends on the other side). *)
  Lemma eta_ctx_prepend Γ Δ Δ' : eta_ctx Δ Δ' -> eta_ctx (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    intro h. unfold app_context. apply All2_app; tas. apply eta_ctx_refl.
  Qed.

  Lemma eta_rt_one t u : eta1 t u -> eta_rt t u.
  Proof. intro h. now apply rt_step. Qed.

  Lemma red_le_one Γ t u : red1 Σ Γ t u -> red_le Σ Γ t u.
  Proof. intro h. now constructor. Qed.

  Lemma red_le_refl Γ t : red_le Σ Γ t t.
  Proof. now constructor. Qed.

  Lemma All2_upto_domain_refl l : All2 upto_domain l l.
  Proof. apply All2_refl. intro; apply upto_domain_refl. Qed.

  Lemma All2_branch_refl (brs : list (branch term)) :
    All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                     × upto_domain x.(bbody) y.(bbody)) brs brs.
  Proof.
    apply All2_refl. intro. split.
    - apply eq_context_upto_names_refl.
    - apply upto_domain_refl.
  Qed.

  (** *** η-star congruences for [tCase] *)

  Lemma eta_rt_case_param ci p c brs l l' :
    eta_rt_l l l' ->
    eta_rt (tCase ci (set_pparams p l) c brs) (tCase ci (set_pparams p l') c brs).
  Proof.
    induction 1 as [x y h|x|x y z h1 ih1 h2 ih2].
    - apply rt_step. exact (case_eta_param ci (set_pparams p x) y c brs h).
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma eta_rt_case_return ci p c brs x y :
    eta_rt x y ->
    eta_rt (tCase ci (set_preturn p x) c brs) (tCase ci (set_preturn p y) c brs).
  Proof.
    induction 1 as [a b h|a|a b d h1 ih1 h2 ih2].
    - apply rt_step. exact (case_eta_return ci (set_preturn p a) b c brs h).
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma eta_rt_case_discr ci p brs x y :
    eta_rt x y -> eta_rt (tCase ci p x brs) (tCase ci p y brs).
  Proof.
    induction 1 as [a b h|a|a b d h1 ih1 h2 ih2].
    - apply rt_step. exact (case_eta_discr ci p a b brs h).
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma eta_rt_case_brs ci p c brs brs' :
    clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext)) brs brs' ->
    eta_rt (tCase ci p c brs) (tCase ci p c brs').
  Proof.
    induction 1 as [a b h|a|a b d h1 ih1 h2 ih2].
    - apply rt_step. exact (case_eta_brs ci p c a b h).
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  (** Lifting an η-star step at one list position. *)
  Lemma eta_rt_l_hd x y (tl : list term) : eta_rt x y -> eta_rt_l (x :: tl) (y :: tl).
  Proof.
    induction 1 as [a b h|a|a b d h1 ih1 h2 ih2].
    - apply rt_step. now constructor.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma eta_rt_l_one l l' : OnOne2 eta1 l l' -> eta_rt_l l l'.
  Proof. intro h. now apply rt_step. Qed.

  Lemma eta_rt_brs_hd (hd hd' : branch term) tl :
    hd.(bcontext) = hd'.(bcontext) -> eta_rt hd.(bbody) hd'.(bbody) ->
    clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext)) (hd :: tl) (hd' :: tl).
  Proof.
    intros hc hb. revert hd hd' hc hb.
    assert (gen : forall b1 b2, eta_rt b1 b2 -> forall hd hd' : branch term,
               hd.(bcontext) = hd'.(bcontext) -> hd.(bbody) = b1 -> hd'.(bbody) = b2 ->
               clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext)) (hd :: tl) (hd' :: tl)).
    { intros b1 b2 h. induction h as [a b h|a|a b d h1 ih1 h2 ih2]; intros hd hd' hc e1 e2.
      - apply rt_step. constructor. split.
        + unfold on_Trel. rewrite e1 e2. exact h.
        + exact hc.
      - assert (hd = hd') as ->.
        { destruct hd, hd'; cbn in *; now subst. }
        apply rt_refl.
      - eapply rt_trans.
        + exact (ih1 hd {| bcontext := hd.(bcontext); bbody := b |} eq_refl e1 eq_refl).
        + exact (ih2 {| bcontext := hd.(bcontext); bbody := b |} hd' hc eq_refl e2). }
    intros hd hd' hc hb. exact (gen _ _ hb hd hd' hc eq_refl eq_refl). 
  Qed.

  (** *** [upto_domain] for two [tCase]s differing in one component *)

  Ltac utd_close :=
    first [ apply upto_domain_refl | apply eq_context_upto_names_refl
          | apply All2_branch_refl | apply All2_upto_domain_refl | reflexivity ].

  Lemma utd_case_params ci p c brs l l' :
    All2 upto_domain l l' ->
    upto_domain (tCase ci (set_pparams p l) c brs) (tCase ci (set_pparams p l') c brs).
  Proof. intro h. constructor; cbn; tas; utd_close. Qed.

  Lemma utd_case_return ci p c brs x y :
    upto_domain x y ->
    upto_domain (tCase ci (set_preturn p x) c brs) (tCase ci (set_preturn p y) c brs).
  Proof. intro h. constructor; cbn; tas; utd_close. Qed.

  Lemma utd_case_discr ci p brs x y :
    upto_domain x y -> upto_domain (tCase ci p x brs) (tCase ci p y brs).
  Proof. intro h. constructor; tas; utd_close. Qed.

  Lemma eta_rt_l_tl hd l l' : eta_rt_l l l' -> eta_rt_l (hd :: l) (hd :: l').
  Proof.
    induction 1 as [a b h|a|a b d h1 ih1 h2 ih2].
    - apply rt_step. now constructor.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  (** red_le (≤ 1 red1) congruences for [tCase], so the IH legs need no
      shared-variable [destruct]. *)
  Lemma red_le_case_param Γ ci p c brs l m :
    ((m = l) + OnOne2 (red1 Σ Γ) l m) ->
    red_le Σ Γ (tCase ci (set_pparams p l) c brs) (tCase ci (set_pparams p m) c brs).
  Proof.
    intros [->|h].
    - apply red_le_refl.
    - apply red_le_one. exact (case_red_param Σ Γ ci (set_pparams p l) m c brs h).
  Qed.

  Lemma red_le_case_return Γ ci p c brs x y :
    red_le Σ (Γ ,,, inst_case_predicate_context p) x y ->
    red_le Σ Γ (tCase ci (set_preturn p x) c brs) (tCase ci (set_preturn p y) c brs).
  Proof.
    intro h. destruct h as [z hs|].
    - apply red_le_one. exact (case_red_return Σ Γ ci (set_preturn p x) z c brs hs).
    - apply red_le_refl.
  Qed.

  Lemma red_le_case_discr Γ ci p brs x y :
    red_le Σ Γ x y -> red_le Σ Γ (tCase ci p x brs) (tCase ci p y brs).
  Proof.
    intro h. destruct h as [z hs|].
    - apply red_le_one. now apply case_red_discr.
    - apply red_le_refl.
  Qed.

  (** ** The list square: [OnOne2 red1] against [OnOne2 eta1] on the same list *)

  Lemma onone2_param_square Γ l l1 l2 :
    OnOne2 (red1 Σ Γ) l l1 -> OnOne2 eta1 l l2 ->
    ∑ m m', ((m = l2) + OnOne2 (red1 Σ Γ) l2 m)
          × eta_rt_l l1 m' × All2 upto_domain m m'.
  Proof.
    intro h. revert l2. induction h as [hd hd1 tl r|hd tl tl1 h ih];
      intros l2 he; depelim he.
    - (* both at the head *)
      destruct (IH Γ hd hd' hd1 r e) as [w [w' [hle [heta hu]]]].
      exists (w :: tl), (w' :: tl). repeat split.
      + destruct hle as [? hstep|].
        * right. now constructor.
        * left. reflexivity.
      + now apply eta_rt_l_hd.
      + constructor; tas. apply All2_upto_domain_refl.
    - (* red1 at the head, η in the tail *)
      exists (hd1 :: tl'), (hd1 :: tl'). repeat split.
      + right. now constructor.
      + apply eta_rt_l_one. now constructor.
      + apply All2_upto_domain_refl.
    - (* red1 in the tail, η at the head *)
      exists (hd' :: tl1), (hd' :: tl1). repeat split.
      + right. now constructor.
      + apply eta_rt_l_one. now constructor.
      + apply All2_upto_domain_refl.
    - (* both in the tail *)
      destruct (ih _ he) as [m [m' [hm [hm' hu]]]].
      exists (hd :: m), (hd :: m'). repeat split.
      + destruct hm as [->|hstep].
        * left. reflexivity.
        * right. now constructor.
      + now apply eta_rt_l_tl.
      + constructor; tas. apply upto_domain_refl.
  Qed.

  (** ** Row 1: [case_red_param] *)

  Lemma c3_case_red_param Γ ci p params' c brs (u : term) :
    OnOne2 (red1 Σ Γ) p.(pparams) params' ->
    eta1 (tCase ci p c brs) u ->
    joinable Σ Γ u (tCase ci (set_pparams p params') c brs).
  Proof.
    intros hr he. depelim he.
    - (* case_eta_param: both steps in pparams *)
      match goal with Ho : OnOne2 eta1 _ _ |- _ => rename Ho into ho end.
      destruct (onone2_param_square Γ _ _ _ hr ho) as [m [m' [hm [hm' hu]]]].
      exists (tCase ci (set_pparams p m) c brs), (tCase ci (set_pparams p m') c brs).
      repeat split.
      + exact (red_le_case_param Γ ci p c brs params'0 m hm).
      + now apply eta_rt_case_param.
      + now apply utd_case_params.
    - (* case_eta_return: disjoint *)
      match goal with Ho : eta1 _ _ |- _ => rename Ho into ho end.
      exists (tCase ci (set_pparams (set_preturn p preturn') params') c brs),
             (tCase ci (set_pparams (set_preturn p preturn') params') c brs).
      repeat split.
      + apply red_le_one. now apply case_red_param.
      + apply eta_rt_one.
        exact (case_eta_return ci (set_pparams p params') preturn' c brs ho).
      + apply upto_domain_refl.
    - (* case_eta_discr: disjoint *)
      exists (tCase ci (set_pparams p params') c' brs),
             (tCase ci (set_pparams p params') c' brs).
      repeat split.
      + apply red_le_one. now apply case_red_param.
      + apply eta_rt_one. now apply case_eta_discr.
      + apply upto_domain_refl.
    - (* case_eta_brs: disjoint *)
      exists (tCase ci (set_pparams p params') c brs'),
             (tCase ci (set_pparams p params') c brs').
      repeat split.
      + apply red_le_one. now apply case_red_param.
      + apply eta_rt_one. now apply case_eta_brs.
      + apply upto_domain_refl.
  Qed.

  (** ** Row 2: [case_red_return] — the context-moving row.

      This is the first of the two squares the lane lead singled out: the β step is
      taken in [Γ ,,, inst_case_predicate_context p], and the η step changes
      [pparams], hence changes that very context. It closes: [red1_eta_ctx_strong]
      replays the β step in the moved context with ONE [red1] (C3's η-leg budget),
      and the β-reduct pays with η steps only — one [case_eta_param] plus the η-star
      the moved context forces inside [preturn]. *)

  Lemma c3_case_red_return Γ ci p preturn' c brs (u : term) :
    red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
    eta1 (tCase ci p c brs) u ->
    joinable Σ Γ u (tCase ci (set_preturn p preturn') c brs).
  Proof.
    intros hr he. depelim he.
    - (* case_eta_param: the η step MOVES the β step's context *)
      match goal with Ho : OnOne2 eta1 _ _ |- _ => rename Ho into ho end.
      destruct (red1_eta_ctx_le (Γ ,,, inst_case_predicate_context p)
                  (Γ ,,, inst_case_predicate_context (set_pparams p params'))
                  _ _ (eta_ctx_prepend Γ _ _ (eta_ctx_inst_case_context _ _ _ _ ho)) hr)
        as [pr'' [hle heta]].
      exists (tCase ci (set_preturn (set_pparams p params') pr'') c brs),
             (tCase ci (set_preturn (set_pparams p params') pr'') c brs).
      repeat split; [| |apply upto_domain_refl].
      + (* η-leg: at most one red1, replayed in the moved context *)
        destruct hle as [? hstep|].
        * apply red_le_one. now apply case_red_return.
        * apply red_le_refl.
      + (* β-leg: η only *)
        eapply rt_trans.
        * exact (eta_rt_case_param ci (set_preturn p preturn') c brs
                   p.(pparams) params' (eta_rt_l_one _ _ ho)).
        * exact (eta_rt_case_return ci (set_pparams p params') c brs
                   preturn' pr'' heta).
    - (* case_eta_return: same position, IH at the SAME context
         ([inst_case_predicate_context] does not read [preturn]) *)
      match goal with Ho : eta1 _ _ |- _ => rename Ho into ho end.
      destruct (IH (Γ ,,, inst_case_predicate_context p) p.(preturn)
                   preturn'0 preturn' hr ho) as [w [w' [hle [heta hu]]]].
      exists (tCase ci (set_preturn p w) c brs), (tCase ci (set_preturn p w') c brs).
      repeat split.
      + exact (red_le_case_return Γ ci p c brs preturn'0 w hle).
      + now apply eta_rt_case_return.
      + now apply utd_case_return.
    - (* case_eta_discr: disjoint *)
      exists (tCase ci (set_preturn p preturn') c' brs),
             (tCase ci (set_preturn p preturn') c' brs).
      repeat split.
      + apply red_le_one. now apply case_red_return.
      + apply eta_rt_one. now apply case_eta_discr.
      + apply upto_domain_refl.
    - (* case_eta_brs: disjoint *)
      exists (tCase ci (set_preturn p preturn') c brs'),
             (tCase ci (set_preturn p preturn') c brs').
      repeat split.
      + apply red_le_one. now apply case_red_return.
      + apply eta_rt_one. now apply case_eta_brs.
      + apply upto_domain_refl.
  Qed.

  (** ** Row 3: [case_red_discr] *)

  Lemma c3_case_red_discr Γ ci p c c' brs (u : term) :
    red1 Σ Γ c c' ->
    eta1 (tCase ci p c brs) u ->
    joinable Σ Γ u (tCase ci p c' brs).
  Proof.
    intros hr he. depelim he.
    - (* case_eta_param *)
      exists (tCase ci (set_pparams p params') c' brs),
             (tCase ci (set_pparams p params') c' brs).
      repeat split.
      + apply red_le_one. now apply case_red_discr.
      + apply eta_rt_one. now apply case_eta_param.
      + apply upto_domain_refl.
    - (* case_eta_return *)
      exists (tCase ci (set_preturn p preturn') c' brs),
             (tCase ci (set_preturn p preturn') c' brs).
      repeat split.
      + apply red_le_one. now apply case_red_discr.
      + apply eta_rt_one. now apply case_eta_return.
      + apply upto_domain_refl.
    - (* case_eta_discr: same position, IH *)
      match goal with Ho : eta1 _ _ |- _ => rename Ho into ho end.
      destruct (IH Γ c c'0 c' hr ho) as [w [w' [hle [heta hu]]]].
      exists (tCase ci p w brs), (tCase ci p w' brs).
      repeat split.
      + exact (red_le_case_discr Γ ci p brs c'0 w hle).
      + now apply eta_rt_case_discr.
      + now apply utd_case_discr.
    - (* case_eta_brs *)
      exists (tCase ci p c' brs'), (tCase ci p c' brs').
      repeat split.
      + apply red_le_one. now apply case_red_discr.
      + apply eta_rt_one. now apply case_eta_brs.
      + apply upto_domain_refl.
  Qed.

  (** ** Row 4: [case_red_brs] — the branch-context row.

      The second square the lane lead singled out. Two facts make it close:
      (i) [eta1] on a branch ([case_eta_brs]) uses [on_Trel_eq eta1 bbody bcontext],
      so it NEVER changes [bcontext]; and [inst_case_branch_context p br] reads only
      [br.(bcontext)] (and [p.(pparams)]/[p.(puinst)]). So a branch η step does NOT
      move the branch's reduction context — the collision is an ordinary IH square in
      a FIXED context. (ii) The only η step that moves [inst_case_branch_context] is
      [case_eta_param] (it changes [pparams]); that is the context-moving subcase and
      it closes exactly as [case_red_return] did, via [red1_eta_ctx_strong]. *)

  Notation brs_red Γ p :=
    (OnOne2 (fun br br' =>
       on_Trel_eq (fun t u => red1 Σ (Γ ,,, inst_case_branch_context p br) t u)
                  bbody bcontext br br')).

  Lemma red_le_case_brs Γ ci p c brs brs' :
    ((brs' = brs) + brs_red Γ p brs brs') ->
    red_le Σ Γ (tCase ci p c brs) (tCase ci p c brs').
  Proof.
    intros [->|h].
    - apply red_le_refl.
    - apply red_le_one. now apply case_red_brs.
  Qed.

  Lemma utd_case_brs ci p c brs brs' :
    All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                     × upto_domain x.(bbody) y.(bbody)) brs brs' ->
    upto_domain (tCase ci p c brs) (tCase ci p c brs').
  Proof.
    intro h. constructor; tas.
    - apply All2_upto_domain_refl.
    - reflexivity.
    - apply eq_context_upto_names_refl.
    - apply upto_domain_refl.
    - apply upto_domain_refl.
  Qed.

  (** The branch collision square: [case_red_brs] against [case_eta_brs]. Mirrors
      [onone2_param_square]; the per-branch context is fixed because η preserves
      [bcontext]. *)
  Lemma onone2_brs_square Γ p brs brs1 brs2 :
    brs_red Γ p brs brs1 ->
    OnOne2 (on_Trel_eq eta1 bbody bcontext) brs brs2 ->
    ∑ m m', ((m = brs2) + brs_red Γ p brs2 m)
          × clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext)) brs1 m'
          × All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                             × upto_domain x.(bbody) y.(bbody)) m m'.
  Proof.
    intro h. revert brs2. induction h as [hd hd1 tl [r ec]|hd tl tl1 h ih];
      intros brs2 he; depelim he.
    - (* both at the head: IH on the colliding branch body, FIXED context *)
      destruct p0 as [e ec2].
      unfold on_Trel in *.
      destruct (IH (Γ ,,, inst_case_branch_context p hd)
                   hd.(bbody) hd'.(bbody) hd1.(bbody) r e)
        as [w [w' [hle [heta hu]]]].
      assert (ebc : inst_case_branch_context p hd' = inst_case_branch_context p hd).
      { unfold inst_case_branch_context. now rewrite ec2. }
      destruct hle as [z hs|].
      + (* one red1 on the branch body *)
        exists ({| bcontext := hd.(bcontext); bbody := z |} :: tl),
               ({| bcontext := hd.(bcontext); bbody := w' |} :: tl).
        repeat split.
        * right. constructor. split.
          -- unfold on_Trel; cbn. rewrite ebc. exact hs.
          -- cbn. now rewrite ec2.
        * apply eta_rt_brs_hd; cbn; [exact (eq_sym ec)|exact heta].
        * constructor.
          -- split; cbn; [apply eq_context_upto_names_refl|exact hu].
          -- apply All2_branch_refl.
      + (* no red1: η-reduct branch already joined *)
        exists (hd' :: tl),
               ({| bcontext := hd.(bcontext); bbody := w' |} :: tl).
        repeat split.
        * left. reflexivity.
        * apply eta_rt_brs_hd; cbn; [exact (eq_sym ec)|exact heta].
        * constructor.
          -- split; cbn; [rewrite ec2; apply eq_context_upto_names_refl|].
             (* w = bbody hd' here *) exact hu.
          -- apply All2_branch_refl.
    - (* red1 at head, η in tail: disjoint *)
      exists (hd1 :: tl'), (hd1 :: tl'). repeat split.
      + right. constructor. split; [exact r|exact ec].
      + apply rt_step. apply OnOne2_tl. exact he.
      + apply All2_branch_refl.
    - (* red1 in tail, η at head: disjoint *)
      destruct p0 as [e ec2].
      exists (hd' :: tl1), (hd' :: tl1). repeat split.
      + right. apply OnOne2_tl. exact h.
      + apply rt_step. constructor. split; [exact e|exact ec2].
      + apply All2_branch_refl.
    - (* both in tail *)
      destruct (ih _ he) as [m [m' [hm [hm' hu]]]].
      exists (hd :: m), (hd :: m'). repeat split.
      + destruct hm as [->|hstep].
        * left. reflexivity.
        * right. now apply OnOne2_tl.
      + clear -hm'. induction hm' as [a b hh|a|a b d h1 ih1 h2 ih2].
        * apply rt_step. now apply OnOne2_tl.
        * apply rt_refl.
        * eapply rt_trans; eassumption.
      + constructor; tas.
        split; [apply eq_context_upto_names_refl|apply upto_domain_refl].
  Qed.

  (** The context-move for one β branch step when η changes [pparams]:
      replay the branch step in the moved context ([red1_eta_ctx_strong], ≤1 red1),
      and give the η-star from the β-reduct branches to the join branches. *)
  Lemma brs_red_move Γ p params' brs brs' :
    OnOne2 eta1 (pparams p) params' ->
    brs_red Γ p brs brs' ->
    ∑ brs'',
      ((brs'' = brs) + brs_red Γ (set_pparams p params') brs brs'')
      × clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext)) brs' brs''.
  Proof.
    intros ho hr. induction hr as [hd hd' tl [r ec]|hd tl tl' h ih].
    - unfold on_Trel in *.
      destruct (red1_eta_ctx_le
          (Γ ,,, inst_case_branch_context p hd)
          (Γ ,,, inst_case_branch_context (set_pparams p params') hd)
          _ _
          (eta_ctx_prepend Γ _ _
             (eta_ctx_inst_case_context (pparams p) params' (puinst p) hd.(bcontext) ho))
          r) as [b'' [hle heta]].
      destruct hle as [z hs|].
      + exists ({| bcontext := hd.(bcontext); bbody := z |} :: tl). split.
        * right. constructor. split.
          -- unfold on_Trel; cbn. exact hs.
          -- reflexivity.
        * apply eta_rt_brs_hd; cbn; [exact (eq_sym ec)|exact heta].
      + exists (hd :: tl). split.
        * left. reflexivity.
        * apply eta_rt_brs_hd; cbn; [exact (eq_sym ec)|exact heta].
    - destruct ih as [brs'' [hsum heta_br]].
      exists (hd :: brs''). split.
      + destruct hsum as [->|hstep].
        * left. reflexivity.
        * right. now apply OnOne2_tl.
      + (* prepend hd to the η-star *)
        clear -heta_br. induction heta_br as [a b hh|a|a b d h1 ih1 h2 ih2].
        * apply rt_step. now apply OnOne2_tl.
        * apply rt_refl.
        * eapply rt_trans; eassumption.
  Qed.

  Lemma c3_case_red_brs Γ ci p c brs brs' (u : term) :
    brs_red Γ p brs brs' ->
    eta1 (tCase ci p c brs) u ->
    joinable Σ Γ u (tCase ci p c brs').
  Proof.
    intros hr he. depelim he.
    - (* case_eta_param: MOVES inst_case_branch_context — the context row *)
      match goal with Ho : OnOne2 eta1 _ _ |- _ => rename Ho into ho end.
      destruct (brs_red_move Γ p params' brs brs' ho hr) as [brs'' [hsum heta_br]].
      exists (tCase ci (set_pparams p params') c brs''),
             (tCase ci (set_pparams p params') c brs'').
      repeat split; [| |apply upto_domain_refl].
      + exact (red_le_case_brs Γ ci (set_pparams p params') c brs brs'' hsum).
      + eapply rt_trans.
        * apply eta_rt_one.
          exact (case_eta_param ci p params' c brs' ho).
        * exact (eta_rt_case_brs ci (set_pparams p params') c brs' brs'' heta_br).
    - (* case_eta_return: disjoint (brs context ignores preturn) *)
      match goal with Ho : eta1 _ _ |- _ => rename Ho into ho end.
      exists (tCase ci (set_preturn p preturn') c brs'),
             (tCase ci (set_preturn p preturn') c brs').
      repeat split; [| |apply upto_domain_refl].
      + apply red_le_one. now apply case_red_brs.
      + apply eta_rt_one. now apply case_eta_return.
    - (* case_eta_discr: disjoint *)
      exists (tCase ci p c' brs'), (tCase ci p c' brs').
      repeat split; [| |apply upto_domain_refl].
      + apply red_le_one. now apply case_red_brs.
      + apply eta_rt_one. now apply case_eta_discr.
    - (* case_eta_brs: collision via the branch square (fixed context) *)
      match goal with Ho : OnOne2 _ _ _ |- _ => rename Ho into ho end.
      destruct (onone2_brs_square Γ p brs brs' brs'0 hr ho)
        as [m [m' [hm [hm' hu]]]].
      exists (tCase ci p c m), (tCase ci p c m'). repeat split.
      + exact (red_le_case_brs Γ ci p c brs'0 m hm).
      + now apply eta_rt_case_brs.
      + now apply utd_case_brs.
  Qed.

  (** ** Row 5: [red_iota] — the let-bound-parameter / [expand_lets] row.

      The β step IS the ι-contraction: it reads [p.(pparams)], [p.(puinst)] and the
      selected branch's [bcontext] through [inst_case_branch_context], substitutes the
      spine via [expand_lets] (where let-bound parameters are duplicated), and drops
      the predicate's [preturn] and the other branches. So an η step in any of those
      positions must be reflected in [iota_red]. Every subcase closes with ONE
      [red_iota] on the η-reduct side and η-steps (through [expand_lets]/[subst]) on
      the β-reduct side. *)

  Context (eta_rt_iota_args : forall npar pr args args' br,
             OnOne2 eta1 args args' ->
             eta_rt (iota_red npar pr args br) (iota_red npar pr args' br)).
  Context (eta_rt_iota_params : forall npar pr params' args br,
             OnOne2 eta1 pr.(pparams) params' ->
             eta_rt (iota_red npar pr args br) (iota_red npar (set_pparams pr params') args br)).
  Context (eta_rt_iota_body : forall npar pr args br br',
             br.(bcontext) = br'.(bcontext) -> eta1 br.(bbody) br'.(bbody) ->
             eta_rt (iota_red npar pr args br) (iota_red npar pr args br')).

  Lemma c3_red_iota Γ ci cidx uinst args p brs br (u : term) :
    nth_error brs cidx = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    eta1 (tCase ci p (mkApps (tConstruct ci.(ci_ind) cidx uinst) args) brs) u ->
    joinable Σ Γ u (iota_red ci.(ci_npar) p args br).
  Proof.
    intros hnth hlen he. depelim he.
    - (* case_eta_param: η in pparams, reflected through inst_case_branch_context *)
      match goal with Ho : OnOne2 eta1 _ _ |- _ => rename Ho into ho end.
      exists (iota_red ci.(ci_npar) (set_pparams p params') args br),
             (iota_red ci.(ci_npar) (set_pparams p params') args br).
      repeat split; [| |apply upto_domain_refl].
      + apply red_le_one. now apply red_iota.
      + exact (eta_rt_iota_params ci.(ci_npar) p params' args br ho).
    - (* case_eta_return: iota_red ignores preturn → join is the β-reduct itself *)
      exists (iota_red ci.(ci_npar) (set_preturn p preturn') args br),
             (iota_red ci.(ci_npar) p args br).
      repeat split; [| |apply upto_domain_refl].
      + apply red_le_one. now apply red_iota.
      + apply rt_refl.
    - (* case_eta_discr: η in the discriminee spine args (tConstruct is η-inert) *)
      match goal with Ho : eta1 _ _ |- _ => rename Ho into ho end.
      apply eta1_mkApps_inv in ho as [[M' [hM ->]]|[args' [hargs ->]]].
      + (* η on the head tConstruct: impossible *)
        exfalso. depelim hM.
      + exists (iota_red ci.(ci_npar) p args' br),
               (iota_red ci.(ci_npar) p args' br).
        repeat split; [| |apply upto_domain_refl].
        * apply red_le_one. apply red_iota; tas.
          now rewrite <- (OnOne2_length hargs).
        * exact (eta_rt_iota_args ci.(ci_npar) p args args' br hargs).
    - (* case_eta_brs: η in one branch body; bcontext preserved *)
      match goal with Ho : OnOne2 _ _ _ |- _ => rename Ho into ho end.
      destruct (OnOne2_nth_error _ _ _ _ _ ho hnth) as [br' [hnth' hbr]].
      exists (iota_red ci.(ci_npar) p args br'),
             (iota_red ci.(ci_npar) p args br').
      repeat split; [| |apply upto_domain_refl].
      + apply red_le_one. apply red_iota; tas.
        destruct hbr as [heq|[hbody hctx]].
        * now rewrite <- heq.
        * unfold on_Trel in hctx. now rewrite <- hctx.
      + destruct hbr as [heq|[hbody hctx]].
        * rewrite <- heq. apply rt_refl.
        * unfold on_Trel in hbody, hctx.
          exact (eta_rt_iota_body ci.(ci_npar) p args br br' hctx hbody).
  Qed.

End Falsify.

(** No [Admitted], no [Axiom]. Each row's [Print Assumptions] shows only the
    Section [Context] hypotheses (the U-rows and the C3-budget [red1_eta_ctx]),
    which are discharged by the plan's U-rows, never an axiom. *)
Print Assumptions c3_case_red_param.
Print Assumptions c3_case_red_return.
Print Assumptions c3_case_red_discr.
Print Assumptions c3_case_red_brs.
Print Assumptions c3_red_iota.
