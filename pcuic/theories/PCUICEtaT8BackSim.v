(* Distributed under the terms of the MIT license. *)

(** * T8, step 3: [R_c*] on [canon T] read back as base [red] on [T]

  ** Where this sits in the T8 route ([PCUICEtaT8Probe], "Route")
  1. A6 gives [(R_c ∪ eta1)*] from [canon T] to the head form.
  2. η is postponed in that chain: [R_c* (canon T) w] then [eta1* w head].
  3. (this file) [R_c* (canon T) w] is lifted back to [red T T'] with [canon T' = w].
  4. [w] is not a λ, so its η tail keeps its head; [canon T'] has that head, hence
     [T'] has it too ([canon_Sort_inv], [canon_Prod_inv], [canon_mkApps_Ind_inv]).

  ** Result: CLOSED, no premise
  [R_c_backsim]: [clos_refl_trans (R_c Σ Γ) (canon T) w -> ∑ T', red Σ Γ T T' × canon T' = w],
  for every [Σ], [Γ], [T]: no scoping, no [ClosedBodies], no typing, no [wf].
  [red_canon_backsim] is the same for a base [red] chain from [canon T]
  ([red Σ Γ (canon T) v -> ∑ T', red Σ Γ T T' × canon T' = canon v]), in case step 2
  ends with base [red] instead of [R_c*].

  ** Why no premise is needed
  [R_c] is "one [red1] step, then [canon]". Its one-step case analysis is the
  induction on [red1] in [red1_upto_domain_r_bodies] ([PCUICEtaC1aR]), which is
  premise-free and stated for ANY [upto_domain_r]-related pair. [upto_domain_r] is
  symmetric ([upto_domain_r_sym]) and relates [canon T] to [T]
  ([upto_domain_r_canon_self], read backwards), so the forward lemma read backwards
  IS the backward simulation: a [red1] step from [canon T] becomes at most one
  [red1] step from [T], and the two results are [upto_domain_r]-related, so
  [canon]-equal ([upto_domain_r_canon_iff]).

  Per [red1] rule, what a redex of [canon T] needs from [T] (all CLOSED in the
  C1a induction, no premise):
  - β: [canon] keeps every λ (domain := [canon_dom], annotation erased); β reads
    neither, so [T] has the same β-redex.
  - ζ, [red_rel] (context body; [upto_domain_r_bodies] carries it), δ (a [tConst]
    is unchanged by [canon]), [red_prim_op] (literals are unchanged by [canon]).
  - ι: same constructor, same branch index; [bcontext] keeps its declaration
    TYPES and bodies ([canon_decl] erases names only), so [context_assumptions] is
    the same and the arity check fires on [T] too.
  - proj: same constructor, same argument index.
  - fix / cofix-case / cofix-proj: [canon] keeps [rarg], the bodies up to
    [upto_domain_r], and every [tConstruct] head, so [unfold_fix]/[unfold_cofix]
    and [is_constructor] fire on [T] too.
  - congruences: the step is in a subterm that [T] also has, except a step in a λ
    DOMAIN of [canon T]; that domain is [canon_dom = tSort sProp], which has no
    [red1] step, and the C1a case [abs_red_l] answers it with zero steps anyway.

  So the canonical erasure never creates a redex: the decisive risk of step 3 (a
  canonical [R_c] step with no base step on [T]) does not arise, and there is no
  counterexample to look for. The one-step lemma gives [clos_refl red1], not
  [red1⁺]; T8's consumer needs [red] ([Σ ;;; Γ ⊢ T ⇝ T']), so the zero-step
  alternative (unreachable from a canonical source, see the congruence item) costs
  nothing and is not excluded here.

  [R_c_backsim_closed] packages the result as [closed_red], the form the pinned T8
  statements use; its two scoping premises are only the [closed_red] packaging, and
  T8 gets them from its typing premise.

  Dependencies: [PCUICEtaCanon], [PCUICEtaC1aR], [PCUICEtaCanonRed], and
  [PCUICWellScopedCumulativity] for [closed_red] only. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICEtaDefs PCUICEtaCanon PCUICEtaC1aR PCUICEtaCanonRed.

Local Open Scope type_scope.
Set Default Goal Selector "!".

(** ** The pinned statement *)

Definition T8_backsim_statement (Σ : global_env) : Type :=
  forall Γ T w, clos_refl_trans (R_c Σ Γ) (canon T) w -> ∑ T', red Σ Γ T T' × canon T' = w.

(** ** One step *)

(** [canon t] is [upto_domain_r]-related to [t]: [upto_domain_r_canon_self] read backwards. *)
Lemma canon_upto_domain_r t : upto_domain_r (canon t) t.
Proof. exact (upto_domain_r_sym _ _ (upto_domain_r_canon_self t)). Qed.

(** One [R_c] step from [canon t] is at most one [red1] step from [t]. *)
Lemma R_c_back1 Σ Γ t w :
  R_c Σ Γ (canon t) w -> ∑ t', clos_refl (red1 Σ Γ) t t' × canon t' = w.
Proof.
  intros (v0 & r & ->).
  destruct (red1_upto_domain_r_fixed (canon_upto_domain_r t) r) as (t' & ht' & e).
  exists t'. split; [exact ht'|].
  symmetry. exact (canon_eq_of_upto_domain_r _ _ e).
Qed.

(** ** The closure *)

Theorem R_c_backsim Σ Γ T w :
  clos_refl_trans (R_c Σ Γ) (canon T) w -> ∑ T', red Σ Γ T T' × canon T' = w.
Proof.
  intros h. apply clos_rt_rt1n_iff in h.
  remember (canon T) as x eqn:Ex.
  induction h as [x|x y z hs _ IH] in T, Ex |- *; subst x.
  - exists T. split; [apply rt_refl|reflexivity].
  - destruct (R_c_back1 Σ Γ T y hs) as (T1 & h1 & <-).
    destruct (IH T1 eq_refl) as (T' & h' & e').
    exists T'. split; [|exact e'].
    eapply rt_trans; [|exact h'].
    destruct h1 as [? h1|]; [now apply rt_step|apply rt_refl].
Qed.

Theorem T8_backsim Σ : T8_backsim_statement Σ.
Proof. intros Γ T w h. exact (R_c_backsim Σ Γ T w h). Qed.

(** The same for a base [red] chain from [canon T]: the form of step 2's output if η
    is postponed over base [red1] instead of over [R_c]. The chain lemma is the local
    [move] of [R_c_red] ([PCUICEtaCanonRed]), named here. *)
Lemma red_upto_domain_r_fixed Σ Γ a b a' :
  red Σ Γ a b -> upto_domain_r a a' -> ∑ b', red Σ Γ a' b' × upto_domain_r b b'.
Proof.
  intros hab. revert a'. apply clos_rt_rt1n_iff in hab.
  induction hab as [a|a b c hs _ IH]; intros a' ea.
  - exists a'. split; [apply rt_refl|exact ea].
  - destruct (red1_upto_domain_r_fixed ea hs) as (b' & hb' & eb).
    destruct (IH b' eb) as (c' & hc' & ec).
    exists c'. split; [|exact ec].
    eapply rt_trans; [|exact hc'].
    destruct hb' as [? hb'|]; [now apply rt_step|apply rt_refl].
Qed.

Lemma red_canon_backsim Σ Γ T v :
  red Σ Γ (canon T) v -> ∑ T', red Σ Γ T T' × canon T' = canon v.
Proof.
  intros h.
  destruct (red_upto_domain_r_fixed Σ Γ _ _ _ h (canon_upto_domain_r T)) as (T' & r & e).
  exists T'. split; [exact r|].
  symmetry. exact (canon_eq_of_upto_domain_r _ _ e).
Qed.

(** The [closed_red] form ([Σ ;;; Γ ⊢ T ⇝ T']) of the pinned T8 statements. *)
Lemma R_c_backsim_closed (Σ : global_env_ext) Γ T w :
  is_closed_context Γ -> is_open_term Γ T ->
  clos_refl_trans (R_c Σ Γ) (canon T) w -> ∑ T', Σ ;;; Γ ⊢ T ⇝ T' × canon T' = w.
Proof.
  intros hΓ hT h. destruct (R_c_backsim Σ Γ T w h) as (T' & r & e).
  exists T'. split; [|exact e].
  constructor; assumption.
Qed.

(** ** Head forms: what step 4 reads off [canon T' = w] *)

Lemma canon_Sort_inv t s : canon t = tSort s -> t = tSort s.
Proof. destruct t; cbn [canon]; intros e; try discriminate e; exact e. Qed.

Lemma canon_Ind_inv t ind u : canon t = tInd ind u -> t = tInd ind u.
Proof. destruct t; cbn [canon]; intros e; try discriminate e; exact e. Qed.

Lemma canon_Prod_inv t na A B :
  canon t = tProd na A B ->
  ∑ na0 A0 B0, [× t = tProd na0 A0 B0, canon_na na0 = na, canon A0 = A & canon B0 = B].
Proof.
  destruct t; cbn [canon]; intros e; try discriminate e.
  injection e as e1 e2 e3.
  do 3 eexists. split; [reflexivity|exact e1|exact e2|exact e3].
Qed.

Lemma canon_App_inv t f a :
  canon t = tApp f a -> ∑ f0 a0, [× t = tApp f0 a0, canon f0 = f & canon a0 = a].
Proof.
  destruct t; cbn [canon]; intros e; try discriminate e.
  injection e as e1 e2.
  do 2 eexists. split; [reflexivity|exact e1|exact e2].
Qed.

Lemma canon_mkApps_Ind_inv t ind u l :
  canon t = mkApps (tInd ind u) l -> ∑ l0, t = mkApps (tInd ind u) l0 × map canon l0 = l.
Proof.
  revert t. induction l as [|a l IH] using MRList.rev_ind; intros t e.
  - exists []. split; [|reflexivity]. exact (canon_Ind_inv t ind u e).
  - rewrite mkApps_app in e. cbn [mkApps] in e.
    destruct (canon_App_inv _ _ _ e) as (f0 & a0 & [-> ef ea]).
    destruct (IH f0 ef) as (l0 & -> & hl).
    exists (l0 ++ [a0]). split.
    + now rewrite mkApps_app.
    + rewrite map_app hl. cbn [map]. now rewrite ea.
Qed.

(** An [R_c*] chain that already ends at a head form gives a base reduction of [T]
    to that head form (the η tail of step 2 empty). *)

Lemma R_c_backsim_Sort Σ Γ T s :
  clos_refl_trans (R_c Σ Γ) (canon T) (tSort s) -> red Σ Γ T (tSort s).
Proof.
  intros h. destruct (R_c_backsim Σ Γ T _ h) as (T' & r & e).
  apply canon_Sort_inv in e. subst T'. exact r.
Qed.

Lemma R_c_backsim_Prod Σ Γ T na A B :
  clos_refl_trans (R_c Σ Γ) (canon T) (tProd na A B) ->
  ∑ na0 A0 B0, [× red Σ Γ T (tProd na0 A0 B0), canon_na na0 = na, canon A0 = A & canon B0 = B].
Proof.
  intros h. destruct (R_c_backsim Σ Γ T _ h) as (T' & r & e).
  destruct (canon_Prod_inv _ _ _ _ e) as (na0 & A0 & B0 & [-> e1 e2 e3]).
  exists na0, A0, B0. split; assumption.
Qed.

Lemma R_c_backsim_Ind Σ Γ T ind u l :
  clos_refl_trans (R_c Σ Γ) (canon T) (mkApps (tInd ind u) l) ->
  ∑ l0, red Σ Γ T (mkApps (tInd ind u) l0) × map canon l0 = l.
Proof.
  intros h. destruct (R_c_backsim Σ Γ T _ h) as (T' & r & e).
  destruct (canon_mkApps_Ind_inv _ _ _ _ e) as (l0 & -> & hl).
  exists l0. split; assumption.
Qed.

(** ** Instance: the decisive case, β through an erased domain

  [canon] replaces the domain [A] by [canon_dom]; the [R_c] β step on the canonical
  form comes back as a β step on the original term. *)

Lemma R_c_backsim_beta_instance Σ Γ na A s :
  ∑ T', red Σ Γ (tApp (tLambda na A (tRel 0)) (tSort s)) T' × canon T' = tSort s.
Proof.
  apply R_c_backsim. apply rt_step. exists (tSort s). split; [|reflexivity].
  cbn [canon]. exact (red_beta Σ Γ canon_la canon_dom (tRel 0) (tSort s)).
Qed.
