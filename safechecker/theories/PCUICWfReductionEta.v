(* Distributed under the terms of the MIT license. *)
(** * The well-founded orders of [PCUICWfReduction], over an abstract typing

  BET-315 eta lane, plan I7 rev 13/14 B3 (a): the E copy of [PCUICWfReduction.v]
  (trunk [0729d50e], equal to [frac/eta] [0cb773a4]). It keeps base [PCUICPosition].

  The order [redp_subterm_rel] is stated over an abstract well-typedness predicate [wt]
  and an abstract environment predicate [wfP]. Its well-foundedness uses exactly two
  typed facts, the same two base uses:
  - normalization: [NormalizationInWt wt Σ], [Acc (cored Σ Γ) t] for every [wt]-typed
    [t] (base [NormalizationIn]; [NormalizationInE] when [wt := welltypedE], by
    conversion);
  - subject reduction along [red]: [WtRed wt wfP] (base [red_welltyped]).
  The reduction machine ([PCUICSafeReduceEta]) terminates by fuel ([PCUICFuelEta]) and
  uses no well-founded order of this file (BET-64 FUEL).

  [AbstractEnvWf X_type X wfP] says the environments of [X] satisfy [wfP]. Its instance
  [abstract_env_wfP_E] (at [wfP := wf_extE], from [abstract_env_ext_wf] of
  [PCUICWfEnvEta]) is proved below.

  The instance [wt_red_base] of [WtRed] at base [welltyped] and [wf_ext] is proved below,
  with what it shows and what it does not. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnOne
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakeningConv PCUICWeakeningTyp PCUICReduction PCUICConversion
     PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses
     PCUICTypingEta.

From MetaRocq.SafeChecker Require Import PCUICWfEnvEta.


From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

(** ** The interface *)

(** Normalization of the [wt]-typed terms (base [NormalizationIn], with [welltyped]
    replaced by [wt]). *)
Class NormalizationInWt {cf : checker_flags} {no : normalizing_flags}
  (wt : global_env_ext -> context -> term -> Prop) (Σ : global_env_ext) :=
  normalization_in_wt : forall Γ t, wt Σ Γ t -> Acc (cored Σ Γ) t.
#[export] Hint Mode NormalizationInWt - - - + : typeclass_instances.

(** Subject reduction of [wt] along [red] (plan row T1 at [welltypedE]). *)
Class WtRed {cf : checker_flags}
  (wt : global_env_ext -> context -> term -> Prop) (wfP : global_env_ext -> Type) :=
  wt_red : forall Σ Γ u v, wfP Σ -> wt Σ Γ u -> red Σ Γ u v -> wt Σ Γ v.
#[export] Hint Mode WtRed - + - : typeclass_instances.

(** The environments of an abstract environment satisfy [wfP]. *)
Class AbstractEnvWf {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
  (wfP : global_env_ext -> Type) :=
  abstract_env_wfP : forall Σ, abstract_env_ext_rel X Σ -> ∥ wfP Σ ∥.
#[export] Hint Mode AbstractEnvWf - - - + : typeclass_instances.

(** The instance used by every E caller. *)
#[export] Instance abstract_env_wfP_E {cf : checker_flags} (X_type : abstract_env_impl)
  (X : X_type.π2.π1) : AbstractEnvWf X_type X wf_extE :=
  fun Σ h => abstract_env_ext_wf X h.

(** *** The base instance of [WtRed]

    [wt_red_base] proves [WtRed] at base [welltyped] and [wf_ext] from base subject
    reduction ([subject_reduction]). (1) It shows that the hypothesis is consistent and
    that the sections below are about something real: the base reduction machine is
    the instance of this file at [welltyped]. (2) It does NOT discharge the
    instantiation at [welltypedE] and [wf_extE]: subject reduction over [typingE]
    (plan row T1) remains a hypothesis until that row lands. *)
#[export] Instance wt_red_base {cf : checker_flags} : WtRed welltyped wf_ext.
Proof.
  intros Σ Γ u v [wfΣ _] [A h] r. exists A.
  eapply subject_reduction; eauto.
Qed.

(* Show that taking head normal forms and then the subterm relation is well-founded *)

Inductive term_direct_subterm : term -> term -> Type :=
| term_direct_subterm_4_1 : forall (na : aname) (A B : term),
  term_direct_subterm B (tProd na A B)
| term_direct_subterm_4_2 : forall (na : aname) (A B : term),
  term_direct_subterm A (tProd na A B)
| term_direct_subterm_5_1 : forall (na : aname) (A t : term),
  term_direct_subterm t (tLambda na A t)
| term_direct_subterm_5_2 : forall (na : aname) (A t : term),
  term_direct_subterm A (tLambda na A t)
| term_direct_subterm_6_1 : forall (na : aname) (b B t : term),
  term_direct_subterm t (tLetIn na b B t)
| term_direct_subterm_6_2 : forall (na : aname) (b B t : term),
  term_direct_subterm B (tLetIn na b B t)
| term_direct_subterm_6_3 : forall (na : aname) (b B t : term),
  term_direct_subterm b (tLetIn na b B t)
| term_direct_subterm_7_1 : forall u v : term,
  term_direct_subterm v (tApp u v)
| term_direct_subterm_7_2 : forall u v : term,
  term_direct_subterm u (tApp u v)
| term_direct_subterm_11_1 : forall (ci : case_info)
     (p : predicate term) (c : term) (brs : list (branch term)),
   term_direct_subterm c (tCase ci p c brs)
| term_direct_subterm_11_2 : forall (ci : case_info)
  (p : predicate term) (c : term) (brs : list (branch term)),
  term_direct_subterm p.(preturn) (tCase ci p c brs)
| term_direct_subterm_12_1 : forall (p : projection) (c : term),
  term_direct_subterm c (tProj p c).
Derive Signature for term_direct_subterm.

Definition term_direct_subterm_context (t u : term) (p : term_direct_subterm t u) : context :=
  match p with
  | term_direct_subterm_4_1 na A B => [vass na A]
  | term_direct_subterm_5_1 na A t => [vass na A]
  | term_direct_subterm_6_1 na b B t => [vdef na b B]
  | term_direct_subterm_11_2 ci p c brs => inst_case_predicate_context p
  | _ => []
  end.

Require Equations.Type.WellFounded.
Definition term_subterm := Relation.trans_clos term_direct_subterm.

Fixpoint term_subterm_context {t u : term} (p : term_subterm t u) : context :=
  match p with
  | Relation.t_step y xy => term_direct_subterm_context _ _ xy
  | Relation.t_trans y z rxy ryz =>
    term_subterm_context rxy ++ term_subterm_context ryz
  end.

Definition term_subterm_wf : Equations.Type.WellFounded.well_founded term_subterm.
Proof.
  eapply WellFounded.wf_trans_clos.
  red. fix IH 1. intro x; constructor.
  destruct x; intros y sub; depelim sub; apply IH.
Defined.

(** At least one step of reduction *)
Definition redp Σ Γ t u := Relation.trans_clos (red1 Σ Γ) t u.

#[global]
Instance redp_trans Σ Γ : CRelationClasses.Transitive (redp Σ Γ).
Proof. econstructor 2; eauto. Qed.

#[global]
Instance redp_red Σ Γ : CRelationClasses.subrelation (redp Σ Γ) (red Σ Γ).
Proof.
  intros x y.
  induction 1; solve [econstructor; eauto].
Qed.

#[global]
Instance cored_transitive Σ Γ : RelationClasses.Transitive (cored Σ Γ).
Proof.
  intros x y z.
  induction 1 in z |- *. econstructor 2; eauto.
  intros uz. specialize (IHcored _ uz).
  econstructor 2. eapply IHcored. assumption.
Qed.

Lemma cored_redp Σ Γ t u : cored Σ Γ u t <-> ∥ redp Σ Γ t u ∥.
Proof.
  split.
  * induction 1; sq; try solve [econstructor; eauto].
    transitivity v; auto. now constructor.
  * intros []. induction X.
    + now constructor.
    + now transitivity y.
Qed.

(** Weak-head reduction and the subterm relation on ([wt]-typed) terms: the facts the
    order [redp_subterm_rel] below uses. *)
Section fix_sigma.
  Context {cf : checker_flags} {no : normalizing_flags}.
  Context {wt : global_env_ext -> context -> term -> Prop} {wfP : global_env_ext -> Type}.
  Context {WR : WtRed wt wfP}.
  Context {Σ : global_env_ext} {HΣ : ∥ wfP Σ ∥}.

  Lemma term_subterm_red1 {Γ s s' t} {ts : term_subterm s t} :
    red1 Σ (Γ ,,, term_subterm_context ts) s s' ->
    exists t', ∥ red1 Σ Γ t t' × ∑ ts' : term_subterm s' t', term_subterm_context ts' = term_subterm_context ts ∥.
  Proof using Type.
    induction ts in Γ, s' |- *.
    - induction r; simpl.
    all:intros red; eexists; split;
    try solve [split; [solve [eauto using red1]|unshelve eexists;[repeat constructor|simpl; eauto]]].
    split.
    eapply letin_red_body; eauto. unshelve eexists. repeat constructor. reflexivity.
    split.
    eapply letin_red_ty; eauto. unshelve eexists. repeat constructor. reflexivity.
    split. eapply letin_red_def; eauto. unshelve eexists. repeat constructor. reflexivity.
    split. eapply case_red_return; eauto. unshelve eexists. repeat constructor.
    eapply (term_direct_subterm_11_2 ci (set_preturn p s')). simpl. reflexivity.
    - simpl. intros.
    rewrite app_context_assoc in X.
    specialize (IHts1 _ _ X) as [t' [[yt' [ts Hts]]]].
    specialize (IHts2 _ _ yt') as [t'' [[zt' [ts'' Hts'']]]].
    exists t''. split; split; auto.
    unshelve eexists. econstructor 2; eauto. simpl.
    now rewrite Hts Hts''.
  Qed.

  Lemma term_subterm_redp {Γ s s' t} {ts : term_subterm s t} :
    redp Σ (Γ ,,, term_subterm_context ts : context) s s' ->
    exists t', ∥ redp Σ Γ t t' × ∑ ts' : term_subterm s' t', term_subterm_context ts' = term_subterm_context ts ∥.
  Proof using Type.
    intros r.
    generalize_eqs r. intros ->. revert t ts.
    induction r.
    - intros t ts ->.
      destruct (term_subterm_red1 r) as [t' [[red1 [ts' Hts']]]].
      exists t'; split; auto. split; auto. now constructor. exists ts'; auto.
    - intros t ts ->. specialize (IHr1 t ts eq_refl) as [t' [[yt' [ts' Hts]]]].
      specialize (IHr2 t' ts').
      forward IHr2. now rewrite Hts.
      destruct IHr2 as [t'' [[zt' [ts'' Hts'']]]].
      exists t''. split; split; auto.
      now transitivity t'.
      exists ts''.
      now rewrite Hts'' Hts.
  Qed.

  Opaque Acc_intro_generator.
  Opaque Wf.Acc_intro_generator.
  Ltac sq := try (destruct HΣ as [wfΣ]; clear HΣ);
    repeat match goal with
    | H : ∥ _ ∥ |- _ => destruct H
    end; try eapply sq.

End fix_sigma.

Section fix_sigma.
  Context {cf : checker_flags} {no : normalizing_flags}.
  Context {wt : global_env_ext -> context -> term -> Prop} {wfP : global_env_ext -> Type}.
  Context {WR : WtRed wt wfP}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {hX : AbstractEnvWf X_type X wfP}.

  Context {normalization_in : forall Σ, wfP Σ -> Σ ∼_ext X -> NormalizationInWt wt Σ}.

  (* Reducing at least one step or taking a subterm is well-founded *)
  Definition redp_subterm_rel : Relation_Definitions.relation (∑ Γ t, forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ t) :=
    fun '(Γ2; t2; H) '(Γ1; t1; H2) => forall Σ (wfΣ : abstract_env_ext_rel X Σ),
    ∥ (redp Σ Γ1 t1 t2 * (Γ1 = Γ2)) + ∑ ts : term_subterm t2 t1, Γ2 = (Γ1 ,,, term_subterm_context ts) ∥.

  Definition wf_redp_subterm_rel : WellFounded redp_subterm_rel.
  Proof.
    intros (Γ & s & H). pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (@abstract_env_wfP _ X_type X wfP hX Σ wfΣ) as [wfPΣ].
    induction (normalization_in Σ wfPΣ wfΣ Γ s (H _ wfΣ)) as [s _ IH].
    induction (term_subterm_wf s) as [s _ IH_sub] in Γ, H, IH |- *.
    econstructor.
    intros (Γ' & t2 & ?). intro R. specialize (R _ wfΣ).
    destruct R as [[[r eq]|[ts eqctx]]].
    + subst. eapply Relation_Properties.trans_clos_tn1 in r.
      eapply IH. clear -r.
      induction r; try solve [econstructor; auto].
      now eapply cored_trans with y.
    + subst.
      apply IH_sub. eauto.
      intros. eapply cored_redp in H0 as [].
      destruct (term_subterm_redp X0) as [t'' [[redt' [tst' Htst']]]].
      eapply IH. eapply cored_redp. sq. eassumption. red. intros.
      sq. right. exists tst'. now rewrite Htst'.
    Unshelve. intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
              eapply redp_red in redt'.
              eapply wt_red; [exact wfPΣ|exact (H _ wfΣ)|exact redt'].
    Unshelve. eauto.
  Defined.

  Global Instance wf_redp_subterm : WellFounded redp_subterm_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_redp_subterm_rel.
  Defined.
  Opaque wf_redp_subterm.
  Opaque Acc_intro_generator.
  Opaque Wf.Acc_intro_generator.

End fix_sigma.
