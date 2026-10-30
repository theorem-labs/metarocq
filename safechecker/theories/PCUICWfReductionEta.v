(* Distributed under the terms of the MIT license. *)
(** * The orders of [PCUICWfReduction], over an abstract typing

  BET-315 eta lane, plan I7 rev 13/14 B3 (a): the E copy of [PCUICWfReduction.v]
  (trunk [0729d50e], equal to [frac/eta] [0cb773a4]). It keeps base [PCUICPosition].

  The order [redp_subterm_rel] is stated over an abstract well-typedness predicate [wt]
  and an abstract environment predicate [wfP]. Its well-foundedness is no longer proved
  here: it needed the normalisation premise, and the η checker's recursions now terminate
  by fuel ([PCUICFuelEta], BET-64 FUEL): the reduction machine ([PCUICSafeReduceEta]) and the
  cofixpoint codomain walk ([PCUICTypeCheckerEta.check_codomain_ind]). The order stays for
  the decrease proof of that walk ([PCUICTypeCheckerEta.codomain_step_lt]), kept.

  Subject reduction along [red] is the class [WtRed wt wfP] (base [red_welltyped]), used by
  the machine. [AbstractEnvWf X_type X wfP] says the environments of [X] satisfy [wfP]. Its
  instance [abstract_env_wfP_E] (at [wfP := wf_extE], from [abstract_env_ext_wf] of
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

(* The subterm relation (under binders, with the context it extends), for [redp_subterm_rel] below *)

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

(** The order of the cofixpoint codomain walk's decrease proof: one reduction step or more, or a
    subterm (under its binders). *)
Section redp_subterm.
  Context {cf : checker_flags} {wt : global_env_ext -> context -> term -> Prop}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Definition redp_subterm_rel : Relation_Definitions.relation (∑ Γ t, forall Σ (wfΣ : abstract_env_ext_rel X Σ), wt Σ Γ t) :=
    fun '(Γ2; t2; H) '(Γ1; t1; H2) => forall Σ (wfΣ : abstract_env_ext_rel X Σ),
    ∥ (redp Σ Γ1 t1 t2 * (Γ1 = Γ2)) + ∑ ts : term_subterm t2 t1, Γ2 = (Γ1 ,,, term_subterm_context ts) ∥.

End redp_subterm.
