(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICWcbvEval PCUICClassification PCUICCanonicity PCUICSN PCUICNormalization PCUICViews.

From Equations Require Import Equations.

Definition False_oib : one_inductive_body :=
  {| ind_name := "False";
     ind_indices := [];
     ind_sort := sProp;
     ind_type := tSort sProp;
     ind_kelim := IntoAny;
     ind_ctors := [];
     ind_projs := [];
     ind_relevance := Relevant |}.

Definition False_mib : mutual_inductive_body :=
  {| ind_finite := BiFinite;
     ind_npars := 0;
     ind_params := [];
     ind_bodies := [False_oib];
     ind_universes := Monomorphic_ctx;
     ind_variance := None |}.

(** The one case the proof below cannot close: a closed well-typed term of the empty
    type whose weak-head normal form is a case blocked on a cofixpoint. Rocq's kernel
    types such a match, because its rule for the type of a case makes no coinductivity
    test (kernel/typeops.ml:547-583); its machine unfolds the cofixpoint under the case
    (kernel/cClosure.ml:1925-1932), which is the step that breaks subject reduction
    here; Rocq's manual records that failure as a known caveat
    (doc/sphinx/language/core/coinductive.rst:75-86). This hypothesis is not proved
    here for environments with a coinductive type, and we found no proof of it
    anywhere. It holds in every environment without one, which the lemmas below prove,
    with a concrete instance. What would refute it is a closed term of that shape at
    type False; under Rocq's guard condition such a term would also be a closed proof
    of False in Rocq's kernel. *)
Definition no_closed_stuck_cofix_case_at {cf : checker_flags} (Σ : global_env_ext)
    (ind : inductive) :=
  forall t, stuck_cofix_case t -> Σ ;;; [] |- t : tInd ind [] -> False.

(** A typed term contains a typed cofixpoint whenever it has the shape
    [stuck_cofix_case]; a typed cofixpoint needs a coinductive block in the environment
    ([wf_cofixpoint]). These inversions need no well-formedness of [Σ]. *)
Lemma typing_tApp_inv {cf : checker_flags} {Σ : global_env_ext} {Γ f a T} :
  Σ ;;; Γ |- tApp f a : T -> (∑ U, Σ ;;; Γ |- f : U) × (∑ U, Σ ;;; Γ |- a : U).
Proof.
  intros h; depind h; try solve [eauto]; split; eexists; eassumption.
Qed.

Lemma typing_tCase_scrut {cf : checker_flags} {Σ : global_env_ext} {Γ ci p c brs T} :
  Σ ;;; Γ |- tCase ci p c brs : T -> ∑ U, Σ ;;; Γ |- c : U.
Proof.
  intros h; depind h; try solve [eauto]; eexists; eassumption.
Qed.

Lemma typing_tProj_arg {cf : checker_flags} {Σ : global_env_ext} {Γ pr c T} :
  Σ ;;; Γ |- tProj pr c : T -> ∑ U, Σ ;;; Γ |- c : U.
Proof.
  intros h; depind h; try solve [eauto]; eexists; eassumption.
Qed.

Lemma typing_tCoFix_cofinite {cf : checker_flags} {Σ : global_env_ext} {Γ mfix idx T} :
  Σ ;;; Γ |- tCoFix mfix idx : T ->
  ∑ mind, check_recursivity_kind (lookup_env Σ) mind CoFinite.
Proof.
  intros h; depind h; try solve [eauto];
  match goal with H : wf_cofixpoint _ _ _ |- _ => destruct H as (mind & _ & _ & hk) end;
  now exists mind.
Qed.

Lemma typing_mkApps_arg {cf : checker_flags} {Σ : global_env_ext} {Γ f args T n arg} :
  Σ ;;; Γ |- mkApps f args : T -> nth_error args n = Some arg ->
  ∑ U, Σ ;;; Γ |- arg : U.
Proof.
  revert T; induction args using rev_ind; intros T; [intros _ hn; now destruct n|].
  rewrite mkApps_app /=. intros h hn.
  destruct (typing_tApp_inv h) as [[U hf] [V hx]].
  destruct (lt_dec n #|args|) as [lt|ge].
  - rewrite nth_error_app_lt // in hn. eauto.
  - rewrite nth_error_app_ge in hn; [lia|].
    destruct (n - #|args|) as [|k]; cbn in hn; [|now destruct k].
    injection hn as <-. now exists V.
Qed.

Lemma typing_mkApps_head {cf : checker_flags} {Σ : global_env_ext} {Γ f args T} :
  Σ ;;; Γ |- mkApps f args : T -> ∑ U, Σ ;;; Γ |- f : U.
Proof.
  revert T; induction args using rev_ind; intros T; [intros h; now exists T|].
  rewrite mkApps_app /=. intros h.
  destruct (typing_tApp_inv h) as [[U hf] _]. eauto.
Qed.

Lemma typing_stuck_cofix_case_cofinite {cf : checker_flags} {Σ : global_env_ext} {Γ t T} :
  stuck_cofix_case t -> Σ ;;; Γ |- t : T ->
  ∑ mind, check_recursivity_kind (lookup_env Σ) mind CoFinite.
Proof.
  intros st; induction st in Γ, T |- *; intros h.
  - destruct (typing_tCase_scrut h) as [U hc].
    destruct (typing_mkApps_head hc) as [V hcf].
    exact (typing_tCoFix_cofinite hcf).
  - destruct (typing_tApp_inv h) as [[U hf] _]. eauto.
  - destruct (typing_tCase_scrut h) as [U hc]. eauto.
  - destruct (typing_tProj_arg h) as [U hc]. eauto.
  - match goal with hn : nth_error args _ = Some arg |- _ =>
      destruct (typing_mkApps_arg h hn) as [U ha] end. eauto.
Qed.

(** The hypothesis holds in every environment without a coinductive block. *)
Lemma no_closed_stuck_cofix_case_at_no_cofinite {cf : checker_flags} (Σ : global_env_ext) ind :
  (forall mind, check_recursivity_kind (lookup_env Σ) mind CoFinite = false) ->
  no_closed_stuck_cofix_case_at Σ ind.
Proof.
  intros nocof t st h.
  destruct (typing_stuck_cofix_case_cofinite st h) as [mind hk].
  now rewrite nocof in hk.
Qed.

(** A concrete instance: the environment that declares only [False]. *)
Definition False_kn : kername := (MPfile ["Logic"; "Init"; "Corelib"], "False").

Definition Σ_False : global_env_ext :=
  ({| universes := ContextSet.empty;
      declarations := [(False_kn, InductiveDecl False_mib)];
      retroknowledge := Retroknowledge.empty |}, Monomorphic_ctx).

Lemma no_closed_stuck_cofix_case_at_Σ_False {cf : checker_flags} :
  no_closed_stuck_cofix_case_at Σ_False (mkInd False_kn 0).
Proof.
  apply no_closed_stuck_cofix_case_at_no_cofinite.
  intros mind. unfold check_recursivity_kind, lookup_env, Σ_False; cbn.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Theorem pcuic_consistent {cf:checker_flags} {nor : normalizing_flags} Σ
  {normalization_in: NormalizationIn Σ} t False_pcuic :
  declared_inductive Σ False_pcuic False_mib False_oib ->
  wf_ext Σ -> axiom_free Σ ->
  no_closed_stuck_cofix_case_at Σ False_pcuic ->
  Σ ;;; [] |- t : tInd False_pcuic []  -> False.
Proof.
  intros Hdecl wfΣ axΣ nostuck typ_false.
  destruct (pcuic_canonicity Σ t False_pcuic [] []) as [t' [[typ_false' eqtt'] ctor]]; eauto.
  destruct ctor as [ctor|stuck].
  2:{ now eapply nostuck. }
  destruct Hdecl as [Hdecl Hidecl].
  destruct False_pcuic as [kn n]. destruct n; cbn in *; [| now rewrite nth_error_nil in Hidecl].
  rewrite /construct_cofix_discr /head in ctor.
  destruct decompose_app eqn:decomp.
  apply decompose_app_inv in decomp; subst.
  destruct t0; try discriminate ctor.
  - apply PCUICValidity.inversion_mkApps in typ_false' as H; auto.
    destruct H as (?&typ_ctor&_).
    apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
    eapply Construct_Ind_ind_eq with (args' := []) in typ_false'; tea.
    2: eauto.
    destruct (on_declared_constructor d).
    destruct p.
    destruct s.
    destruct p.
    destruct typ_false' as (((((->&_)&_)&_)&_)&_).
    clear -Hdecl d wfΣ. destruct wfΣ.
    cbn in *.
    destruct d as ((?&?)&?).
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    unshelve eapply declared_minductive_to_gen in H; eauto.
    red in H, Hdecl. cbn in *. rewrite Hdecl in H; noconf H.
    cbn in H0. noconf H0.
    cbn in H1. rewrite nth_error_nil in H1.
    discriminate.
  - eapply @typing_cofix_coind with (indargs := []) in typ_false'; eauto.
    unfold check_recursivity_kind in typ_false'. destruct wfΣ.
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    red in Hdecl. rewrite Hdecl in typ_false'.
    cbn in typ_false'. inversion typ_false'.
Qed.
