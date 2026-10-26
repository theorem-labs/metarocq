(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
     PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosedTyp PCUICContexts
     PCUICSubstitution PCUICCumulativity PCUICWellScopedCumulativity
     PCUICContextConversion PCUICConversion PCUICInductives.

(** * Reduction witnesses for the (co)fixpoint well-formedness conditions

  [wf_fixpoint] asks the declared type of a body to _convert_ to a type whose
  recursive argument is syntactically an applied inductive; [wf_cofixpoint] asks the
  same of the conclusion. A checker, and the bidirectional system, work instead with
  a _reduct_ of the declared type. For a well-scoped declared type the two agree, and
  this file proves both directions:

  - [fix_on_ind_red] / [cofix_on_ind_red]: the conversion witness yields a reduction
    witness, because [check_one_fix] and [check_one_cofix] only look at the shape of
    a type, and that shape is preserved by reduction and by equality up to universes;
  - [red_fix_on_ind] / [red_cofix_on_ind]: the converse, a reduct is convertible. *)

Implicit Types (cf : checker_flags).

(** ** [check_one_fix] and [check_one_cofix] are stable under equality up to universes *)

Lemma destInd_mind_eq_term_upto {Σ cmp_universe cmp_sort pb napp t u} :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t u ->
  match destInd t with Some (mkInd mind _, _) => Some mind | None => None end =
  match destInd u with Some (mkInd mind _, _) => Some mind | None => None end.
Proof.
  induction 1; cbn; reflexivity.
Qed.

Lemma check_one_fix_eq_term_upto {Σ cmp_universe cmp_sort} d t u :
  eq_term_upto_univ Σ cmp_universe cmp_sort Conv t u ->
  check_one_fix (def_with_type d t) = check_one_fix (def_with_type d u).
Proof.
  intros eqt.
  rewrite /check_one_fix /def_with_type /=.
  have h := decompose_prod_assum_upto [] [] t u ltac:(constructor) eqt.
  do 2 destruct decompose_prod_assum.
  destruct h as [eqctx _].
  eapply (eq_context_upto_smash_context _ _ _ Conv [] []) in eqctx;
    [| intros ??; auto | intros ??; auto | constructor].
  eapply eq_context_upto_rev' in eqctx.
  have hn := eq_context_upto_nth_error _ _ _ _ _ _ (rarg d) eqctx.
  destruct (nth_error (List.rev (smash_context [] c)) (rarg d)) as [argd|],
           (nth_error (List.rev (smash_context [] c0)) (rarg d)) as [argd'|];
    depelim hn => //.
  destruct e as [[_ _] eqty].
  destruct (decompose_app (decl_type argd)) as [hd args] eqn:eqdec.
  destruct (decompose_app_upto eqty eqdec) as (hd' & tl' & -> & eqhd & napp & _).
  rewrite decompose_app_mkApps //.
  exact (destInd_mind_eq_term_upto eqhd).
Qed.

Lemma check_one_cofix_eq_term_upto {Σ cmp_universe cmp_sort} d t u :
  eq_term_upto_univ Σ cmp_universe cmp_sort Conv t u ->
  check_one_cofix (def_with_type d t) = check_one_cofix (def_with_type d u).
Proof.
  intros eqt.
  rewrite /check_one_cofix /def_with_type /=.
  have h := decompose_prod_assum_upto [] [] t u ltac:(constructor) eqt.
  do 2 destruct decompose_prod_assum.
  destruct h as [_ eqconcl].
  destruct (decompose_app t0) as [hd args] eqn:eqdec.
  destruct (decompose_app_upto eqconcl eqdec) as (hd' & tl' & -> & eqhd & napp & _).
  rewrite decompose_app_mkApps //.
  exact (destInd_mind_eq_term_upto eqhd).
Qed.

Section FixWitness.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  (** ** [check_one_fix] and [check_one_cofix] are stable under reduction *)

  Lemma check_one_fix_closed_red {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_fix (def_with_type d ty) = Some mind ->
    check_one_fix (def_with_type d v) = Some mind.
  Proof using wfΣ.
    intros r.
    rewrite {1}/check_one_fix /def_with_type /=.
    destruct (decompose_prod_assum [] ty) as [ctx concl] eqn:decomp.
    destruct (nth_error (List.rev (smash_context [] ctx)) (rarg d)) as [argd|] eqn:hnth => //.
    destruct (decompose_app (decl_type argd)) as [hd args] eqn:dapp.
    destruct (destInd hd) as [[ind u]|] eqn:di => //.
    destruct ind as [mind' k] => - [= <-].
    apply destInd_Some_eq in di; subst hd.
    apply decompose_app_inv in dapp.
    have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp; cbn in eqty.
    rewrite eqty in r.
    destruct (red_it_mkProd_or_LetIn_smash _ _ _ _ _ _ r hnth)
      as [ctx' [t' [d' [decomp' hnth' r']]]].
    rewrite /check_one_fix /def_with_type /= decomp' hnth'.
    rewrite dapp in r'.
    eapply invert_red_mkApps_tInd in r' as [args' [-> _ _]].
    now rewrite decompose_app_mkApps.
  Qed.

  Lemma check_one_cofix_closed_red {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_cofix (def_with_type d ty) = Some mind ->
    check_one_cofix (def_with_type d v) = Some mind.
  Proof using wfΣ.
    intros r.
    rewrite {1}/check_one_cofix /def_with_type /=.
    destruct (decompose_prod_assum [] ty) as [ctx concl] eqn:decomp.
    destruct (decompose_app concl) as [hd args] eqn:dapp.
    destruct (destInd hd) as [[ind u]|] eqn:di => //.
    destruct ind as [mind' k] => - [= <-].
    apply destInd_Some_eq in di; subst hd.
    apply decompose_app_inv in dapp; subst concl.
    have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp; cbn in eqty.
    rewrite eqty in r.
    destruct (red_it_mkProd_or_LetIn_mkApps_Ind r) as [ctx' [args' ->]].
    rewrite /check_one_cofix /def_with_type /=.
    rewrite decompose_prod_assum_it_mkProd; [apply is_ind_app_head_mkApps|].
    now rewrite decompose_app_mkApps.
  Qed.

  (** ** From the conversion witness to a reduction witness *)

  Lemma fix_on_ind_red Γ mind d :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    fix_on_ind Σ Γ mind d ->
    ∑ ty, (Σ ;;; Γ ⊢ dtype d ⇝ ty) × check_one_fix (def_with_type d ty) = Some mind.
  Proof using wfΣ.
    intros clΓ opd [_ [ty [hc [opty cv]]]].
    eapply convSpec_convAlgo_curry in cv; tea.
    eapply ws_cumul_pb_alt_closed in cv as [v [v' [rv rv' eq]]].
    exists v; split => //.
    rewrite (check_one_fix_eq_term_upto d _ _ eq).
    now eapply check_one_fix_closed_red.
  Qed.

  Lemma cofix_on_ind_red Γ mind d :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    cofix_on_ind Σ Γ mind d ->
    ∑ ty, (Σ ;;; Γ ⊢ dtype d ⇝ ty) × check_one_cofix (def_with_type d ty) = Some mind.
  Proof using wfΣ.
    intros clΓ opd [ty [hc [opty cv]]].
    eapply convSpec_convAlgo_curry in cv; tea.
    eapply ws_cumul_pb_alt_closed in cv as [v [v' [rv rv' eq]]].
    exists v; split => //.
    rewrite (check_one_cofix_eq_term_upto d _ _ eq).
    now eapply check_one_cofix_closed_red.
  Qed.

  (** The same, from the hypotheses a typing derivation provides. *)

  Lemma fix_on_ind_red_wf Γ mind d :
    wf_local Σ Γ -> isType Σ Γ (dtype d) ->
    fix_on_ind Σ Γ mind d ->
    ∑ ty, (check_one_fix (def_with_type d ty) = Some mind) × red Σ Γ (dtype d) ty.
  Proof using wfΣ.
    intros wfΓ isty h.
    destruct (fix_on_ind_red Γ mind d (wf_local_closed_context wfΓ)
      (isType_is_open_term isty) h) as [ty [r hc]].
    exists ty; split => //. exact (clrel_rel r).
  Qed.

  Lemma cofix_on_ind_red_wf Γ mind d :
    wf_local Σ Γ -> isType Σ Γ (dtype d) ->
    cofix_on_ind Σ Γ mind d ->
    ∑ ty, (check_one_cofix (def_with_type d ty) = Some mind) × red Σ Γ (dtype d) ty.
  Proof using wfΣ.
    intros wfΓ isty h.
    destruct (cofix_on_ind_red Γ mind d (wf_local_closed_context wfΓ)
      (isType_is_open_term isty) h) as [ty [r hc]].
    exists ty; split => //. exact (clrel_rel r).
  Qed.

  (** ** From a reduction witness back to the conversion witness *)

  Lemma red_fix_on_ind Γ mind d ty :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    has_rec_arg d ->
    check_one_fix (def_with_type d ty) = Some mind ->
    red Σ Γ (dtype d) ty ->
    fix_on_ind Σ Γ mind d.
  Proof using wfΣ.
    intros clΓ opd hr hc r.
    have cr : Σ ;;; Γ ⊢ dtype d ⇝ ty by eapply into_closed_red.
    split => //.
    exists ty; split => //; split.
    - exact (closed_red_open_right cr).
    - exact (@cumulAlgo_cumulSpec _ _ Conv _ _ _ (red_ws_cumul_pb cr)).
  Qed.

  Lemma red_cofix_on_ind Γ mind d ty :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    check_one_cofix (def_with_type d ty) = Some mind ->
    red Σ Γ (dtype d) ty ->
    cofix_on_ind Σ Γ mind d.
  Proof using wfΣ.
    intros clΓ opd hc r.
    have cr : Σ ;;; Γ ⊢ dtype d ⇝ ty by eapply into_closed_red.
    exists ty; split => //; split.
    - exact (closed_red_open_right cr).
    - exact (@cumulAlgo_cumulSpec _ _ Conv _ _ _ (red_ws_cumul_pb cr)).
  Qed.

End FixWitness.
