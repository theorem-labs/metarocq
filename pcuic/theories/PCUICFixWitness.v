(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
     PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosedTyp PCUICContexts
     PCUICSubstitution PCUICCumulativity PCUICWellScopedCumulativity
     PCUICContextConversion PCUICConversion PCUICSigmaCalculus PCUICInversion
     PCUICArities PCUICInductives.

(** * Reduction witnesses for the (co)fixpoint well-formedness conditions

  [wf_fixpoint] and [wf_cofixpoint] ask, through [mfix_on_ind], the declared type of
  each body to _convert_ to a type on which [check_one_fix] (resp. [check_one_cofix])
  finds the block. A checker, and the bidirectional system, work instead with a
  _reduct_ of the declared type. Both checks read only the shape of a type, which
  reduction and equality up to universes preserve ([ShapeCheck]); so for a
  well-scoped declared type the two witnesses agree, and this file proves both
  directions, once for any such check:

  - [mfix_body_on_conv_closed_red], [mfix_body_on_conv_red], [mfix_on_ind_conv_red],
    [mfix_on_ind_inv]: the conversion witness yields a reduction witness;
  - [mfix_body_on_red_conv], [mfix_on_ind_red_conv]: the converse, a reduct is
    convertible;
  - [mfix_body_on_red_unique]: two reduction witnesses give the same block. *)

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
  match goal with e : eq_decl_upto_gen _ _ _ _ _ _ |- _ => destruct e as [[_ _] eqty] end.
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

(** ** What [check_one_fix] and [check_one_cofix] accept *)

Lemma check_one_fix_inv d ty mind :
  check_one_fix (def_with_type d ty) = Some mind ->
  ∑ ctx concl argd i u args,
    (decompose_prod_assum [] ty = (ctx, concl)) ×
    (nth_error (List.rev (smash_context [] ctx)) (rarg d) = Some argd) ×
    (decl_type argd = mkApps (tInd {| inductive_mind := mind; inductive_ind := i |} u) args).
Proof.
  rewrite /check_one_fix /def_with_type /=.
  destruct (decompose_prod_assum [] ty) as [ctx concl] eqn:decomp.
  destruct (nth_error (List.rev (smash_context [] ctx)) (rarg d)) as [argd|] eqn:hnth => //.
  destruct (decompose_app (decl_type argd)) as [hd args] eqn:dapp.
  destruct (destInd hd) as [[[mind' i] u]|] eqn:di => //.
  move=> [= <-].
  apply destInd_Some_eq in di; subst hd.
  apply decompose_app_inv in dapp.
  exists ctx, concl, argd, i, u, args.
  repeat split; assumption.
Qed.

Lemma check_one_cofix_inv d ty mind :
  check_one_cofix (def_with_type d ty) = Some mind ->
  ∑ ctx i u args,
    ty = it_mkProd_or_LetIn ctx
      (mkApps (tInd {| inductive_mind := mind; inductive_ind := i |} u) args).
Proof.
  rewrite /check_one_cofix /def_with_type /=.
  destruct (decompose_prod_assum [] ty) as [ctx concl] eqn:decomp.
  destruct (decompose_app concl) as [hd l] eqn:da.
  destruct (destInd hd) as [[[mind' i'] u']|] eqn:di => //.
  move=> [=] <-.
  exists ctx, i', u', l.
  destruct hd => //; noconf di.
  eapply decompose_app_inv in da. subst concl.
  eapply (decompose_prod_assum_it_mkProd_or_LetIn [] ty) in decomp. now cbn in decomp.
Qed.

(** [check_one_cofix] on a telescope over an applied inductive type. *)
Lemma check_one_cofix_it_mkProd {d ctx i u l} :
  check_one_cofix (def_with_type d (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l)))
  = Some (inductive_mind i).
Proof.
  rewrite /check_one_cofix /def_with_type /=.
  rewrite decompose_prod_assum_it_mkProd; first apply is_ind_app_head_mkApps.
  cbn -[decompose_app].
  rewrite decompose_app_mkApps //.
  now destruct i.
Qed.

(** A check that reads only the shape of the declared type: it ignores the body,
    and what it finds is preserved by equality up to universes and by reduction. *)
Class ShapeCheck (check : def term -> option kername) : Prop := {
  shape_check_dbody d bo :
    check {| dname := d.(dname); dtype := d.(dtype); dbody := bo; rarg := d.(rarg) |} = check d;
  shape_check_eq_term_upto {Σ cmp_universe cmp_sort} d t u :
    eq_term_upto_univ Σ cmp_universe cmp_sort Conv t u ->
    check (def_with_type d t) = check (def_with_type d u);
  shape_check_closed_red {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check (def_with_type d ty) = Some mind ->
    check (def_with_type d v) = Some mind }.

Section FixWitness.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  (** ** [check_one_fix] and [check_one_cofix] are stable under reduction *)

  Lemma check_one_fix_closed_red {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_fix (def_with_type d ty) = Some mind ->
    check_one_fix (def_with_type d v) = Some mind.
  Proof using wfΣ.
    intros r hc.
    destruct (check_one_fix_inv _ _ _ hc)
      as (ctx & concl & argd & k & u & args & decomp & hnth & dapp).
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
    intros r hc.
    destruct (check_one_cofix_inv _ _ _ hc) as [ctx [k [u [args ->]]]].
    destruct (red_it_mkProd_or_LetIn_mkApps_Ind r) as [ctx' [args' ->]].
    exact (check_one_cofix_it_mkProd (i := {| inductive_mind := mind; inductive_ind := k |})).
  Qed.

End FixWitness.

#[export] Instance check_one_fix_shape : ShapeCheck check_one_fix :=
  @Build_ShapeCheck check_one_fix (fun d bo => ltac:(destruct d; reflexivity))
    (@check_one_fix_eq_term_upto) (@check_one_fix_closed_red).

#[export] Instance check_one_cofix_shape : ShapeCheck check_one_cofix :=
  @Build_ShapeCheck check_one_cofix (fun d bo => ltac:(destruct d; reflexivity))
    (@check_one_cofix_eq_term_upto) (@check_one_cofix_closed_red).

Section MfixWitness.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.
  Context {check : def term -> option kername} {shape : ShapeCheck check}.

  (** ** From the conversion witness to a reduction witness *)

  Lemma mfix_body_on_conv_closed_red {Γ mind d} :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    mfix_body_on check (conv_witness Σ Γ) mind d ->
    mfix_body_on check (closed_red Σ Γ) mind d.
  Proof using wfΣ shape.
    intros clΓ opd [ty [hc [opty cv]]].
    eapply convSpec_convAlgo_curry in cv; tea.
    eapply ws_cumul_pb_alt_closed in cv as [v [v' [rv rv' eq]]].
    exists v; split => //.
    rewrite (shape_check_eq_term_upto (check := check) d _ _ eq).
    exact (shape_check_closed_red (check := check) (wfΣ := wfΣ) rv' hc).
  Qed.

  (** The same, from the hypotheses a typing derivation provides. *)
  Lemma mfix_body_on_conv_red {Γ mind d} :
    wf_local Σ Γ -> isType Σ Γ (dtype d) ->
    mfix_body_on check (conv_witness Σ Γ) mind d ->
    mfix_body_on check (red Σ Γ) mind d.
  Proof using wfΣ shape.
    intros wfΓ isty h.
    destruct (mfix_body_on_conv_closed_red (wf_local_closed_context wfΓ)
      (isType_is_open_term isty) h) as [ty [hc r]].
    exists ty; split => //. exact (clrel_rel r).
  Qed.

  Lemma mfix_on_ind_conv_red {ok Γ mfix} :
    wf_local Σ Γ -> All (fun d => isType Σ Γ (dtype d)) mfix ->
    mfix_on_ind check (conv_witness Σ Γ) ok mfix ->
    mfix_on_ind check (red Σ Γ) ok mfix.
  Proof using wfΣ shape.
    intros wfΓ alltys. apply mfix_on_ind_All2; [|easy].
    apply All_All2_refl. eapply All_impl; tea. intros d isty m.
    now apply mfix_body_on_conv_red.
  Qed.

  (** A reduct of the declared type of each body passes the check and finds the
      block; the declared type itself need not pass it. *)
  Lemma mfix_on_ind_inv {ok Γ mfix idx decl} :
    is_closed_context Γ -> is_open_term Γ (dtype decl) ->
    mfix_on_ind check (conv_witness Σ Γ) ok mfix ->
    nth_error mfix idx = Some decl ->
    ∑ mind ty,
      [× Σ ;;; Γ ⊢ dtype decl ⇝ ty, check (def_with_type decl ty) = Some mind & ok mind].
  Proof using wfΣ shape.
    intros clΓ opd [mind [ne [hall hck]]] nthe.
    eapply nth_error_all in hall; tea.
    eapply mfix_body_on_conv_closed_red in hall as [ty [hc r]]; tea.
    exists mind, ty. split; tea.
  Qed.

  (** ** From a reduction witness back to the conversion witness *)

  Lemma mfix_body_on_red_conv {Γ mind d} :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    mfix_body_on check (red Σ Γ) mind d ->
    mfix_body_on check (conv_witness Σ Γ) mind d.
  Proof using wfΣ.
    intros clΓ opd [ty [hc r]].
    have cr : Σ ;;; Γ ⊢ dtype d ⇝ ty by eapply into_closed_red.
    exists ty; split => //; split.
    - exact (closed_red_open_right cr).
    - exact (@cumulAlgo_cumulSpec _ _ Conv _ _ _ (red_ws_cumul_pb cr)).
  Qed.

  Lemma mfix_on_ind_red_conv {ok Γ mfix} :
    wf_local Σ Γ -> All (fun d => isType Σ Γ (dtype d)) mfix ->
    mfix_on_ind check (red Σ Γ) ok mfix ->
    mfix_on_ind check (conv_witness Σ Γ) ok mfix.
  Proof using wfΣ.
    intros wfΓ alltys. apply mfix_on_ind_All2; [|easy].
    apply All_All2_refl. eapply All_impl; tea. intros d isty m.
    apply mfix_body_on_red_conv.
    - now eapply wf_local_closed_context.
    - now eapply isType_is_open_term.
  Qed.

  (** ** Two reducts of one declared type give the same block *)

  Lemma mfix_body_on_red_unique {Γ d m1 m2} :
    on_def_type (lift_typing1 (typing Σ)) Γ d ->
    mfix_body_on check (red Σ Γ) m1 d ->
    mfix_body_on check (red Σ Γ) m2 d ->
    m1 = m2.
  Proof using wfΣ shape.
    intros ond [ty1 [hc1 r1]] [ty2 [hc2 r2]].
    have isty : isType Σ Γ (dtype d) by now eapply isTypeRel_isType.
    have clΓ : is_closed_context Γ.
    { eapply wf_local_closed_context. now eapply isType_wf_local. }
    have op : is_open_term Γ (dtype d) by now eapply isType_is_open_term.
    have c1 : Σ ;;; Γ ⊢ dtype d ⇝ ty1 by now eapply into_closed_red.
    have c2 : Σ ;;; Γ ⊢ dtype d ⇝ ty2 by now eapply into_closed_red.
    destruct (closed_red_confluence c1 c2) as [v [rv1 rv2]].
    have e1 : check (def_with_type d v) = Some m1.
    { exact (shape_check_closed_red (check := check) (wfΣ := wfΣ) rv1 hc1). }
    have e2 : check (def_with_type d v) = Some m2.
    { exact (shape_check_closed_red (check := check) (wfΣ := wfΣ) rv2 hc2). }
    rewrite e1 in e2. now injection e2.
  Qed.

End MfixWitness.

(** ** Welltypedness of what a checker reduces to find the block *)

Lemma wf_local_nth_error_welltyped {cf : checker_flags} {Σ : global_env_ext} {Γ n c} :
  wf_local Σ Γ ->
  nth_error Γ n = Some c ->
  welltyped Σ (skipn (S n) Γ) (decl_type c).
Proof.
  induction Γ as [|a Γ ih] in n |- *; intros wf hnth.
  - now rewrite nth_error_nil in hnth.
  - depelim wf.
    + destruct n; cbn in hnth.
      * noconf hnth. rewrite skipn_S skipn_0.
        now eapply isTypeRel_welltyped.
      * rewrite skipn_S. now eapply ih.
    + destruct n; cbn in hnth.
      * noconf hnth. rewrite skipn_S skipn_0.
        apply lift_sorting_forget_body in l.
        now eapply isTypeRel_welltyped.
      * rewrite skipn_S. now eapply ih.
Qed.

(** The type of the [n]-th argument of a declared type is welltyped in the context
    of the arguments that precede it. *)
Lemma isType_rec_arg_welltyped {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ T ctx concl n c} :
  isType Σ Γ T ->
  decompose_prod_assum [] T = (ctx, concl) ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  welltyped Σ (Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c).
Proof.
  intros isty decomp hnth.
  have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp.
  cbn in eqty. rewrite eqty in isty.
  apply isType_it_mkProd_or_LetIn_wf_local in isty.
  apply wf_local_smash_end in isty.
  have hlt : n < #|smash_context [] ctx|.
  { have h := nth_error_Some_length hnth. now rewrite List.length_rev in h. }
  rewrite (nth_error_rev_inv _ _ hlt) in hnth.
  have hnth' : nth_error (Γ ,,, smash_context [] ctx) (#|smash_context [] ctx| - S n) = Some c.
  { rewrite /app_context nth_error_app_lt //. lia. }
  have w := wf_local_nth_error_welltyped isty hnth'.
  rewrite /app_context in w |- *.
  have e : S (#|smash_context [] ctx| - S n) = #|smash_context [] ctx| - n by lia.
  rewrite e skipn_app in w.
  replace (#|smash_context [] ctx| - n - #|smash_context [] ctx|) with 0 in w by lia.
  now rewrite skipn_0 in w.
Qed.

Lemma welltyped_prod_codomain {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ na A B} :
  welltyped Σ Γ (tProd na A B) -> welltyped Σ (Γ ,, vass na A) B.
Proof.
  intros [T hT]. eapply inversion_Prod in hT as (? & ? & ? & ? & ?); tea.
  now eexists.
Qed.

(** A reduct whose telescope has let-ins reduces further to one without them. *)
Lemma red_mkApps_smash_witness {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ C ctx i u l} :
  Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) ->
  ∑ l', Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (mkApps (tInd i u) l').
Proof.
  intros r.
  have clΓ := clrel_ctx r.
  have opr : is_open_term Γ (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l))
    := closed_red_open_right r.
  have h : Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) ⇝
           it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx (mkApps (tInd i u) l)).
  { now eapply red_it_mkProd_or_LetIn_to_smash. }
  rewrite expand_lets_mkApps in h.
  rewrite /expand_lets /expand_lets_k /= in h.
  eexists.
  transitivity (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l)); [exact r|exact h].
Qed.
