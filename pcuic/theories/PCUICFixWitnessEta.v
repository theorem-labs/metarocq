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
     PCUICArities PCUICInductives PCUICFixWitness
     PCUICConfluence PCUICClosedBodies PCUICCumulativitySpecEta PCUICTypingEta
     PCUICTypingEtaNotions PCUICClosedTypEta PCUICWellScopedCumulativityEta
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICInversionEta PCUICSREtaConv.

(** * Reduction witnesses for the (co)fixpoint well-formedness conditions over [typingE]

  The E copy of [PCUICFixWitness]. Each declaration of the base file that mentions typing,
  [wf_local], [wf], [isType], [welltyped] or the conversion witness (in its statement, or through
  the [wf] variable of its section) is copied; its E name is the base name with the suffix [E],
  and its statement is the base statement with only the relations renamed: [typing] →
  [typingE], [wf_local] → [wf_localE], [wf] → [wfE], [isType] → [isTypeE], [welltyped] →
  [welltypedE], [conv_witness] → [conv_witnessE], [ShapeCheck] → [ShapeCheckE] (here).
  Reduction ([Σ ;;; Γ ⊢ t ⇝ u], [red]) and [eq_term_upto_univ] are unchanged. Implicit status,
  binder names and positions are base's; section premises are base's ([Proof using] kept), and
  so is the file's [Implicit Types] (only [cf]).

  The class [ShapeCheckE] (fields [shape_check_dbodyE], [shape_check_eq_term_uptoE],
  [shape_check_closed_redE]) is base's [ShapeCheck] with [wf Σ] → [wfE Σ] in its third field;
  [check_one_fix_shapeE] and [check_one_cofix_shapeE] are export instances, as base's. The first
  two fields read no environment: their proofs are base's relation-free lemmas
  [check_one_fix_eq_term_upto] and [check_one_cofix_eq_term_upto], used as they are.

  [mfix_body_on_red_convE] and [mfix_on_ind_red_convE] state exactly the statements of
  [Bidirectional/BDTypingEta.v], compiled form included (names, binder order and types, the
  section premise [{cb : ClosedBodies Σ}] of the first and the premises [{wfΣ : wfE Σ}],
  [wf_localE] and [on_type (lift_typing typingE)] of the second). The first is NOT a twin in its
  premise: base's [wf Σ] is replaced by [ClosedBodies Σ] (weaker, a reduction fact), so the E
  statement is stronger than the twin; its binder [Γ : context] is written, as [BDTypingEta.v]
  infers it, where base infers [list context_decl] (the same type by delta). The second spells
  base's [isType] as its body [on_type (lift_typing typingE)], which is [isTypeE] by delta.

  Proof routes that differ from base (statements are twins):
  - [check_one_fix_closed_redE], [check_one_cofix_closed_redE]: the [ClosedBodies] forms
    [red_it_mkProd_or_LetIn_smash_cb] ([PCUICSREtaConv]), [invert_red_mkApps_tInd_cb]
    ([PCUICConversion]) and [red_it_mkProd_or_LetIn_mkApps_Ind_cb] ([PCUICInductives]), through
    [wfE_ClosedBodies];
  - [mfix_body_on_red_convE]: the reduction is a [ws_cumul_pbE] ([red_ws_cumul_pbE]), hence a
    [convSpecE] ([ws_cumul_pbE_forget_spec], the canonical join's specification bridge), where
    base goes through [cumulAlgo_cumulSpec];
  - [mfix_body_on_red_uniqueE]: base's [closed_red_confluence] needs [wf Σ]; its two-line proof
    is replayed on [red_confluence_cb] ([PCUICConfluence], [ClosedBodies]);
  - [red_mkApps_smash_witnessE]: base's [red_it_mkProd_or_LetIn_to_smash] carries [wf Σ], which
    its proof does not use, and no E form of it is on this tree; its proof is replayed inline.

  Not copied:
  - the declarations that mention none of the relations (used from base, which this file
    imports): [destInd_mind_eq_term_upto], [check_one_fix_eq_term_upto],
    [check_one_cofix_eq_term_upto], [check_one_fix_inv], [check_one_cofix_inv],
    [check_one_cofix_it_mkProd], [has_rec_arg_nth_error];
  - [mfix_body_on_conv_closed_red] and [mfix_on_ind_inv]: their E forms (premises
    [is_closed_context] and [is_open_term] only) are FALSE, refuted in
    [PCUICFixWitnessEtaCounter.v] ([mfix_body_on_conv_closed_redE_fix_false],
    [mfix_body_on_conv_closed_redE_cofix_false], [mfix_body_on_conv_closed_redE_false]);
  - [mfix_body_on_conv_red] and [mfix_on_ind_conv_red]: their base proofs go through
    [mfix_body_on_conv_closed_red]. Over η the conversion witness gives a reduction witness only
    for a TYPED declared type, by a typed reduct lemma proved with subject reduction over
    [typingE]; that route reads the structure of [check_one_fix] / [check_one_cofix], so it is
    stated per check, not over a [ShapeCheckE] class, and lives with subject reduction. *)

Implicit Types (cf : checker_flags).

(** A check that reads only the shape of the declared type: it ignores the body,
    and what it finds is preserved by equality up to universes and by reduction. *)
Class ShapeCheckE (check : def term -> option kername) : Prop := {
  shape_check_dbodyE d bo :
    check {| dname := d.(dname); dtype := d.(dtype); dbody := bo; rarg := d.(rarg) |} = check d;
  shape_check_eq_term_uptoE {Σ cmp_universe cmp_sort} d t u :
    eq_term_upto_univ Σ cmp_universe cmp_sort Conv t u ->
    check (def_with_type d t) = check (def_with_type d u);
  shape_check_closed_redE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check (def_with_type d ty) = Some mind ->
    check (def_with_type d v) = Some mind }.

Section FixWitness.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** ** [check_one_fix] and [check_one_cofix] are stable under reduction *)

  Lemma check_one_fix_closed_redE {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_fix (def_with_type d ty) = Some mind ->
    check_one_fix (def_with_type d v) = Some mind.
  Proof using wfΣ.
    intros r hc.
    destruct (check_one_fix_inv _ _ _ hc)
      as (ctx & concl & argd & k & u & args & decomp & hnth & dapp).
    have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp; cbn in eqty.
    rewrite eqty in r.
    destruct (red_it_mkProd_or_LetIn_smash_cb _ _ _ _ _ _ r hnth)
      as [ctx' [t' [d' [decomp' hnth' r']]]].
    rewrite /check_one_fix /def_with_type /= decomp' hnth'.
    rewrite dapp in r'.
    eapply invert_red_mkApps_tInd_cb in r' as [args' [-> _ _]].
    now rewrite decompose_app_mkApps.
  Qed.

  Lemma check_one_cofix_closed_redE {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_cofix (def_with_type d ty) = Some mind ->
    check_one_cofix (def_with_type d v) = Some mind.
  Proof using wfΣ.
    intros r hc.
    destruct (check_one_cofix_inv _ _ _ hc) as [ctx [k [u [args ->]]]].
    destruct (red_it_mkProd_or_LetIn_mkApps_Ind_cb r) as [ctx' [args' ->]].
    exact (check_one_cofix_it_mkProd (i := {| inductive_mind := mind; inductive_ind := k |})).
  Qed.

End FixWitness.

#[export] Instance check_one_fix_shapeE : ShapeCheckE check_one_fix :=
  @Build_ShapeCheckE check_one_fix (fun d bo => ltac:(destruct d; reflexivity))
    (@check_one_fix_eq_term_upto) (@check_one_fix_closed_redE).

#[export] Instance check_one_cofix_shapeE : ShapeCheckE check_one_cofix :=
  @Build_ShapeCheckE check_one_cofix (fun d bo => ltac:(destruct d; reflexivity))
    (@check_one_cofix_eq_term_upto) (@check_one_cofix_closed_redE).

(** ** From a reduction witness back to the conversion witness *)

Section FixWitnessRedConv.
  Context {cf : checker_flags} {Σ : global_env_ext} {cb : ClosedBodies Σ}.

  (** [BDTypingEta.v] writes [{check Γ mind d}] under its [Implicit Types (Γ : context)]; this file
      keeps base's [Implicit Types], so the binder type is written. *)
  Lemma mfix_body_on_red_convE {check} {Γ : context} {mind d} :
    is_closed_context Γ -> is_open_term Γ (dtype d) ->
    mfix_body_on check (red Σ Γ) mind d ->
    mfix_body_on check (conv_witnessE Σ Γ) mind d.
  Proof using cb.
    intros clΓ opd [ty [hc r]].
    have cr : Σ ;;; Γ ⊢ dtype d ⇝ ty by eapply into_closed_red.
    exists ty; split => //; split.
    - exact (closed_red_open_right_cb cr).
    - exact (ws_cumul_pbE_forget_spec (red_ws_cumul_pbE (pb := Conv) cr)).
  Qed.

End FixWitnessRedConv.

Lemma mfix_on_ind_red_convE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {check ok Γ mfix} :
  wf_localE Σ Γ -> All (fun d => on_type (lift_typing typingE) Σ Γ (dtype d)) mfix ->
  mfix_on_ind check (red Σ Γ) ok mfix ->
  mfix_on_ind check (conv_witnessE Σ Γ) ok mfix.
Proof.
  intros wfΓ alltys. apply mfix_on_ind_All2; [|easy].
  apply All_All2_refl. eapply All_impl; tea. intros d isty m.
  apply mfix_body_on_red_convE.
  - now eapply wf_local_closed_contextE.
  - now eapply isType_is_open_termE.
Qed.

Section MfixWitness.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.
  Context {check : def term -> option kername} {shape : ShapeCheckE check}.

  (** ** Two reducts of one declared type give the same block *)

  Lemma mfix_body_on_red_uniqueE {Γ d m1 m2} :
    on_def_type (lift_typing1 (typingE Σ)) Γ d ->
    mfix_body_on check (red Σ Γ) m1 d ->
    mfix_body_on check (red Σ Γ) m2 d ->
    m1 = m2.
  Proof using wfΣ shape.
    intros ond [ty1 [hc1 r1]] [ty2 [hc2 r2]].
    have isty : isTypeE Σ Γ (dtype d) by now eapply isTypeRelE_isTypeE.
    have clΓ : is_closed_context Γ.
    { eapply wf_local_closed_contextE. now eapply isType_wf_localE. }
    have op : is_open_term Γ (dtype d) by now eapply isType_is_open_termE.
    have c1 : Σ ;;; Γ ⊢ dtype d ⇝ ty1 by now eapply into_closed_red.
    have c2 : Σ ;;; Γ ⊢ dtype d ⇝ ty2 by now eapply into_closed_red.
    have [v [rv1 rv2]] : ∑ v', Σ ;;; Γ ⊢ ty1 ⇝ v' × Σ ;;; Γ ⊢ ty2 ⇝ v'.
    { have op1 : is_open_term Γ ty1 by exact (closed_red_open_right_cb c1).
      have op2 : is_open_term Γ ty2 by exact (closed_red_open_right_cb c2).
      destruct (red_confluence_cb (Γ := exist Γ clΓ) (t := exist (dtype d) op)
        (clrel_rel c1) (clrel_rel c2)) as [v' [redl redr]].
      cbn in redl, redr. exists v'; split; eapply into_closed_red; tea. }
    have e1 : check (def_with_type d v) = Some m1.
    { exact (shape_check_closed_redE (check := check) (wfΣ := wfΣ) rv1 hc1). }
    have e2 : check (def_with_type d v) = Some m2.
    { exact (shape_check_closed_redE (check := check) (wfΣ := wfΣ) rv2 hc2). }
    rewrite e1 in e2. now injection e2.
  Qed.

End MfixWitness.

(** ** Welltypedness of what a checker reduces to find the block *)

Lemma wf_local_nth_error_welltypedE {cf : checker_flags} {Σ : global_env_ext} {Γ n c} :
  wf_localE Σ Γ ->
  nth_error Γ n = Some c ->
  welltypedE Σ (skipn (S n) Γ) (decl_type c).
Proof.
  induction Γ as [|a Γ ih] in n |- *; intros wf hnth.
  - now rewrite nth_error_nil in hnth.
  - depelim wf.
    + destruct n; cbn in hnth.
      * noconf hnth. rewrite skipn_S skipn_0.
        now eapply isTypeRelE_welltypedE.
      * rewrite skipn_S. now eapply ih.
    + destruct n; cbn in hnth.
      * noconf hnth. rewrite skipn_S skipn_0.
        apply lift_sorting_forget_body in l.
        now eapply isTypeRelE_welltypedE.
      * rewrite skipn_S. now eapply ih.
Qed.

(** The type of the [n]-th argument of a declared type is welltyped in the context
    of the arguments that precede it. *)
Lemma isType_rec_arg_welltypedE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ T ctx concl n c} :
  isTypeE Σ Γ T ->
  decompose_prod_assum [] T = (ctx, concl) ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  welltypedE Σ (Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c).
Proof.
  intros isty decomp hnth.
  have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp.
  cbn in eqty. rewrite eqty in isty.
  apply isType_it_mkProd_or_LetIn_wf_localE in isty.
  apply wf_local_smash_endE in isty.
  have hlt : n < #|smash_context [] ctx|.
  { have h := nth_error_Some_length hnth. now rewrite List.length_rev in h. }
  rewrite (nth_error_rev_inv _ _ hlt) in hnth.
  have hnth' : nth_error (Γ ,,, smash_context [] ctx) (#|smash_context [] ctx| - S n) = Some c.
  { rewrite /app_context nth_error_app_lt //. lia. }
  have w := wf_local_nth_error_welltypedE isty hnth'.
  rewrite /app_context in w |- *.
  have e : S (#|smash_context [] ctx| - S n) = #|smash_context [] ctx| - n by lia.
  rewrite e skipn_app in w.
  replace (#|smash_context [] ctx| - n - #|smash_context [] ctx|) with 0 in w by lia.
  now rewrite skipn_0 in w.
Qed.

Lemma welltyped_prod_codomainE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na A B} :
  welltypedE Σ Γ (tProd na A B) -> welltypedE Σ (Γ ,, vass na A) B.
Proof.
  intros [T hT]. eapply inversion_ProdE in hT as (? & ? & ? & ? & ?); tea.
  now eexists.
Qed.

(** A reduct whose telescope has let-ins reduces further to one without them. *)
Lemma red_mkApps_smash_witnessE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ C ctx i u l} :
  Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) ->
  ∑ l', Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (mkApps (tInd i u) l').
Proof.
  intros r.
  have clΓ := clrel_ctx r.
  have opr : is_open_term Γ (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l))
    by exact (closed_red_open_right_cb r).
  (* base's [red_it_mkProd_or_LetIn_to_smash], whose [wf Σ] premise its proof does not use *)
  have h : Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) ⇝
           it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx (mkApps (tInd i u) l)).
  { eapply into_closed_red => //.
    clear r opr clΓ.
    move: (mkApps (tInd i u) l) => T.
    induction ctx in Γ, T |- * using PCUICInduction.ctx_length_rev_ind; simpl; auto.
    - rewrite expand_lets_nil. reflexivity.
    - rewrite smash_context_app_expand /=.
      destruct d as [na [b|] ty].
      * rewrite expand_lets_vdef {1}it_mkProd_or_LetIn_app /= subst_context_nil app_context_nil_l.
        rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil.
        rewrite /expand_lets_ctx /expand_lets_k_ctx /= subst_empty lift0_id lift0_context.
        rewrite /mkProd_or_LetIn /=.
        etransitivity.
        + eapply red1_red, red_zeta.
        + rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
          now eapply X; len.
      * rewrite expand_lets_vass it_mkProd_or_LetIn_app /=.
        rewrite it_mkProd_or_LetIn_app /=.
        eapply red_prod. reflexivity.
        rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil.
        rewrite expand_lets_ctx_assumption_context. repeat constructor.
        now eapply X. }
  rewrite expand_lets_mkApps in h.
  rewrite /expand_lets /expand_lets_k /= in h.
  eexists.
  transitivity (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l)); [exact r|exact h].
Qed.
