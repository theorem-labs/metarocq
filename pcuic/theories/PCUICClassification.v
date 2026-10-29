(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion PCUICViews
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICFixWitness PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity.

Local Existing Instance config.extraction_checker_flags.

From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation_Properties.

Set Default Proof Using "Type*".

Lemma negb_False (p : bool) : negb p -> p -> False.
Proof.
intros n pos. rewrite pos in n => //.
Qed.

(* Arities*)


Ltac destruct_sigma H :=
  repeat match type of H with
  | @sigT _ (fun x => _) => let v := fresh x in
    destruct H as (v & H); simpl in H
  | (_ × _)%type => destruct H as (? & H); simpl in H
  end.

Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args using rev_ind; simpl => //.
  - now rewrite andb_true_r.
  - now rewrite mkApps_app /= IHargs forallb_app andb_assoc /= andb_true_r.
Qed.



    Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} :
      on_free_vars P (it_mkProd_or_LetIn Δ t) =
      on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
  Proof.
    move: P. induction Δ using rev_ind => P.
    - cbn. now rewrite shiftnP0.
    - destruct x as [na [b|] ty]; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
        /on_free_vars_decl /test_decl /=. ring.
      rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /=
      /on_free_vars_decl /test_decl /=. ring.
  Qed.




(** Evaluation is a subrelation of reduction: *)

Tactic Notation "redt" uconstr(y) := eapply (CRelationClasses.transitivity (R:=red _ _) (y:=y)).

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

Fixpoint axiom_free_value Σ args t :=
  match t with
  | tApp hd arg => axiom_free_value Σ (axiom_free_value Σ [] arg :: args) hd
  | tConst kn _ => match lookup_env Σ kn with
                   | Some (ConstantDecl {| cst_body := None |}) => false
                   | _ => true
                   end
  | tCase _ _ discr _ => axiom_free_value Σ [] discr
  | tProj _ t => axiom_free_value Σ [] t
  | tFix defs i =>
    match nth_error defs i with
    | Some def => nth (rarg def) args true
    | None => true
    end
  | _ => true
  end.

Lemma axiom_free_axiom_free_value Σ t :
  axiom_free Σ ->
  axiom_free_value Σ [] t.
Proof.
  intros axfree.
  cut (Forall is_true []); [|constructor].
  generalize ([] : list bool).
  induction t using term_forall_list_ind; intros axfree_args all_true; cbn; auto.
  - destruct lookup_env eqn:find; auto.
    destruct g; auto.
    destruct c; auto.
    apply declared_constant_from_gen in find.
    apply axfree in find; cbn in *.
    now destruct cst_body0.
  - destruct nth_error; auto.
    rewrite nth_nth_error.
    destruct nth_error eqn:nth; auto.
    eapply nth_error_forall in nth; eauto.
Qed.

(** A case on a coinductive type whose return clause may mention the scrutinee has
    [ci_cofix_nondep] unset. A cofixpoint under such a case does not unfold, because
    unfolding it there breaks subject reduction, so the case stays blocked for ever.
    [stuck_cofix_case t] says that [t] is blocked by such a case: [t] is one, or [t]
    eliminates one, or [t] is a fixpoint whose recursive argument is one. *)
Inductive stuck_cofix_case : term -> Type :=
| stuck_cofix_case_scrut ci p mfix idx args brs :
    ci.(ci_cofix_nondep) = false ->
    stuck_cofix_case (tCase ci p (mkApps (tCoFix mfix idx) args) brs)
| stuck_cofix_case_app f a :
    stuck_cofix_case f ->
    stuck_cofix_case (tApp f a)
| stuck_cofix_case_case ci p c brs :
    stuck_cofix_case c ->
    stuck_cofix_case (tCase ci p c brs)
| stuck_cofix_case_proj pr c :
    stuck_cofix_case c ->
    stuck_cofix_case (tProj pr c)
| stuck_cofix_case_fix mfix idx args d arg :
    nth_error mfix idx = Some d ->
    nth_error args d.(rarg) = Some arg ->
    stuck_cofix_case arg ->
    stuck_cofix_case (mkApps (tFix mfix idx) args).
Derive Signature for stuck_cofix_case.

(** The two blocked shapes, side by side. [stuck_cofix_case] is the *syntactic shape* of
    a weak-head normal form that no head reduction can move: a case whose cofixpoint
    scrutinee does not unfold, under an elimination spine. [wcbv_stuck] is the *machine
    position*: it has the same base case, and its other constructors are exactly the
    subterms the weak call-by-value machine evaluates before it reaches the head
    ([wcbv_red1] in PCUICWcbvEval: the two sides of an application, a let's definiens, a
    case's and a projection's scrutinee, an array's default and its elements). The two
    differ: [tLetIn na b ty b'] with a blocked [b] is a machine position, while head
    reduction still unfolds the let, so it is not a weak-head normal form. *)
Inductive wcbv_stuck (Σ : global_env) : term -> Type :=
| wcbv_stuck_cofix_case ci p mfix idx args brs :
    ci.(ci_cofix_nondep) = false ->
    wcbv_stuck Σ (tCase ci p (mkApps (tCoFix mfix idx) args) brs)
| wcbv_stuck_app_l f a :
    wcbv_stuck Σ f -> wcbv_stuck Σ (tApp f a)
| wcbv_stuck_app_r f a :
    value Σ f -> wcbv_stuck Σ a -> wcbv_stuck Σ (tApp f a)
| wcbv_stuck_let na b ty b' :
    wcbv_stuck Σ b -> wcbv_stuck Σ (tLetIn na b ty b')
| wcbv_stuck_case ci p c brs :
    wcbv_stuck Σ c -> wcbv_stuck Σ (tCase ci p c brs)
| wcbv_stuck_proj pr c :
    wcbv_stuck Σ c -> wcbv_stuck Σ (tProj pr c)
| wcbv_stuck_prim_default a :
    wcbv_stuck Σ a.(array_default) -> wcbv_stuck Σ (tPrim (prim_array a))
| wcbv_stuck_prim_value a n elt :
    nth_error a.(array_value) n = Some elt ->
    wcbv_stuck Σ elt ->
    wcbv_stuck Σ (tPrim (prim_array a)).
Derive Signature for wcbv_stuck.

(** A term whose evaluation reaches a blocked case. *)
Definition reduces_to_wcbv_stuck (Σ : global_env) (t : term) :=
  ∑ w, red Σ [] t w × wcbv_stuck Σ w.

(** A blocked term has no value. *)
Lemma wcbv_stuck_no_eval {cf : checker_flags} {Σ : global_env_ext} {t} :
  wcbv_stuck Σ t -> forall u, eval Σ t u -> False.
Proof.
  induction 1; intros u ev.
  - depelim ev.
    all: try solve [ match goal with
        | h : eval _ (mkApps (tCoFix _ _) _) _ |- _ =>
          eapply eval_mkApps_tCoFix in h as [args' heq]; solve_discr
        end ].
    all: try solve [congruence].
    all: try solve [cbn in *; congruence].
  - depelim ev; eauto.
  - depelim ev; eauto.
  - depelim ev; eauto.
  - depelim ev; eauto.
  - depelim ev; eauto.
  - depelim ev; eauto.
    depelim e; eauto.
  - depelim ev; eauto.
    match goal with
    | h : eval_primitive _ _ _ |- _ => depelim h
    end.
    match goal with
    | h : All2 _ _ _ |- _ => eapply All2_nth_error_Some in h as (? & ? & ?); tea
    end.
    eauto.
Qed.

Lemma stuck_cofix_case_whne {flags Σ Γ t} :
  stuck_cofix_case t -> whne flags Σ Γ t.
Proof.
  induction 1.
  - now apply whne_case_cofix_dep.
  - now apply whne_app.
  - now apply whne_case.
  - now apply whne_proj.
  - eapply whne_fixapp; eauto.
Qed.

Lemma stuck_cofix_case_whnf {flags Σ Γ t} :
  stuck_cofix_case t -> whnf flags Σ Γ t.
Proof. intros st. constructor. now eapply stuck_cofix_case_whne. Qed.

Lemma stuck_cofix_case_mkApps t l :
  stuck_cofix_case t -> stuck_cofix_case (mkApps t l).
Proof.
  intros st. induction l in t, st |- *; cbn; auto.
  apply IHl. now apply stuck_cofix_case_app.
Qed.

Lemma stuck_cofix_case_mkApps_inv t l :
  negb (isApp t) ->
  stuck_cofix_case (mkApps t l) ->
  stuck_cofix_case t +
  ∑ mfix idx d a,
    t = tFix mfix idx ×
    nth_error mfix idx = Some d ×
    nth_error l (rarg d) = Some a ×
    stuck_cofix_case a.
Proof.
  intros Ha h. revert t Ha h.
  induction l using rev_ind; intros.
  - eauto.
  - rewrite mkApps_snoc in h.
    depelim h.
    + edestruct IHl as [ | (? & ? & ? & ? & ? & ? & ? & ?)]; eauto. subst.
      right. exists x0, x1, x2, x3. repeat split; eauto. now eapply nth_error_app_left.
    + match goal with
      | e : mkApps (tFix _ _) _ = _ |- _ => rename e into heq
      | e : _ = mkApps (tFix _ _) _ |- _ => symmetry in e; rename e into heq
      end.
      rewrite <- mkApps_snoc in heq.
      eapply (f_equal decompose_app) in heq;
        rewrite !decompose_app_mkApps in heq; cbn in *; try intuition congruence.
      inversion heq. subst.
      right. exists mfix, idx, d, arg. repeat split; eauto.
Qed.

Lemma stuck_cofix_case_head t :
  stuck_cofix_case t ->
  construct_cofix_discr (head t) = false.
Proof.
  induction 1.
  - reflexivity.
  - change (tApp f a) with (mkApps f [a]). now rewrite head_mkApps.
  - reflexivity.
  - reflexivity.
  - now rewrite head_mkApps.
Qed.

Lemma stuck_cofix_case_isConstruct_app t :
  stuck_cofix_case t -> isConstruct_app t = false.
Proof.
  intros st. apply stuck_cofix_case_head in st.
  rewrite /isConstruct_app /head in st |- *.
  destruct (decompose_app t).1 => //.
Qed.

Lemma stuck_cofix_case_not_atom t :
  stuck_cofix_case t -> atom t = false.
Proof.
  induction 1; cbn; auto.
  destruct args using rev_case.
  - match goal with
    | H : nth_error [] _ = Some _ |- _ => now rewrite nth_error_nil in H
    end.
  - rewrite mkApps_app /= //.
Qed.

Lemma value_head_not_stuck_cofix_case {Σ n f} :
  value_head Σ n f -> stuck_cofix_case f -> False.
Proof.
  intros vh st. destruct vh.
  - apply stuck_cofix_case_not_atom in st; cbn in st; discriminate.
  - apply stuck_cofix_case_not_atom in st; cbn in st; discriminate.
  - apply stuck_cofix_case_head in st; cbn in st; discriminate.
  - depelim st.
    match goal with
    | Heq : _ = mkApps (tFix _ _) ?args |- _ =>
        destruct args using rev_case;
        [ match goal with
          | Hn : nth_error [] _ = Some _ |- _ => now rewrite nth_error_nil in Hn
          end
        | rewrite mkApps_snoc in Heq; discriminate Heq ]
    end.
Qed.

Lemma value_not_stuck_cofix_case {Σ t} :
  value Σ t -> stuck_cofix_case t -> False.
Proof.
  intros val.
  induction val using value_values_ind; intros st.
  - depelim st;
    first
    [ solve [cbn in *; discriminate]
    | match goal with
      | H : is_true (PCUICWcbvEval.atom (mkApps (tFix _ _) ?args)) |- _ =>
          destruct args using rev_case;
          [ match goal with
            | Hn : nth_error [] _ = Some _ |- _ => now rewrite nth_error_nil in Hn
            end
          | rewrite mkApps_snoc in H; cbn in H; discriminate ]
      end ].
  - depelim st; solve_discr.
  - assert (Hna : ~~ isApp f) by now eapply value_head_nApp.
    apply (stuck_cofix_case_mkApps_inv _ _ Hna) in st as [st|(mfix&idx&d&a&eq&hnth&harg&sta)].
    + eapply value_head_not_stuck_cofix_case; eauto.
    + exact (nth_error_all harg X1 sta).
Qed.

Lemma red1_mkApps_tCoFix_shape Σ Γ mfix idx args t' :
  red1 Σ Γ (mkApps (tCoFix mfix idx) args) t' ->
  ∑ mfix' args', t' = mkApps (tCoFix mfix' idx) args'.
Proof.
  intros r. eapply red1_mkApps_tCoFix_inv in r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
Qed.

Lemma stuck_cofix_case_mkApps_cofix_absurd {mfix idx args} :
  stuck_cofix_case (mkApps (tCoFix mfix idx) args) -> False.
Proof.
  intros st.
  apply (stuck_cofix_case_mkApps_inv (tCoFix mfix idx) args eq_refl) in st
    as [st|(?&?&?&?&eq&?&?&?)].
  - depelim st; solve_discr.
  - discriminate eq.
Qed.

Lemma stuck_cofix_case_mkApps_construct_absurd {ind c u args} :
  stuck_cofix_case (mkApps (tConstruct ind c u) args) -> False.
Proof.
  intros st.
  apply (stuck_cofix_case_mkApps_inv (tConstruct ind c u) args eq_refl) in st
    as [st|(?&?&?&?&eq&?&?&?)].
  - depelim st; solve_discr.
  - discriminate eq.
Qed.

Lemma stuck_cofix_case_red1 {Σ Γ t t'} :
  stuck_cofix_case t -> red1 Σ Γ t t' -> stuck_cofix_case t'.
Proof.
  intros st. induction st in t' |- *; intros r.
  - depelim r; solve_discr.
    all: try (unfold is_true in *; congruence).
    all: first
      [ now apply stuck_cofix_case_scrut
      | eapply red1_mkApps_tCoFix_shape in r as (?&?&->); now apply stuck_cofix_case_scrut ].
  - depelim r; solve_discr.
    + depelim st; solve_discr.
    + exfalso.
      assert (st' : stuck_cofix_case (mkApps (tFix mfix idx) args)).
      { rewrite -H. now apply stuck_cofix_case_app. }
      apply (stuck_cofix_case_mkApps_inv (tFix mfix idx) args eq_refl) in st'
        as [st'|(?&?&?&?&eq&hnth&harg&sta)].
      * depelim st'; solve_discr;
        match goal with
        | H : nth_error [] _ = Some _ |- _ => now rewrite nth_error_nil in H
        end.
      * noconf eq.
        rewrite /unfold_fix hnth in e. noconf e.
        rewrite /is_constructor harg in e0.
        now rewrite (stuck_cofix_case_isConstruct_app _ sta) in e0.
    + now apply stuck_cofix_case_app, IHst.
    + now apply stuck_cofix_case_app.
  - depelim r; solve_discr.
    + exfalso. eapply stuck_cofix_case_mkApps_construct_absurd; eassumption.
    + exfalso. eapply stuck_cofix_case_mkApps_cofix_absurd; eassumption.
    + now apply stuck_cofix_case_case.
    + now apply stuck_cofix_case_case.
    + now apply stuck_cofix_case_case, IHst.
    + now apply stuck_cofix_case_case.
  - depelim r; solve_discr.
    + exfalso. eapply stuck_cofix_case_mkApps_cofix_absurd; eassumption.
    + exfalso. eapply stuck_cofix_case_mkApps_construct_absurd; eassumption.
    + now apply stuck_cofix_case_proj, IHst.
  - eapply red1_mkApps_tFix_inv in r.
    2:{ rewrite /unfold_fix e. rewrite /is_constructor e0.
        now rewrite (stuck_cofix_case_isConstruct_app _ st). }
    destruct r as [[(args'&->&o)|(mfix'&->&o)]|(mfix'&->&o)].
    + destruct (All_Forall.OnOne2_nth_error _ _ _ _ _ o e0) as (arg' & harg' & [eqa|ra]).
      * eapply stuck_cofix_case_fix; [exact e|exact harg'|]. now rewrite -eqa.
      * eapply stuck_cofix_case_fix; [exact e|exact harg'|]. now apply IHst.
    + destruct (All_Forall.OnOne2_nth_error _ _ _ _ _ o e) as (d' & hd' & [eqd|[rd eqf]]).
      * eapply stuck_cofix_case_fix; [exact hd'| |exact st]. now rewrite -eqd.
      * eapply stuck_cofix_case_fix; [exact hd'| |exact st].
        replace (rarg d') with (rarg d) by congruence. exact e0.
    + destruct (All_Forall.OnOne2_nth_error _ _ _ _ _ o e) as (d' & hd' & [eqd|[rd eqf]]).
      * eapply stuck_cofix_case_fix; [exact hd'| |exact st]. now rewrite -eqd.
      * eapply stuck_cofix_case_fix; [exact hd'| |exact st].
        replace (rarg d') with (rarg d) by congruence. exact e0.
Qed.

Lemma stuck_cofix_case_red {Σ Γ t t'} :
  stuck_cofix_case t -> red Σ Γ t t' -> stuck_cofix_case t'.
Proof.
  intros st r. induction r using red_rect_n1; auto.
  eapply stuck_cofix_case_red1; eauto.
Qed.


Section classification.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Notation wh_neutral := (whne RedFlags.default).
  Notation wh_normal := (whnf RedFlags.default).

  Transparent construct_cofix_discr.

  Lemma value_whnf t : closed t -> value Σ t -> wh_normal Σ [] t.
  Proof.
    intros cl ev.
    induction ev in cl |- * using value_values_ind.
    destruct t; simpl in H; try discriminate; try solve [constructor; constructor].
    - eapply (whnf_indapp _ _ [] _ _ []).
    - eapply (whnf_cstrapp _ _ [] _ _ _ []).
    - eapply (whnf_fixapp _ _ [] _ _ []).
      destruct nth_error as [rarg|] => /= //; [|easy].
      left ; eexists; split; eauto.
      now rewrite nth_error_nil.
    - eapply (whnf_cofixapp _ _ [] _ _ []).
    - eapply whnf_prim.
    - destruct X => //.
      pose proof cl as cl'.
      rewrite closedn_mkApps in cl'. move/andP: cl' => [clfix _].
      rewrite -closed_unfold_fix_cunfold_eq in e => //.
      rewrite /unfold_fix in e.
      destruct nth_error eqn:nth => //. noconf e.
      eapply whnf_fixapp. rewrite nth. left; eexists; split; eauto.
      now eapply nth_error_None.
  Qed.

  Lemma eval_whne t t' : closed t -> eval Σ t t' -> wh_normal Σ [] t'.
  Proof.
    intros cl ev.
    pose proof (eval_closed Σ _ _ cl ev).
    eapply eval_to_value in ev.
    now eapply value_whnf.
  Qed.

  Lemma typing_var {Γ n ty} : Σ ;;; Γ |- (tVar n) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Lemma typing_evar {Γ n l ty} : Σ ;;; Γ |- (tEvar n l) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.




  Lemma axiom_free_value_mkApps Σ' args hd args' :
    axiom_free_value Σ' args (mkApps hd args') =
    axiom_free_value Σ' (map (axiom_free_value Σ' []) args' ++ args) hd.
  Proof.
    revert hd args.
    induction args' using MRList.rev_ind; intros hd args; cbn; auto.
    rewrite mkApps_app /=.
    rewrite IHargs'.
    now rewrite map_app /= -app_assoc.
  Qed.

  (** A closed well-typed neutral term is blocked by a case on a cofixpoint: every other
      way of being neutral is refuted by typing in the empty context. *)
  Lemma wh_neutral_empty_gen Γ free t ty :
    axiom_free_value Σ free t ->
    wh_neutral Σ [] t ->
    Σ ;;; Γ |- t : ty ->
    Γ = [] ->
    stuck_cofix_case t.
  Proof.
    intros axfree ne typed.
    induction ne in free, t, ty, axfree, ne, typed |- *; intros ->; simpl in *; try discriminate.
    - exfalso. apply inversion_Rel in typed as (?&?&?&?); auto.
      rewrite nth_error_nil in e0; discriminate.
    - exfalso. now eapply typing_var in typed.
    - exfalso. now eapply typing_evar in typed.
    - exfalso. apply inversion_Const in typed as [decl' [wfd [declc [cu cum]]]]; eauto.
      unshelve eapply declared_constant_to_gen in declc; eauto.
      red in declc. rewrite declc in e, axfree.
      noconf e.
      destruct decl; cbn in *.
      rewrite e0 in axfree; congruence.
    - eapply inversion_App in typed as [na [A [B [Hf _]]]]; eauto.
      eapply stuck_cofix_case_app; eauto.
    - eapply inversion_mkApps in typed as (? & ? & ?); eauto.
      eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
      eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
      eapply typing_spine_strengthen in t0; eauto.
      rewrite /unfold_fix in e. rewrite e1 in e. noconf e.
      eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
      rewrite e0 in t0. destruct t0 as [ind [u [indargs [tyarg ckind]]]].
      rewrite axiom_free_value_mkApps in axfree.
      cbn in axfree.
      rewrite e1 nth_nth_error nth_error_app1 in axfree.
      1: { rewrite length_map.
           apply nth_error_Some_length in e0; auto. }
      rewrite nth_error_map e0 in axfree.
      cbn in axfree.
      eapply stuck_cofix_case_fix; [exact e1|exact e0|].
      eauto.
    - eapply inversion_Case in typed as (? & ? & ? & ? & [] & ?); tas; eauto.
      eapply stuck_cofix_case_case; eauto.
    - now eapply stuck_cofix_case_scrut.
    - eapply inversion_Proj in typed as (? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      eapply stuck_cofix_case_proj; eauto.
    (* whne_primapp_stuck / whne_primapp_inert: the head is a bodiless
       registered constant, which [axiom_free_value] sends to [false]. *)
    - rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
    - rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
  Qed.

  Lemma wh_neutral_empty t ty :
    axiom_free_value Σ [] t ->
    wh_neutral Σ [] t ->
    Σ ;;; [] |- t : ty ->
    stuck_cofix_case t.
  Proof. eauto using wh_neutral_empty_gen. Qed.

  Lemma whnf_classification' t i u args :
    axiom_free_value Σ [] t ->
    wh_normal Σ [] t ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t) + stuck_cofix_case t.
  Proof.
    intros axfree ne typed.
    pose proof (subject_closed typed) as cl.
    depelim ne; simpl in *.
    - right. eauto using wh_neutral_empty.
    - eapply inversion_Sort in typed as (? & ? & e); auto.
      now eapply invert_cumul_sort_ind in e.
    - eapply inversion_Prod in typed as (? & ? & ? & ? & e); auto.
      now eapply invert_cumul_sort_ind in e.
    - eapply inversion_Lambda in typed as (? & ? & ? & e); auto.
      now eapply invert_cumul_prod_ind in e.
    - left. now rewrite head_mkApps /= /head /=.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct nth_error; [|easy].
      destruct o as [[? [? ?]]|]; [|easy]. inversion H; eauto.
    - left. now rewrite head_mkApps /head /=.
    - eapply inversion_Prim in typed as [prim_ty [cdecl [? hpc ? ? hp]]]; eauto.
      (* The guard on the axiom inversions: prim_ty is a registered primitive
         TYPE constant, which §4.2(a)1 keeps out of the operation table. *)
      assert (hnop : prim_op_of Σ prim_ty = None).
      { pose proof wfΣ as [_ [wfr _]].
        exact (prim_op_of_primitive_constant _ _ _ wfr hpc). }
      destruct p as [? []]; simp prim_type in w.
      1-3:eapply (invert_cumul_axiom_ind (args := [])) in w; eauto; destruct p0 as [? []]; eauto.
      eapply (invert_cumul_axiom_ind (args := [array_type a0])) in w; eauto. destruct p0 as [s []]; eauto.
    (* whnf_primapp_partial / whnf_primapp_rigid: the head is a bodiless
       registered constant, which [axiom_free_value] sends to [false]. *)
    - exfalso. rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
    - exfalso. rewrite axiom_free_value_mkApps in axfree; cbn in axfree.
      match goal with H : lookup_env _ _ = Some (ConstantDecl ?d) |- _ => rewrite H in axfree end.
      match goal with H : cst_body ?d = None |- _ => destruct d; cbn in *; subst; discriminate axfree end.
  Qed.

  Lemma whnf_classification t i u args :
    axiom_free Σ ->
    wh_normal Σ [] t ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    construct_cofix_discr (head t) + stuck_cofix_case t.
  Proof.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply whnf_classification'; eauto.
  Qed.

  Definition notCoInductive Σ ind :=
    ~check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.

  Lemma ind_whnf_classification' t ind u indargs :
    axiom_free_value Σ [] t -> notCoInductive Σ ind ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t + stuck_cofix_case t.
  Proof.
    intros axfree ck typed whnf.
    eapply whnf_classification' in whnf; eauto.
    destruct whnf as [whnf|st]; [|now right].
    left. rewrite /isConstruct_app.
    rewrite /head in whnf.
    destruct (decompose_app t) as [hd tl] eqn:da; simpl in *.
    destruct hd eqn:eqh => //. subst hd.
    eapply decompose_app_inv in da. subst.
    eapply typing_cofix_coind in typed.
    congruence.
  Qed.

  Lemma ind_whnf_classification t ind u indargs :
    axiom_free Σ -> notCoInductive Σ ind ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    isConstruct_app t + stuck_cofix_case t.
  Proof.
    intros axfree; eapply axiom_free_axiom_free_value in axfree.
    intros; eapply ind_whnf_classification'; eauto.
  Qed.

  Lemma fix_app_is_constructor {mfix idx args ty narg fn} :
    Σ;;; [] |- mkApps (tFix mfix idx) args : ty ->
    unfold_fix mfix idx = Some (narg, fn) ->
    match nth_error args narg return Type with
    | Some a => axiom_free_value Σ [] a -> wh_normal Σ [] a -> isConstruct_app a + stuck_cofix_case a
    | None => ∑ na dom codom, Σ ;;; [] ⊢ tProd na dom codom ≤ ty
    end.
  Proof.
    intros typed unf.
    eapply inversion_mkApps in typed as (? & ? & ?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
    eapply typing_spine_strengthen in t0; eauto.
    rewrite /unfold_fix in unf. rewrite e in unf.
    noconf unf.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite /is_constructor. destruct (nth_error args (rarg x0)) eqn:hnth; [|assumption].
    destruct_sigma t0.
    intros axfree norm.
    eapply ind_whnf_classification' in t1; eauto.
    intros chk.
    pose proof (check_recursivity_kind_inj chk t0).
    discriminate.
  Qed.


  Lemma value_axiom_free Σ' t :
    value Σ' t ->
    axiom_free_value Σ' [] t.
  Proof.
    intros val.
    induction val using value_values_ind.
    - destruct t; try discriminate; auto.
      cbn.
      destruct ?; auto.
      destruct ?; auto.
    - cbn. constructor.
    - rewrite axiom_free_value_mkApps.
      rewrite app_nil_r.
      destruct X; try constructor.
      cbn.
      unfold isStuckFix, cunfold_fix in e.
      destruct nth_error; auto.
      rewrite nth_overflow; auto. len. now noconf e.
  Qed.

  (** Evaluation on well-typed terms corresponds to reduction.
      It differs in two ways from standard reduction:
      - using closed substitution operations applicable only on closed terms
      - it does not check that fixpoints that are applied to enough arguments
        have a constructor at their recursive argument as it is ensured by typing
        + classification. *)

  Import PCUICGlobalEnv.

  Lemma wcbveval_red t ty u :
    Σ ;;; [] |- t : ty ->
    eval Σ t u -> red Σ [] t u.
  Proof.
    intros Hc He.
    revert ty Hc.
    induction He; simpl; move=> ty Ht;
      try solve[econstructor; eauto].

    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      redt (tApp (tLambda na t b) a); eauto.
      eapply red_app; eauto.
      redt (tApp (tLambda na t b) a'). eapply red_app; eauto.
      specialize (IHHe1 _ t0). specialize (IHHe2 _ t1).
      redt (csubst a' 0 b).
      rewrite (closed_subst a' 0 b).
      eapply eval_closed; eauto. now eapply subject_closed in t1.
      eapply red1_red. constructor.
      pose proof (subject_closed t1); auto.
      eapply eval_closed in H; eauto.
      eapply subject_reduction in IHHe1. 2-3:eauto.
      eapply inversion_Lambda in IHHe1 as (? & ? & ? & e); eauto.
      eapply (substitution0 (Γ := [])) in t2; eauto.
      eapply IHHe3.
      rewrite (closed_subst a' 0 b); auto.
      rewrite /subst1 in t2. eapply t2.
      eapply (type_ws_cumul_pb (pb:=Conv)); eauto.
      eapply subject_reduction in IHHe2; eauto.
      now eapply isTypeRel_isType.
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna dom codom]; eauto.
      now symmetry.

    - eapply inversion_LetIn in Ht as (? & ? & ? & ?); auto.
      apply unlift_TermTyp in l as t0'.
      redt (tLetIn na b0' t b1); eauto.
      eapply red_letin; eauto.
      redt (b1 {0 := b0'}); auto.
      do 2 econstructor.
      specialize (IHHe1 _ t0').
      rewrite /subst1.
      rewrite -(closed_subst b0' 0 b1).
      eapply subject_reduction in t0'; eauto. eapply subject_closed in t0'; eauto.
      eapply IHHe2.
      rewrite closed_subst.
      eapply subject_reduction in t0'; eauto. eapply subject_closed in t0'; eauto.
      pose proof (subject_is_open_term t0).
      eapply substitution_let in t0; eauto.
      eapply subject_reduction in t0.
      3:{ eapply (red_red (Δ := [vass na t]) (Γ' := [])); eauto. 3:repeat constructor.
          cbn. rewrite addnP_shiftnP. eapply type_is_open_term in t0'. now erewrite t0'.
          repeat constructor. cbn. rewrite addnP_shiftnP.
          eapply subject_is_open_term in t0'. cbn in t0'. now setoid_rewrite shiftnP0 in t0'. }
      apply t0. auto.

    - redt (subst_instance u body); auto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.
      eapply IHHe. eapply subject_reduction; eauto.
      eapply red1_red. econstructor; eauto.
      apply declared_constant_from_gen; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Case in Ht; auto. destruct_sigma Ht.
      unshelve epose proof (isdecl_ := declared_inductive_to_gen isdecl); eauto.
      destruct (declared_inductive_inj d isdecl_); subst mdecl0 idecl0.
      destruct c0.
      specialize (IHHe1 _ scrut_ty).
      assert (red Σ [] (tCase ci p discr brs) (iota_red ci.(ci_npar) p args br)).
      { clear X. redt _.
        eapply red_case; eauto.
        eapply All2_refl; intros; eauto. red.
        eapply All2_refl; split; reflexivity.
        eapply red1_red. destruct p => /= //.
        eapply red_iota; tea.
        rewrite e1 /cstr_arity eq_npars e3 //. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Proj in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      assert (red Σ [] (tProj p discr) a).
      { redt _.
        eapply red_proj_c; eauto.
        eapply red1_red; constructor; auto. }
      specialize (X X0).
      redt _; eauto.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_App in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      epose proof (subject_reduction Σ [] _ _ _ wfΣ t IHHe1) as Ht2.
      epose proof (subject_reduction Σ [] _ _ _ wfΣ t0 IHHe2) as Ha2.
      assert (red Σ [] (tApp f4 a) (tApp (mkApps fn argsv) av)).
      { redt _.
        eapply red_app; eauto.
        rewrite -![tApp _ _](mkApps_app _ _ [_]).
        eapply red1_red.
        rewrite -closed_unfold_fix_cunfold_eq in e1.
        { eapply subject_closed in Ht2; auto.
          rewrite closedn_mkApps in Ht2. now move/andP: Ht2 => [clf _]. }
        eapply red_fix; eauto.
        assert (Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : B {0 := av}).
        { rewrite mkApps_app /=. eapply type_App'; eauto. }
        epose proof (fix_app_is_constructor X0 e1); eauto.
        rewrite /is_constructor.
        destruct nth_error eqn:hnth => //.
        2:{ eapply nth_error_None in hnth. len in hnth. }
        assert (All (closedn 0) (argsv ++ [av])).
        { eapply subject_closed in X0; eauto.
          rewrite closedn_mkApps in X0.
          move/andP: X0 => [clfix clargs].
          now eapply forallb_All in clargs. }
        assert (All (value Σ) (argsv ++ [av])).
        { eapply All_app_inv; [|constructor; [|constructor]].
          eapply eval_to_value in He1.
          eapply value_mkApps_inv in He1 as [[-> Hat]|[vh vargs]] => //.
          now eapply eval_to_value in He2. }
        solve_all.
        eapply nth_error_all in X3; eauto. simpl in X3.
        destruct X3 as [cl val].
        forward X1. { now eapply value_axiom_free. }
        forward X1. { eapply value_whnf; auto. }
        destruct X1 as [hc|st]; [exact hc|].
        exfalso. eapply value_not_stuck_cofix_case; eauto. }
      redt _; eauto.

    - apply inversion_App in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      specialize (IHHe2 _ t0).
      now eapply red_app.

    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Case in Ht; auto; destruct_sigma Ht.
      destruct c.
      specialize (IHHe1 _ scrut_ty).
      unshelve epose proof (subject_reduction Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closed X0).
      etransitivity. eapply red_case_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)).
      { eapply red1_red. eapply red_cofix_case; [assumption|].
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
      redt _; eauto.
      eapply IHHe2.
      eapply subject_reduction. 3: eapply X1. eauto.
      eapply subject_reduction. 3: eapply red_case_c; eauto. all:eauto.
    - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
      apply inversion_Proj in Ht; auto; destruct_sigma Ht.
      specialize (IHHe1 _ t).
      unshelve epose proof (subject_reduction Σ [] _ _ _ wfΣ _ IHHe1). 2:eauto.
      pose proof (subject_closed X0).
      etransitivity. eapply red_proj_c. eapply IHHe1; eauto.
      rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
      assert (red Σ [] (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))).
      { eapply red1_red. eapply red_cofix_proj.
        rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
        redt _; eauto.
      eapply IHHe2.
      eapply subject_reduction. 3: eapply X1. eauto.
      eapply subject_reduction. 3: eapply red_proj_c; eauto. all:eauto.

    - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      rewrite mkApps_app /=. now eapply red_app.

    - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
      specialize (IHHe1 _ Hf).
      specialize (IHHe2 _ Ha).
      now eapply red_app.

    - eapply inversion_Prim in Ht as [prim_type [decl []]]; eauto.
      depelim X. 1-3:reflexivity.
      depelim p1. specialize (r _ hdef).
      eapply red_primArray_congr; eauto.
      eapply All2_undep in a. solve_all.
  Qed.

  Theorem subject_reduction_eval {t u T} :
    Σ ;;; [] |- t : T -> eval Σ t u -> Σ ;;; [] |- u : T.
  Proof.
    intros Hty Hred.
    eapply wcbveval_red in Hred; eauto. eapply subject_reduction; eauto.
  Qed.

  (** A value is never blocked by a case on a cofixpoint, so classification keeps its
      shape on values. *)
  Lemma value_classification {t i u args} :
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    value Σ t ->
    construct_cofix_discr (head t).
  Proof.
    intros Ht Hvalue.
    eapply value_axiom_free in Hvalue as H.
    assert (hnorm : wh_normal Σ [] t).
    { eapply eval_whne.
      2: eapply value_final; eauto.
      eapply @subject_closed with (Γ := []); eauto. }
    eapply whnf_classification' in hnorm as [hd|st]; eauto.
    exfalso. eapply value_not_stuck_cofix_case; eauto.
  Qed.

  Lemma eval_classification {t i u args} :
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    forall t', eval Σ t t' ->
    construct_cofix_discr (head t').
  Proof.
    intros Ht t' ev.
    pose proof (subject_closed Ht).
    assert (hval : value Σ t') by (eapply eval_to_value; eauto).
    eapply subject_reduction in Ht. 3:eapply wcbveval_red; eauto. 2:auto.
    eapply value_axiom_free in hval as axfree.
    eapply eval_whne in ev; auto.
    eapply whnf_classification' in ev as [hd|st]; eauto.
    exfalso. eapply value_not_stuck_cofix_case; eauto.
  Qed.

End classification.

(* Print Assumptions eval_ind_canonical. *)
