(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Stdlib Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config Universes BasicAst Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICOnOne PCUICCases
     PCUICContextReduction PCUICEquality PCUICLiftSubst PCUICTyping PCUICWeakeningEnvConv
     PCUICWeakeningEnvTyp PCUICReduction PCUICClosedTyp PCUICPrimitiveRed
     PCUICInduction PCUICRedTypeIrrelevance PCUICOnFreeVars PCUICEtaExpand.
From Stdlib Require Import ssreflect ssrbool.
Set Asymmetric Patterns.

(* Require Import Equations.Type.DepElim. *)

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.
  Definition nodelta := mk true true true false true true.
  (** kernel/redFlags.ml [allnolet]: every reduction but zeta. *)
  Definition allnolet := mk true true false true true true.

End RedFlags.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

(** * Primitive-operation redexes

  [split_lits], [lits_of_args] and [prim_reduct] are
  [PCUICPrimitiveRed]'s: the machine ([PCUICSafeReduce]), the machine's graph
  ([PCUICArityRed]) and the weak-head forms here all ask the same two
  questions, so they are answered once, beside [lit_of_term].  [prim_reduct Σ
  op args] is the reduct of [mkApps (tConst c u) args] by [red_prim_op] when
  the rule fires, and [None] when it does not.  It mentions only [Σ], never a
  context or the reduction flags, so the machine and conversion can build it
  from a computed [option term]. *)

(** Every operation in the table takes at least one argument, so none fires on
    an empty argument list: a bare registered constant is a normal form.  This
    is what keeps [ne_const] (and its [nf_no_red]) true without a guard. *)
Lemma prim_op_denote_nil op : prim_op_denote op [] = None.
Proof. destruct op; reflexivity. Qed.

(** A literal argument is irreducible, so a saturated application of literals
    has no reduction but the rule's own. *)
Lemma red1_term_of_lit Σ Γ l t' : red1 Σ Γ (term_of_lit l) t' -> False.
Proof.
  rewrite /term_of_lit; destruct l; cbn; intros r; depelim r; solve_discr.
Qed.

Lemma OnOne2_map_term_of_lit Σ Γ ls args' :
  OnOne2 (red1 Σ Γ) (map term_of_lit ls) args' -> False.
Proof.
  induction ls as [|l ls ih] in args' |- *; cbn; intros o; depelim o.
  - now eapply red1_term_of_lit.
  - now eapply ih.
Qed.

Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  (* Relative to reduction flags *)
  Inductive whne (Γ : context) : term -> Type :=
  | whne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      whne Γ (tRel i)

  | whne_lam_nobeta na A b :
      RedFlags.beta flags = false ->
      whne Γ (tLambda na A b)

  | whne_var v :
      whne Γ (tVar v)

  | whne_evar n l :
      whne Γ (tEvar n l)

  | whne_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t)

  | whne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      prim_op_of Σ c = None ->
      whne Γ (tConst c u)

  | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u)

  | whne_app f v :
      whne Γ f ->
      whne Γ (tApp f v)

  (* Stuck fixpoints are neutrals *)
  | whne_fixapp mfix idx args d arg :
     nth_error mfix idx = Some d ->
     nth_error args (rarg d) = Some arg ->
     whne Γ arg ->
     whne Γ (mkApps (tFix mfix idx) args)

  | whne_fix_nofix defs i :
      RedFlags.fix_ flags = false ->
      whne Γ (tFix defs i)

  | whne_case i p c brs :
      whne Γ c ->
      whne Γ (tCase i p c brs)

  | whne_case_noiota i p c brs :
      RedFlags.iota flags = false ->
      whne Γ (tCase i p c brs)

  | whne_proj p c :
      whne Γ c ->
      whne Γ (tProj p c)

  | whne_proj_noiota p c :
      RedFlags.iota flags = false ->
      whne Γ (tProj p c)

  (** A saturated primitive operation blocked on a stuck argument is neutral,
      exactly as the kernel's [Ntrl] is (kernel/cClosure.ml).  The arguments
      before the stuck one are already literals, which is the order the kernel
      and the machine's [Prim_app] frame evaluate them in; it also makes the
      blocking argument unique, so that a term cannot be stuck here and rigid
      ([whnf_primapp_rigid]) there.  Saturation is exact: over-application goes
      through [whne_app]. *)
  | whne_primapp_stuck c u decl op ls a rest :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      prim_op_of Σ c = Some op ->
      #|ls| + S #|rest| = arity op ->
      whne Γ a ->
      whne Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest))

  (** A saturated primitive operation on literal arguments whose denotation or
      readback fails: the term has no reduction at all.  This is where a
      wrong-tag literal list and an unregistered [retro_bool] land, which is
      what makes the weak-head theory independent of the environment
      condition. *)
  | whne_primapp_inert c u decl op ls :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      prim_op_of Σ c = Some op ->
      #|ls| = arity op ->
      prim_reduct Σ op (map term_of_lit ls) = None ->
      whne Γ (mkApps (tConst c u) (map term_of_lit ls)).

  (* Relative to reduction flags *)
  Inductive whnf (Γ : context) : term -> Type :=
  | whnf_ne t : whne Γ t -> whnf Γ t
  | whnf_sort s : whnf Γ (tSort s)
  | whnf_prod na A B : whnf Γ (tProd na A B)
  | whnf_lam na A B : whnf Γ (tLambda na A B)
  | whnf_cstrapp i n u v : whnf Γ (mkApps (tConstruct i n u) v)
  | whnf_indapp i u v : whnf Γ (mkApps (tInd i u) v)
  | whnf_fixapp mfix idx args :
    (exists d, nth_error mfix idx = Some d /\ nth_error args (rarg d) = None)
      \/ (nth_error mfix idx = None) ->
    whnf Γ (mkApps (tFix mfix idx) args)
  | whnf_cofixapp mfix idx v : whnf Γ (mkApps (tCoFix mfix idx) v)
  | whnf_prim p : whnf Γ (tPrim p)
  (** An unsaturated primitive operation is a value, not a neutral, as the
      kernel says ("partially applied primitives are not Ntrl") and as PCUIC
      treats an unsaturated fixpoint. *)
  | whnf_primapp_partial c u decl op args :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      prim_op_of Σ c = Some op ->
      #|args| < arity op ->
      whnf Γ (mkApps (tConst c u) args)
  (** A saturated primitive operation whose first non-literal argument is
      already a weak-head normal form: the rule can never fire, but the
      application is not neutral.  [lit_of_term a = None] is stable under
      reduction because [a] is a weak-head normal form
      ([whnf_lit_pres1]). *)
  | whnf_primapp_rigid c u decl op ls a rest :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      prim_op_of Σ c = Some op ->
      #|ls| + S #|rest| = arity op ->
      whnf Γ a ->
      lit_of_term a = None ->
      whnf Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)).

  Lemma whne_mkApps :
    forall Γ t args,
      whne Γ t ->
      whne Γ (mkApps t args).
  Proof using Type.
    intros Γ t args h.
    induction args in t, h |- *.
    - assumption.
    - simpl. eapply IHargs. econstructor. assumption.
  Qed.

  Lemma whnf_mkApps :
    forall Γ t args,
      whne Γ t ->
      whnf Γ (mkApps t args).
  Proof using Type.
    intros. econstructor. now eapply whne_mkApps.
  Qed.

  (** A neutral is never a literal, so a stuck argument always blocks the
      rule. *)
  Lemma whne_not_lit Γ t : whne Γ t -> lit_of_term t = None.
  Proof using Type.
    intros h; destruct t => //.
    exfalso; depelim h; solve_discr.
  Qed.

  (** The literal prefix makes the blocking argument unique: [split_lits] is a
      function, and [split_lits_app] computes it on the decomposition. *)
  Lemma lit_split_inj ls a rest ls' a' rest' :
    lit_of_term a = None -> lit_of_term a' = None ->
    map term_of_lit ls ++ a :: rest = map term_of_lit ls' ++ a' :: rest' ->
    [× ls = ls', a = a' & rest = rest'].
  Proof using Type.
    intros ha ha' e.
    pose proof (split_lits_app (ls := ls) (a := a) (rest := rest) ha) as h.
    rewrite e (split_lits_app (ls := ls') (a := a') (rest := rest') ha') in h.
    noconf h; split => //.
  Qed.

  (** Inversion: a saturated application of a declared bodiless registered
      constant is a weak-head normal form only as a neutral or as a rigid
      application.  [whnf_primapp_partial] cannot apply, because the
      application is saturated. *)
  Lemma whnf_primapp_inv Γ c u decl op args :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    prim_op_of Σ c = Some op ->
    #|args| = arity op ->
    whnf Γ (mkApps (tConst c u) args) ->
    whne Γ (mkApps (tConst c u) args) +
    (∑ ls a rest, [× args = map term_of_lit ls ++ a :: rest, whnf Γ a & lit_of_term a = None]).
  Proof using Type.
    intros hl hb hop hlen h.
    depelim h; try solve [exfalso; solve_discr].
    - now left.
    - exfalso.
      eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy].
      noconf eh. subst.
      match goal with H : prim_op_of Σ _ = Some _ |- _ => rewrite hop in H; noconf H end.
      lia.
    - right.
      eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy].
      noconf eh. exists ls, a, rest; split => //.
  Qed.

  (** The blocking argument of a stuck application is determined, so a term
      cannot be stuck at one argument and rigid at another. *)
  Lemma whnf_primapp_stuck_inv Γ c u decl op ls a rest :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    prim_op_of Σ c = Some op ->
    #|ls| + S #|rest| = arity op ->
    lit_of_term a = None ->
    whnf Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) ->
    whne Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) + whnf Γ a.
  Proof using Type.
    intros hl hb hop hlen ha h.
    eapply whnf_primapp_inv in h as [hw|[ls' [a' [rest' [e hw ha']]]]]; tea.
    - now left.
    - right. eapply lit_split_inj in e as [_ <- _]; tea.
    - rewrite length_app length_map /=; lia.
  Qed.

  (** ** Why four constructors, not one "cannot fire" premise (design §6, change log 14)

      The design's version 7 had one saturated constructor with a bare
      "cannot fire" premise: some argument stuck, or not a literal of the expected
      tag, or [prim_op_denote]/[readback] returning [None].  That makes
      [eqb ((fun x => x) 1) 2] neutral (its first argument is not a literal), yet
      it steps to [eqb 1 2], which fires; so [whne_pres1]/[whnf_pres1] would be
      false.  The split keeps both true:
      - [whne_pres1] and [whnf_pres1] are stated only for [RedFlags.default]
        ([default := mk true true true true true true] above), so every
        flag-off neutral constructor is vacuous for them;
      - [whne_primapp_stuck] and [whnf_primapp_rigid] block on a settled
        argument: a [whne] one, or a [whnf] one that is not a literal, and
        [whnf_lit_pres1] proves such an argument never steps to a literal;
      - [whne_primapp_inert] has literal arguments only, so it has no [red1]
        step at all;
      - [whnf_primapp_partial] is stable because a step never changes the
        number of arguments (only an argument reduces: [red1_mkApps_tConst_inv]). *)

  Lemma whne_mkApps_inv :
    forall Γ t l,
      negb (isApp t) ->
      whne Γ (mkApps t l) ->
      whne Γ t +
      (∑ mfix idx d a,
        t = tFix mfix idx ×
        nth_error mfix idx = Some d ×
        nth_error l (rarg d) = Some a ×
        whne Γ a) +
      (∑ c u decl op,
        t = tConst c u ×
        lookup_env Σ c = Some (ConstantDecl decl) ×
        decl.(cst_body) = None ×
        prim_op_of Σ c = Some op ×
        arity op <= #|l| ×
        whne Γ (mkApps (tConst c u) (firstn (arity op) l))).
  Proof using Type.
    intros Γ t l Ha h. revert t Ha h.
    induction l using rev_ind; intros.
    - eauto.
    - rewrite mkApps_snoc in h.
      depelim h.
      + edestruct IHl as [[ | (? & ? & ? & ? & ? & ? & ? & ?)] | (?&?&?&?&?&?&?&?&?&?)]; eauto.
        * subst. left; right. exists x0, x1, x2, x3. repeat split; eauto.
          now eapply nth_error_app_left.
        * subst. right. eexists _, _, _, _. repeat split; tea.
          2:{ rewrite firstn_app.
              replace (arity x3 - #|l|) with 0 by lia.
              now rewrite firstn_O app_nil_r. }
          rewrite length_app /=; lia.
      + rewrite <- mkApps_snoc in x.
        eapply (f_equal decompose_app) in x;
          rewrite !decompose_app_mkApps in x; cbn in *; try intuition congruence.
        inversion x. subst.
        left; right. exists mfix, idx, d, arg. repeat split; eauto.
      + rewrite <- mkApps_snoc in x.
        eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy].
        assert (hl2 : #|l ++ [x0]| = arity op).
        { apply (f_equal (@List.length term)) in ea; revert ea.
          rewrite !length_app !length_map /=; lia. }
        subst. right. eexists _, _, _, _. repeat split; tea.
        * lia.
        * rewrite firstn_all2; try (rewrite hl2; apply le_n).
          (rewrite ea || rewrite -ea).
          eapply whne_primapp_stuck; tea.
      + rewrite <- mkApps_snoc in x.
        eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy].
        assert (hl2 : #|l ++ [x0]| = arity op).
        { apply (f_equal (@List.length term)) in ea; revert ea.
          rewrite !length_app !length_map /=; lia. }
        subst. right. eexists _, _, _, _. repeat split; tea.
        * lia.
        * rewrite firstn_all2; try (rewrite hl2; apply le_n).
          (rewrite ea || rewrite -ea).
          eapply whne_primapp_inert; tea.
  Qed.

  (** Under [delta] the head of a registered operation of positive arity is not
      neutral on its own: [whne_const] needs [prim_op_of Σ c = None]. *)
  Lemma whne_tConst_prim Γ c u op :
    RedFlags.delta flags = true ->
    prim_op_of Σ c = Some op ->
    0 < arity op ->
    whne Γ (tConst c u) -> False.
  Proof using Type.
    intros hd hop hpos h.
    depelim h; try congruence.
    all: apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x; try reflexivity.
    all: cbn in x; noconf x.
    all: try match goal with
         | [ H : ?l ++ _ :: _ = [] |- _ ] => destruct l; discriminate
         end.
    destruct ls; [|discriminate]. cbn in *.
    match goal with
    | [ H : prim_op_of Σ _ = Some ?op', H' : 0 = arity ?op' |- _ ] =>
        rewrite hop in H; noconf H; lia
    end.
  Qed.

  (** A saturated application of a registered operation, under [delta], is
      neutral only through [whne_primapp_stuck] or [whne_primapp_inert]: the head
      alone is not neutral ([whne_tConst_prim]), nor is an unsaturated prefix
      ([whne_mkApps_inv]). *)
  Lemma whne_primapp_sat_inv Γ c u op args :
    RedFlags.delta flags = true ->
    prim_op_of Σ c = Some op ->
    #|args| = arity op ->
    whne Γ (mkApps (tConst c u) args) ->
    (∑ ls a rest, (args = map term_of_lit ls ++ a :: rest) × whne Γ a) +
    (∑ ls, (args = map term_of_lit ls) × prim_reduct Σ op args = None).
  Proof using Type.
    intros hd hop hlen h.
    destruct args as [|y args _] using MRList.rev_ind.
    - cbn in h. depelim h; try congruence.
      all: apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x; try reflexivity.
      all: cbn in x; noconf x.
      all: try match goal with
           | [ H : ?l ++ _ :: _ = [] |- _ ] => destruct l; discriminate
           end.
      right. destruct ls; [|discriminate]. exists []. split; [reflexivity|].
      match goal with H : prim_op_of Σ _ = Some _ |- _ => rewrite hop in H; noconf H end.
      assumption.
    - rewrite length_app /= in hlen. rewrite mkApps_snoc in h.
      depelim h.
      + exfalso.
        eapply (whne_mkApps_inv _ (tConst c u) args eq_refl) in h
          as [[hw|(? & ? & ? & ? & e & _)]|(? & ? & ? & ? & e & _ & _ & hop' & hle & _)].
        * eapply whne_tConst_prim; tea. lia.
        * discriminate.
        * noconf e. rewrite hop in hop'. noconf hop'. lia.
      + rewrite <- mkApps_snoc in x.
        apply (f_equal decompose_app) in x; rewrite !decompose_app_mkApps in x; try reflexivity.
        all: cbn in x; noconf x.
      + rewrite <- mkApps_snoc in x.
        eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy].
        left. exists ls, a, rest. split; [now symmetry|assumption].
      + rewrite <- mkApps_snoc in x.
        eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy].
        noconf eh.
        match goal with H : prim_op_of Σ _ = Some _ |- _ => rewrite hop in H; noconf H end.
        right. exists ls. rewrite -ea. split; [reflexivity|assumption].
  Qed.

  (** An over-applied primitive application is a weak-head normal form only as a
      neutral: [whnf_primapp_partial] and [whnf_primapp_rigid] both have at most
      [arity op] arguments. *)
  Lemma whnf_primapp_over_inv Γ c u decl op args :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    prim_op_of Σ c = Some op ->
    arity op < #|args| ->
    whnf Γ (mkApps (tConst c u) args) -> whne Γ (mkApps (tConst c u) args).
  Proof using Type.
    intros hl hop hlt h.
    depelim h; try solve [exfalso; solve_discr].
    - assumption.
    - exfalso. eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy]. noconf eh. subst.
      match goal with H : prim_op_of Σ _ = Some _ |- _ => rewrite hop in H; noconf H end.
      lia.
    - exfalso. eapply mkApps_eq_inj in x as [eh ea]; [|easy|easy]. noconf eh.
      match goal with H : prim_op_of Σ _ = Some _ |- _ => rewrite hop in H; noconf H end.
      rewrite -ea length_app length_map /= in hlt. lia.
  Qed.

  (** A saturated application blocked on an argument that is neither a literal
      nor a weak-head normal form is not a weak-head normal form, in any
      environment: no constructor of §6 covers it.  (Design change log 14's
      counterexample, [eqb ((fun x => x) 1) 2], is such a term.) *)
  Lemma not_whnf_primapp_arg Γ c u decl op ls a rest :
    RedFlags.delta flags = true ->
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    prim_op_of Σ c = Some op ->
    #|ls| + S #|rest| = arity op ->
    lit_of_term a = None ->
    (whnf Γ a -> False) ->
    whnf Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) -> False.
  Proof using Type.
    intros hd hl hb hop hlen ha hna h.
    eapply whnf_primapp_stuck_inv in h as [hw|hw]; tea.
    2: exact (hna hw).
    eapply whne_primapp_sat_inv in hw as [(ls' & a' & rest' & e & hw)|(ls' & e)]; tea.
    - eapply (lit_split_inj ls a rest ls' a' rest' ha (whne_not_lit _ _ hw)) in e as [_ <- _].
      exact (hna (whnf_ne _ _ hw)).
    - pose proof (split_lits_app (ls := ls) (a := a) (rest := rest) ha) as hs.
      rewrite e split_lits_map in hs. discriminate.
    - rewrite length_app length_map /=. lia.
  Qed.

End Normal.

Derive Signature for whnf.
Derive Signature for whne.
Derive Signature for All.
#[global]
Hint Constructors whnf whne : core.
#[global]
Hint Constructors whnf whne : pcuic.

(** The two weak-head normal forms of design §6 that are primitive-operation
    applications but not neutral: exactly the premises of [whnf_primapp_partial]
    (constructor 2) and [whnf_primapp_rigid] (constructor 5). *)
Variant primapp_nonneutral flags Σ Γ : term -> Type :=
| primapp_nonneutral_partial c u decl op args :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    prim_op_of Σ c = Some op ->
    #|args| < arity op ->
    primapp_nonneutral flags Σ Γ (mkApps (tConst c u) args)
| primapp_nonneutral_rigid c u decl op ls a rest :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    prim_op_of Σ c = Some op ->
    #|ls| + S #|rest| = arity op ->
    whnf flags Σ Γ a ->
    lit_of_term a = None ->
    primapp_nonneutral flags Σ Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)).

Local Ltac inv H := inversion H; subst; clear H.

Ltac help' := try repeat match goal with
| [ H0 : _ = mkApps _ _ |- _ ] =>
  eapply (f_equal decompose_app) in H0;
    rewrite !decompose_app_mkApps in H0; cbn in *; intuition congruence
| [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
  destruct args using rev_ind; cbn in *; [ inv H1 |
                                           rewrite mkApps_app in H1; cbn in *; inv H1
                                  ]
        end.
Ltac help := help'; try match goal with | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0 end; help'.

#[global]
Hint Resolve All_Forall : core.

Notation decision P := ({P} + {~P}).

Lemma dec_All X (L : list X) P : All (fun x => decision (P x)) L ->
                                 All P L + (All P L -> False).
Proof.
  intros. induction X0.
  - left. econstructor.
  - destruct p.
    + destruct IHX0. left; econstructor; eauto. right. inversion 1. subst. eauto.
    + right. inversion 1; subst; eauto.
Defined.

Lemma negb_is_true b :
 ~ is_true b -> is_true (negb b).
Proof.
  destruct b; pcuicfo. congruence.
Qed.
#[global]
Hint Resolve negb_is_true : core.

Lemma whnf_mkApps_inv flags :
  forall Σ Γ t l,
    whnf flags Σ Γ (mkApps t l) ->
    whnf flags Σ Γ t.
Proof.
  intros Σ Γ t l h.
  remember (mkApps t l) eqn:hdeq.
  revert hdeq.
  induction h in h, t, l, t0 |- *; intros eq; subst.
  - destruct (mkApps_elim t l).
    apply whne_mkApps_inv in w; auto.
    destruct w as [[wh|(?&?&?&?&->&?&?&?)]|(c&u&decl&op&->&hl&hb&hop&har&hw)].
    + now apply whnf_mkApps.
    + destruct (leb_spec_Set n (rarg x1)).
      * eapply whnf_fixapp.
        rewrite e. left.
        apply nth_error_Some_length in e0. eexists.
        split; try reflexivity. apply nth_error_None.
        rewrite length_firstn.
        lia.
      * apply whnf_ne.
        eapply whne_fixapp; eauto.
        assert (rarg x1 < #|l|) by (now apply nth_error_Some_length in e0).
        rewrite <- (firstn_skipn n l) in e0.
        rewrite nth_error_app1 in e0; auto.
        rewrite length_firstn.
        lia.
    + destruct (le_lt_dec (arity op) n).
      * rewrite -(firstn_skipn (arity op) (firstn n l)) mkApps_app.
        apply whnf_mkApps.
        assert (firstn (arity op) (firstn n l) = firstn (arity op) l) as ->
          by (rewrite firstn_firstn; f_equal; lia).
        exact hw.
      * eapply whnf_primapp_partial; tea.
        rewrite length_firstn; lia.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
    eapply whnf_fixapp. destruct o; [| now right].
    left; try reflexivity. destruct H; eexists.
    destruct H. split; eauto. destruct nth_error as [?|]; [|easy].
    apply nth_error_None.
    apply nth_error_None in e0.
    rewrite length_firstn.
    lia.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
  - destruct l using MRList.rev_ind; [|now rewrite mkApps_app in eq].
    cbn in *; subst; auto.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
    eapply whnf_primapp_partial; tea.
    rewrite length_firstn; lia.
  - destruct (mkApps_elim t l).
    apply mkApps_eq_inj in eq as (<-&<-); auto.
    match goal with
    | |- whnf _ _ _ (mkApps _ (firstn ?k _)) => destruct (le_lt_dec (arity op) k)
    end.
    + assert (firstn_all_eq : forall k, arity op <= k ->
        firstn k (map term_of_lit ls ++ a :: rest) = map term_of_lit ls ++ a :: rest).
      { intros k hk; apply firstn_all2; rewrite length_app length_map /=; lia. }
      rewrite firstn_all_eq //.
      eapply whnf_primapp_rigid; tea.
    + eapply whnf_primapp_partial; tea.
      rewrite length_firstn length_app length_map /=; lia.
Qed.

Lemma whnf_fixapp' {flags} Σ Γ mfix idx narg v :
  nth_error mfix idx = Some narg ->
  nth_error v (rarg narg) = None ->
  whnf flags Σ Γ (mkApps (tFix mfix idx) v).
Proof.
 intros E1 H. eapply whnf_fixapp. now left.
Qed.
#[global]
Hint Resolve whnf_fixapp' : core.

(** A default weak-head normal form that is neutral under [nodelta] is neutral
    under [default], unless it is one of §6's two non-neutral primitive shapes
    ([primapp_nonneutral]).  The disjunct is needed: [nodelta] makes every
    constant neutral ([whne_const_nodelta]), so for a registered operation [c] of
    positive arity, [tConst c u] is [whnf default] ([whnf_primapp_partial]) and
    [whne nodelta], but not [whne default] ([whne_tConst_prim]); a rigid
    application is the same (design change log 17).  Every other non-neutral
    whnf shape is not [nodelta]-neutral either. *)
Lemma whnf_whne_nodelta_upgrade Σ Γ t :
  whnf RedFlags.default Σ Γ t ->
  whne RedFlags.nodelta Σ Γ t ->
  whne RedFlags.default Σ Γ t + primapp_nonneutral RedFlags.default Σ Γ t.
Proof.
  intros whn whe.
  depelim whn.
  - now left.
  - exfalso; depelim whe; help.
  - exfalso; depelim whe; help.
  - exfalso; depelim whe; cbn in *; try discriminate; help.
  - exfalso.
    eapply whne_mkApps_inv in whe as [[hw|(? & ? & ? & ? & e & _)]|(? & ? & ? & ? & e & _)];
      try reflexivity; try discriminate.
    depelim hw; help.
  - exfalso.
    eapply whne_mkApps_inv in whe as [[hw|(? & ? & ? & ? & e & _)]|(? & ? & ? & ? & e & _)];
      try reflexivity; try discriminate.
    depelim hw; help.
  - exfalso.
    eapply whne_mkApps_inv in whe as [[hw|(mfix' & idx' & d & a & e & hn & ha & _)]|(? & ? & ? & ? & e & _)];
      try reflexivity; try discriminate.
    + depelim hw; cbn in *; try discriminate; help.
      all: apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x; try reflexivity.
      all: cbn in x; noconf x.
      all: match goal with H : nth_error [] ?n = Some _ |- _ => destruct n; discriminate end.
    + noconf e. destruct o as [(d' & hd' & hn')|hn']; congruence.
  - exfalso.
    eapply whne_mkApps_inv in whe as [[hw|(? & ? & ? & ? & e & _)]|(? & ? & ? & ? & e & _)];
      try reflexivity; try discriminate.
    depelim hw; help.
  - exfalso; depelim whe; help.
  - right. eapply primapp_nonneutral_partial; tea.
  - right. eapply primapp_nonneutral_rigid; tea.
Qed.

Local Notation whnf_whne_decision flags Σ Γ t :=
  (({∥whnf flags Σ Γ t∥} + {~∥whnf flags Σ Γ t∥}) *
   ({∥whne flags Σ Γ t∥} + {~∥whne flags Σ Γ t∥}))%type.

(** Under [delta], a neutral application of a constant has a bodiless declared
    head: [whne_const], the stuck and the inert constructor all carry it. *)
Lemma whne_const_app_inv flags Σ Γ c u args :
  RedFlags.delta flags = true ->
  whne flags Σ Γ (mkApps (tConst c u) args) ->
  ∑ decl, (lookup_env Σ c = Some (ConstantDecl decl)) × (cst_body decl = None).
Proof.
  intros hd w.
  eapply whne_mkApps_inv in w as [[w|(? & ? & ? & ? & e & _)]|(? & ? & decl & ? & e & hl & hb & _)];
    try reflexivity; try discriminate.
  - depelim w; try congruence.
    all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
              try reflexivity; cbn in x; noconf x).
    all: eexists; split; eassumption.
  - noconf e. now exists decl.
Qed.

(** The same for a weak-head normal form. *)
Lemma whnf_const_app_inv flags Σ Γ c u args :
  RedFlags.delta flags = true ->
  whnf flags Σ Γ (mkApps (tConst c u) args) ->
  ∑ decl, (lookup_env Σ c = Some (ConstantDecl decl)) × (cst_body decl = None).
Proof.
  intros hd w. depelim w.
  all: try (apply (f_equal decompose_app) in x; rewrite !decompose_app_mkApps in x;
            try reflexivity; cbn in x; noconf x).
  all: try solve [eapply whne_const_app_inv; tea].
  all: eexists; split; eassumption.
Qed.

(** Deciding a saturated application of a registered operation, from decisions
    on its arguments: all literals and inert, all literals and firing (neither),
    or blocked on its first non-literal argument, which is stuck, rigid, or not a
    weak-head normal form (neither). *)
Definition whnf_whne_primapp_sat_dec flags Σ Γ c u decl op args :
  RedFlags.delta flags = true ->
  lookup_env Σ c = Some (ConstantDecl decl) ->
  decl.(cst_body) = None ->
  prim_op_of Σ c = Some op ->
  #|args| = arity op ->
  All (fun a => whnf_whne_decision flags Σ Γ a) args ->
  whnf_whne_decision flags Σ Γ (mkApps (tConst c u) args).
Proof.
  intros hd hl hb hop hlen hall.
  destruct (split_lits args) as [ls|[[ls a] rest]] eqn:hs.
  - pose proof (split_lits_inl hs) as e. subst args.
    destruct (prim_reduct Σ op (map term_of_lit ls)) as [v|] eqn:hr.
    + assert (nwhne : ~ ∥whne flags Σ Γ (mkApps (tConst c u) (map term_of_lit ls))∥).
      { intros [w].
        eapply whne_primapp_sat_inv in w as [(ls' & a' & rest' & e' & w)|(ls' & e' & hr')]; tea.
        - pose proof (split_lits_app (ls := ls') (a := a') (rest := rest') (whne_not_lit _ _ _ _ w)) as hs'.
          rewrite -e' split_lits_map in hs'. discriminate.
        - congruence. }
      split; right; [|exact nwhne].
      intros [w].
      eapply whnf_primapp_inv in w as [w|(ls' & a' & rest' & [e' _ ha'])]; tea.
      * apply nwhne; now constructor.
      * pose proof (split_lits_app (ls := ls') (a := a') (rest := rest') ha') as hs'.
        rewrite -e' split_lits_map in hs'. discriminate.
    + assert (w : whne flags Σ Γ (mkApps (tConst c u) (map term_of_lit ls))).
      { eapply whne_primapp_inert; tea. now rewrite length_map in hlen. }
      split; left; constructor; [now apply whnf_ne|exact w].
  - destruct (split_lits_inr hs) as [e ha]. subst args.
    rewrite length_app length_map /= in hlen.
    apply All_app in hall as [_ hall].
    inversion hall as [|? ? pa hall']; subst.
    destruct pa as [[wa|nwa] [na|nna]].
    + split; left; destruct na as [na]; constructor.
      * apply whnf_ne. eapply whne_primapp_stuck; tea.
      * eapply whne_primapp_stuck; tea.
    + split.
      * left; destruct wa as [wa]; constructor. eapply whnf_primapp_rigid; tea.
      * right. intros [w].
        eapply whne_primapp_sat_inv in w as [(ls' & a' & rest' & e' & w)|(ls' & e' & _)]; tea.
        -- eapply (lit_split_inj ls a rest ls' a' rest' ha (whne_not_lit _ _ _ _ w)) in e' as [_ <- _].
           apply nna; now constructor.
        -- pose proof (split_lits_app (ls := ls) (a := a) (rest := rest) ha) as hs'.
           rewrite e' split_lits_map in hs'. discriminate.
        -- rewrite length_app length_map /=. lia.
    + exfalso. destruct na as [na]. apply nwa. constructor. now apply whnf_ne.
    + assert (nf : whnf flags Σ Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) -> False).
      { eapply not_whnf_primapp_arg; tea. intros wa; apply nwa; now constructor. }
      split; right; intros [w]; apply nf; [exact w|now apply whnf_ne].
Defined.

(** Deciding any application of a registered operation: unsaturated (a whnf,
    not neutral), saturated ([whnf_whne_primapp_sat_dec]), or over-applied,
    decided on its saturated prefix. *)
Definition whnf_whne_primapp_dec flags Σ Γ c u decl op args :
  RedFlags.delta flags = true ->
  lookup_env Σ c = Some (ConstantDecl decl) ->
  decl.(cst_body) = None ->
  prim_op_of Σ c = Some op ->
  All (fun a => whnf_whne_decision flags Σ Γ a) args ->
  whnf_whne_decision flags Σ Γ (mkApps (tConst c u) args).
Proof.
  intros hd hl hb hop hall.
  destruct (lt_eq_lt_dec #|args| (arity op)) as [[hlt|heq]|hgt].
  - split.
    + left; constructor. eapply whnf_primapp_partial; tea.
    + right; intros [w].
      eapply whne_mkApps_inv in w as [[w|(? & ? & ? & ? & e & _)]|(? & ? & ? & op' & e & _ & _ & hop' & hle & _)];
        try reflexivity; try discriminate.
      * eapply whne_tConst_prim; tea. lia.
      * noconf e. rewrite hop in hop'. noconf hop'. lia.
  - exact (whnf_whne_primapp_sat_dec flags Σ Γ c u decl op args hd hl hb hop heq hall).
  - assert (hpre : #|firstn (arity op) args| = arity op) by (rewrite length_firstn; lia).
    assert (hallpre : All (fun a => whnf_whne_decision flags Σ Γ a) (firstn (arity op) args)).
    { rewrite -(firstn_skipn (arity op) args) in hall. now apply All_app in hall as [? _]. }
    destruct (snd (whnf_whne_primapp_sat_dec flags Σ Γ c u decl op _ hd hl hb hop hpre hallpre))
      as [wpre|nwpre].
    + split; left; destruct wpre as [wpre]; constructor.
      * apply whnf_ne. rewrite -(firstn_skipn (arity op) args) mkApps_app. now apply whne_mkApps.
      * rewrite -(firstn_skipn (arity op) args) mkApps_app. now apply whne_mkApps.
    + assert (nw : whne flags Σ Γ (mkApps (tConst c u) args) -> False).
      { intros w.
        eapply whne_mkApps_inv in w
          as [[w|(? & ? & ? & ? & e & _)]|(? & ? & ? & op' & e & _ & _ & hop' & hle & w)];
          try reflexivity; try discriminate.
        - apply nwpre; constructor. now apply whne_mkApps.
        - noconf e. rewrite hop in hop'. noconf hop'. apply nwpre. now constructor. }
      split; right; intros [w]; apply nw; [|exact w].
      eapply whnf_primapp_over_inv; tea.
Defined.

(** Deciding any application of a constant (none of its arguments, or some):
    the case split [whnf_whne_dec] uses for every [tConst] head, since a
    registered operation is decided by its arguments, not by its head. *)
Definition whnf_whne_const_app_dec flags Σ Γ c u args :
  All (fun a => whnf_whne_decision flags Σ Γ a) args ->
  whnf_whne_decision flags Σ Γ (mkApps (tConst c u) args).
Proof.
  intros hall.
  destruct (RedFlags.delta flags) eqn:hd.
  2:{ assert (w : whne flags Σ Γ (mkApps (tConst c u) args))
        by (apply whne_mkApps; now apply whne_const_nodelta).
      split; left; constructor; [now apply whnf_ne|exact w]. }
  assert (neither : ((∑ decl, (lookup_env Σ c = Some (ConstantDecl decl)) × (cst_body decl = None)) -> False) ->
                    whnf_whne_decision flags Σ Γ (mkApps (tConst c u) args)).
  { intros hn. split; right; intros [w]; apply hn;
      [eapply whnf_const_app_inv|eapply whne_const_app_inv]; tea. }
  destruct (lookup_env Σ c) as [[decl|mdecl]|] eqn:hl.
  - destruct (cst_body decl) as [body|] eqn:hb.
    + apply neither. intros (decl' & hl' & hb'). try rewrite hl in hl'. noconf hl'. congruence.
    + destruct (prim_op_of Σ c) as [op|] eqn:hop.
      * exact (whnf_whne_primapp_dec flags Σ Γ c u decl op args hd hl hb hop hall).
      * assert (w : whne flags Σ Γ (mkApps (tConst c u) args))
          by (apply whne_mkApps; eapply whne_const; tea).
        split; left; constructor; [now apply whnf_ne|exact w].
  - apply neither. intros (decl' & hl' & _). try rewrite hl in hl'. discriminate.
  - apply neither. intros (decl' & hl' & _). try rewrite hl in hl'. discriminate.
Defined.

(** The view [whnf_whne_dec] dispatches on. *)
Definition tConst_view t : {k & {ui & t = tConst k ui}} + (forall k ui, t <> tConst k ui).
Proof. destruct t; try (right; congruence). left; now eexists _, _. Defined.

(** No neutral is headed by a sort, a product, a literal or, under [beta], a λ.
    [w] is a neutral [mkApps] of such a head. *)
Local Ltac whne_head_absurd w :=
  eapply whne_mkApps_inv in w as [[w|(? & ? & ? & ? & ?e & _)]|(? & ? & ? & ? & ?e & _)];
  try reflexivity; try discriminate;
  depelim w; cbn in *; try congruence; help.

Definition whnf_whne_dec flags Σ Γ t :
  ({∥whnf flags Σ Γ t∥} + {~∥whnf flags Σ  Γ t∥}) *
  ({∥whne flags Σ Γ t∥} + {~∥whne flags Σ Γ t∥}).
Proof with eauto using sq with pcuic; try congruence.
  induction t using term_forall_mkApps_ind in Γ |- *; split...
  all: try now (right; intros [H]; depelim H;help).
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E...
    + right. intros [H]. depelim H. depelim w. congruence. all:help.
    + right. intros [H]. depelim H. depelim w. congruence. all:help.
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E...
    + right. intros [H]. depelim H; try congruence; help.
    + right. intros [H]. depelim H; try congruence; help.
  - destruct (RedFlags.beta flags) eqn:Er...
    right. intros [H]. depelim H; try congruence; help.
  - destruct (RedFlags.zeta flags) eqn:Er...
    right. intros [H]. depelim H. depelim w. all:help. congruence.
  - destruct (RedFlags.zeta flags) eqn:Er...
    right. intros [H]. depelim H; try congruence; help.
  - destruct (tConst_view t) as [(k & ui & ->)|hnc].
    { exact (fst (whnf_whne_const_app_dec flags Σ Γ k ui v (All_impl X (fun _ h => h Γ)))). }
    destruct (IHt Γ) as [[sh|nh] _].
    + destruct t; try solve [exfalso; exact (hnc _ _ eq_refl)].
      all: try now (left; eauto using whnf_mkApps, All_Forall).
      all: try now left; destruct sh as [w]; constructor; eapply whnf_mkApps; depelim w; eauto; help.
      * (* sort *)
        destruct v as [ | ? v]; [congruence|].
        right. intros [w]. depelim w; help. whne_head_absurd w.
      * (* product *)
        destruct v as [ | ? v]; [congruence|].
        right. intros [w]. depelim w; help. whne_head_absurd w.
      * (* λ *)
        destruct v as [ | ? v]; [congruence|].
        destruct (RedFlags.beta flags) eqn:hbeta.
        -- right. intros [w]. depelim w; help. whne_head_absurd w.
        -- left; constructor. apply whnf_mkApps. now constructor.
      * (* fixpoint *)
        destruct (nth_error mfix idx) as [narg |] eqn:E1.
        -- destruct (nth_error v (rarg narg)) as [a  | ] eqn:E2.
           2:{ left. constructor. eapply whnf_fixapp. rewrite E1. left; eexists; split; eauto. }
           destruct (nth_error_all E2 X Γ) as [_ [sa|na]].
           ++ left. destruct sa as [sa]. constructor. apply whnf_ne. eapply whne_fixapp; tea.
           ++ destruct (RedFlags.fix_ flags) eqn:hfix.
              ** right. intros [w]. depelim w; help.
                 --- eapply whne_mkApps_inv in w
                       as [[w|(mfix' & idx' & d & a' & e & hd & ha & w)]|(? & ? & ? & ? & e & _)];
                       try reflexivity; try discriminate.
                     +++ depelim w; cbn in *; try congruence; help.
                         all: apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                           try reflexivity.
                         all: cbn in x; noconf x.
                         all: match goal with H : nth_error [] ?n = Some _ |- _ => destruct n; discriminate end.
                     +++ noconf e. rewrite E1 in hd. noconf hd. rewrite E2 in ha. noconf ha.
                         apply na; now constructor.
                 --- apply (f_equal decompose_app) in x; rewrite !decompose_app_mkApps in x; try reflexivity.
                     all: cbn in x; noconf x.
                     destruct o as [(d & hd & hn)|hn]; congruence.
              ** left. constructor. apply whnf_mkApps. now constructor.
        -- left. constructor. eapply whnf_fixapp. now right.
      * (* literal *)
        destruct v as [ | ? v]; [congruence|].
        right. intros [w]. depelim w; help. whne_head_absurd w.
    + right. intros [w]. apply nh. constructor. now eapply whnf_mkApps_inv.
  - destruct (tConst_view t) as [(k & ui & ->)|hnc].
    { exact (snd (whnf_whne_const_app_dec flags Σ Γ k ui v (All_impl X (fun _ h => h Γ)))). }
    destruct (IHt Γ) as [_ [sh|nh]].
    + left. destruct sh as [w]. constructor. now eapply whne_mkApps.
    + destruct t; try solve [exfalso; exact (hnc _ _ eq_refl)].
      all: try solve [exfalso; match goal with h : ~ _ |- _ => apply h; reflexivity end].
      all: try solve [right; intros [w];
        eapply whne_mkApps_inv in w as [[w|(? & ? & ? & ? & e & _)]|(? & ? & ? & ? & e & _)];
        try reflexivity; try discriminate; apply nh; now constructor].
      (* fixpoint *)
      destruct (nth_error mfix idx) as [narg |] eqn:E1.
      * destruct (nth_error v (rarg narg)) as [a  | ] eqn:E2.
        -- destruct (nth_error_all E2 X Γ) as [_ [sa|na]].
           ++ left. destruct sa as [sa]. constructor. eapply whne_fixapp; tea.
           ++ destruct (RedFlags.fix_ flags) eqn:hfix.
              ** right. intros [w].
                 eapply whne_mkApps_inv in w
                   as [[w|(mfix' & idx' & d & a' & e & hd & ha & w)]|(? & ? & ? & ? & e & _)];
                   try reflexivity; try discriminate.
                 --- apply nh; now constructor.
                 --- noconf e. rewrite E1 in hd. noconf hd. rewrite E2 in ha. noconf ha.
                     apply na; now constructor.
              ** left. constructor. apply whne_mkApps. now constructor.
        -- right. intros [w].
           eapply whne_mkApps_inv in w
             as [[w|(mfix' & idx' & d & a' & e & hd & ha & w)]|(? & ? & ? & ? & e & _)];
             try reflexivity; try discriminate.
           ++ apply nh; now constructor.
           ++ noconf e. rewrite E1 in hd. noconf hd. congruence.
      * right. intros [w].
        eapply whne_mkApps_inv in w
          as [[w|(mfix' & idx' & d & a' & e & hd & ha & w)]|(? & ? & ? & ? & e & _)];
          try reflexivity; try discriminate.
        -- apply nh; now constructor.
        -- noconf e. congruence.
  - match goal with |- context [tConst ?k ?ui] =>
      exact (fst (whnf_whne_const_app_dec flags Σ Γ k ui [] All_nil)) end.
  - match goal with |- context [tConst ?k ?ui] =>
      exact (snd (whnf_whne_const_app_dec flags Σ Γ k ui [] All_nil)) end.
  - left. constructor. eapply whnf_indapp with (v := []).
  - left. constructor. eapply whnf_cstrapp with (v := []).
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s...
    + right. intros [w]. depelim w. depelim w. all:help...
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s...
    + right. intros [w]. depelim w. all:help...
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s0...
    + right. intros [w]. depelim w. depelim w. all:help...
  - destruct (RedFlags.iota flags) eqn:Eq...
    destruct (IHt Γ) as [_ []].
    + left. destruct s0...
    + right. intros [w]. depelim w. all:help...
  - destruct (nth_error m n) as [narg |] eqn:E1.
    + left. constructor. eapply whnf_fixapp with (args := []). rewrite E1.
      left; eexists; split; eauto. now destruct (rarg narg).
    + left. constructor. eapply whnf_fixapp with (args := []). now right.
  - destruct (RedFlags.fix_ flags) eqn:?...
    right. intros [w]. depelim w; cbn in *; try congruence; help.
    all: apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x; try reflexivity.
    all: cbn in x; noconf x.
    all: match goal with H : nth_error [] ?n = Some _ |- _ => destruct n; discriminate end.
  - left. constructor. eapply whnf_cofixapp with (v := []).
Defined.

Definition whnf_dec flags Σ Γ t := fst (whnf_whne_dec flags Σ Γ t).
Definition whne_dec flags Σ Γ t := snd (whnf_whne_dec flags Σ Γ t).

Lemma red1_mkApps_tConstruct_inv Σ Γ i n u v t' :
  red1 Σ Γ (mkApps (tConstruct i n u) v) t' ->
  ∑ v', (t' = mkApps (tConstruct i n u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help.
  - rewrite mkApps_snoc in X. depelim X; try solve [help].
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x]). rewrite mkApps_snoc. split; eauto.
      apply OnOne2_app_r. assumption.
    + exists (v ++ [N2]). rewrite mkApps_snoc. split; eauto.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma red1_mkApps_tInd_inv Σ Γ i u v t' :
  red1 Σ Γ (mkApps (tInd i u) v) t' ->
  ∑ v', (t' = mkApps (tInd i u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help.
  - rewrite mkApps_snoc in X. depelim X; try solve [help].
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x]). rewrite mkApps_snoc. split; eauto.
      apply OnOne2_app_r. assumption.
    + exists (v ++ [N2]). rewrite mkApps_snoc. split; eauto.
      eapply OnOne2_app. econstructor. eauto.
Qed.

(** An application of fewer than [arity op] arguments cannot fire: a shorter
    literal list is refused by [prim_op_denote] (its tags cannot match
    [po_args], whose length is [arity op]). *)
Lemma prim_reduct_short Σ op args :
  #|args| < arity op -> prim_reduct Σ op args = None.
Proof.
  intros hlt; rewrite /prim_reduct.
  destruct (lits_of_args args) as [ls|] eqn:hls => //.
  apply lits_of_args_inv in hls as ->.
  destruct (prim_op_denote op ls) as [r|] eqn:hd => //.
  apply prim_op_denote_args in hd.
  rewrite length_map /arity -hd length_map in hlt. lia.
Qed.

(** A bodiless registered operation applied to at most [arity op] arguments
    that does not itself fire reduces only inside one argument: the head cannot
    unfold ([cst_body = None] rules out [red_delta]), and the rule cannot fire
    at the root ([prim_reduct = None]) nor at any proper prefix (each is shorter
    than [arity op], [prim_reduct_short]).  This is the inversion the [whnf]
    preservation and [whnf_red] cases of the primitive constructors use. *)
Lemma red1_mkApps_tConst_inv {cf:checker_flags} Σ {wfΣ : wf Σ} Γ c u decl op args t' :
  lookup_env Σ c = Some (ConstantDecl decl) ->
  cst_body decl = None ->
  prim_op_of Σ c = Some op ->
  #|args| <= arity op ->
  prim_reduct Σ op args = None ->
  red1 Σ Γ (mkApps (tConst c u) args) t' ->
  ∑ args', (t' = mkApps (tConst c u) args') × OnOne2 (red1 Σ Γ) args args'.
Proof.
  intros hl hb hop hlen hcf r.
  revert t' hlen hcf r. induction args using rev_ind; intros t' hlen hcf r.
  - cbn in r. depelim r; try solve_discr.
    + (* red_delta: cst_body = Some, contradicting hb *)
      unshelve epose proof (hg := declared_constant_to_gen isdecl); eauto.
      unfold declared_constant_gen in hg. rewrite hl in hg.
      noconf hg. congruence.
    + (* red_prim_op with ls = [] : prim_reduct = Some, contradicting hcf *)
      exfalso. destruct ls; [|discriminate]. rewrite hop in e. noconf e.
      move: hcf. rewrite /prim_reduct /= e1 e2 //.
  - rewrite mkApps_snoc in r. depelim r; try solve_discr; try solve [help].
    + (* red_prim_op at the root: args ++ [x0] all literals, prim_reduct = Some *)
      exfalso. move: hcf.
      rewrite -mkApps_snoc in x. apply mkApps_eq_inj in x as [eh ea]; [|easy|easy]. noconf eh.
      rewrite hop in e. noconf e.
      rewrite -ea /prim_reduct lits_of_args_map e1 e2 //.
    + (* app_red_l: the head application reduces *)
      edestruct (IHargs N1) as (args' & -> & ho).
      * rewrite length_app /= in hlen; lia.
      * apply prim_reduct_short. rewrite length_app /= in hlen; lia.
      * exact r.
      * exists (args' ++ [x]). rewrite mkApps_snoc. split; [reflexivity|].
        now apply OnOne2_app_r.
    + (* app_red_r: the last argument reduces *)
      exists (args ++ [N2]). rewrite mkApps_snoc. split; [reflexivity|].
      apply OnOne2_app. now constructor.
Qed.

(** A one-step reduction of a saturated-up-to-the-blocker application reduces
    either the blocking argument [a] or one of the tail arguments [rest]; the
    literal prefix is never touched, because a literal does not reduce.  This
    keeps a stuck or rigid primitive application in the same shape after a step
    (its witness [whne]/[whnf] for [a] is carried by the caller). *)
Lemma OnOne2_primapp_split {R : term -> term -> Type} ls a rest args' :
  (forall l t, R (term_of_lit l) t -> False) ->
  OnOne2 R (map term_of_lit ls ++ a :: rest) args' ->
  (∑ a', (args' = map term_of_lit ls ++ a' :: rest) × R a a') +
  (∑ rest', (args' = map term_of_lit ls ++ a :: rest') × OnOne2 R rest rest').
Proof.
  intros hlit ho. induction ls as [|l ls ih] in args', ho |- *.
  - cbn in ho. depelim ho.
    + left. eexists; split; [reflexivity|eassumption].
    + right. eexists; split; [reflexivity|eassumption].
  - cbn in ho. depelim ho.
    + exfalso; eapply hlit; eassumption.
    + match goal with H : OnOne2 R (map term_of_lit ls ++ a :: rest) _ |- _ =>
        destruct (ih _ H) as [(a'&->&?)|(rest'&->&?)] end.
      * left. eexists; split; [cbn; reflexivity|eassumption].
      * right. eexists; split; [cbn; reflexivity|eassumption].
Qed.

Lemma is_constructor_app_false i x y :
  is_constructor i (x ++ y) = false ->
  is_constructor i x = false.
Proof.
  unfold is_constructor.
  destruct (nth_error (x ++ y) i) eqn:nth.
  - destruct nth_error eqn:nth' in |- *; [|easy].
    erewrite nth_error_app_left in nth by easy.
    intros; congruence.
  - apply nth_error_None in nth.
    rewrite (proj2 (nth_error_None _ _)); [|easy].
    rewrite length_app in nth.
    lia.
Qed.

Lemma red1_mkApps_tFix_inv Σ Γ mfix id v t' :
  match unfold_fix mfix id with
  | Some (rarg, body) => is_constructor rarg v = false
  | None => True
  end ->
  red1 Σ Γ (mkApps (tFix mfix id) v) t' ->
  (∑ v', (t' = mkApps (tFix mfix id) v') * (OnOne2 (red1 Σ Γ) v v'))
  + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x0 : def term => (dname x0, dbody x0, rarg x0))) mfix mfix'))
  + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody (fun x0 : def term => (dname x0, dtype x0, rarg x0))) mfix mfix')).
Proof.
  intros not_ctor. revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help; eauto.
    solve_discr.
    unfold is_constructor in e0.
    rewrite nth_error_nil in e0.
    congruence.
  - rewrite mkApps_snoc in X.
    depelim X; help; eauto.
    + solve_discr.
      rewrite e in not_ctor, IHv.
      congruence.
    + eapply IHv in X as [ [(? & ? & ?)|(?&?&?)] | (?&?&?)].
      * subst. left. left. exists (x0 ++ [x]). split. now rewrite mkApps_snoc.
        now apply OnOne2_app_r.
      * subst. left. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * subst. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * destruct unfold_fix as [(?&?)|]; [|easy].
        now eapply is_constructor_app_false.
    + left. left. exists (v ++ [N2]). split.
      now rewrite mkApps_snoc.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma red1_mkApps_tCoFix_inv Σ Γ mfix id v t' :
  red1 Σ Γ (mkApps (tCoFix mfix id) v) t' ->
  (∑ v', (t' = mkApps (tCoFix mfix id) v') * (OnOne2 (red1 Σ Γ) v v'))
  + (∑ mfix', (t' = mkApps (tCoFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x0 : def term => (dname x0, dbody x0, rarg x0))) mfix mfix'))
  + (∑ mfix', (t' = mkApps (tCoFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody (fun x0 : def term => (dname x0, dtype x0, rarg x0))) mfix mfix')).
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help; eauto.
  - rewrite mkApps_snoc in X.
    depelim X; help; eauto.
    + eapply IHv in X as [ [(? & ? & ?)|(?&?&?)] | (?&?&?)].
      * subst. left. left. exists (x0 ++ [x]). split. now rewrite mkApps_snoc.
        now apply OnOne2_app_r.
      * subst. left. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * subst. right. exists x0. split. now rewrite mkApps_snoc. eauto.
    + left. left. exists (v ++ [N2]). split.
      now rewrite mkApps_snoc.
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma whne_isConstruct_app flags Σ Γ t :
  isConstruct_app t ->
  whne flags Σ Γ t ->
  False.
Proof.
  intros ctor wh.
  unfold isConstruct_app in *.
  destruct decompose_app eqn:decomp.
  destruct t0; try easy.
  apply decompose_app_notApp in decomp as notapp.
  apply decompose_app_inv in decomp as ->.
  cbn in *.
  eapply whne_mkApps_inv in wh as [[wh|(? & ? & ? & ? & e & _)]|(? & ? & ? & ? & e & _)];
    try reflexivity; try discriminate.
  depelim wh; help.
Qed.

Lemma whnf_mkApps_tSort_inv f Σ Γ s args :
  whnf f Σ Γ (mkApps (tSort s) args) -> args = [].
Proof.
  intros wh.
  inversion wh; solve_discr.
  clear -X.
  remember (mkApps (tSort s) args) eqn:teq.
  exfalso.
  revert teq.
  induction X in args |- *; intros; solve_discr.
  destruct args as [|? ? _] using MRList.rev_ind; [easy|].
  rewrite mkApps_app in teq.
  cbn in teq.
  inv teq.
  eauto.
Qed.

Lemma whnf_mkApps_tProd_inv f Σ Γ na A B args :
  whnf f Σ Γ (mkApps (tProd na A B) args) -> args = [].
Proof.
  intros wh.
  inversion wh; solve_discr.
  clear -X.
  remember (mkApps (tProd na A B) args) eqn:teq.
  exfalso.
  revert teq.
  induction X in args |- *; intros; solve_discr.
  destruct args as [|? ? _] using List.rev_ind; [easy|].
  rewrite mkApps_app in teq.
  cbn in teq.
  inv teq.
  eauto.
Qed.

Lemma whnf_mkApps_tLambda_inv f Σ Γ na A b args :
  RedFlags.beta f = true ->
  whnf f Σ Γ (mkApps (tLambda na A b) args) -> args = [].
Proof.
  intros nobeta wh.
  inversion wh; solve_discr.
  clear -X nobeta.
  remember (mkApps (tLambda na A b) args) eqn:teq.
  exfalso.
  revert teq.
  induction X in args |- *; intros; solve_discr.
  destruct args as [|? ? _] using List.rev_ind; [easy|].
  rewrite mkApps_app in teq.
  cbn in teq.
  inv teq.
  eauto.
Qed.

Section whne_red1_ind.
Context (flags : RedFlags.t).
Context (Σ : global_env).
Context (Γ : context).
Context (P : term -> term -> Type).

Lemma whne_red1_ind {cf:checker_flags} {wfΣ : wf Σ}
      (Hlam_nobeta_1 : forall na A b M',
          RedFlags.beta flags = false ->
          red1 Σ Γ A M' ->
          P (tLambda na A b) (tLambda na M' b))
      (Hlam_nobeta_2 : forall na A b M',
          RedFlags.beta flags = false ->
          red1 Σ (Γ,, vass na A) b M' ->
          P (tLambda na A b) (tLambda na A M'))
      (Hevar : forall n l l',
          OnOne2 (red1 Σ Γ) l l' ->
          P (tEvar n l) (tEvar n l'))
      (Hletin_nozeta_1 :
         forall t' na B b t,
           RedFlags.zeta flags = false ->
           red1 Σ Γ (tLetIn na B b t) t' ->
           P (tLetIn na B b t) t')
      (Hconst_nodelta : forall t' c u,
          RedFlags.delta flags = false ->
          red1 Σ Γ (tConst c u) t' ->
          P (tConst c u) t')
      (Hbeta_nobeta :
         forall na t b v,
           RedFlags.beta flags = false ->
           P (tApp (tLambda na t b) v) (b{0 := v}))
      (Hfix_nofix :
         forall v mfix idx args narg fn,
           RedFlags.fix_ flags = false ->
           nth_error mfix idx = Some narg ->
           is_constructor (rarg narg) (args ++ [v]) = true ->
           P (mkApps (tFix mfix idx) (args ++ [v])) (mkApps fn (args ++ [v])))
      (Happ_1 : forall f v N1,
          whne flags Σ Γ f ->
          red1 Σ Γ f N1 ->
          P f N1 ->
          P (tApp f v) (tApp N1 v))
      (Happ_2 : forall f v N2,
          whne flags Σ Γ f ->
          red1 Σ Γ v N2 ->
          P (tApp f v) (tApp f N2))
      (Hfix_red_arg : forall mfix idx args narg arg x,
          nth_error mfix idx = Some narg ->
          nth_error args (rarg narg) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2 (fun a a' => red1 Σ Γ a a') args x ->
          (forall t', red1 Σ Γ arg t' -> P arg t') ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix mfix idx) x))
      (Hfix_red_def_type : forall mfix idx args d arg x,
          nth_error mfix idx = Some d ->
          nth_error args (rarg d) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2
            (fun x y : def term =>
               red1 Σ Γ (dtype x) (dtype y) *
               ((dname x, dbody x, BasicAst.rarg x) =
                (dname y, dbody y, BasicAst.rarg y))) mfix x ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix x idx) args))
      (Hfix_red_def_body : forall mfix idx args narg arg x,
          nth_error mfix idx = Some narg ->
          nth_error args (rarg narg) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2
            (fun x y : def term =>
               red1 Σ (Γ ,,, fix_context mfix) (dbody x) (dbody y) *
               ((dname x, dtype x, BasicAst.rarg x) =
                (dname y, dtype y, BasicAst.rarg y))) mfix x ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix x idx) args))
      (Hfix_red_type_nofix : forall defs i mfix1,
          RedFlags.fix_ flags = false ->
          OnOne2
            (fun x y : def term =>
               red1 Σ Γ (dtype x) (dtype y) *
               ((dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)))
            defs mfix1 ->
          P (tFix defs i) (tFix mfix1 i))
      (Hfix_red_body_nofix : forall defs i mfix1,
          RedFlags.fix_ flags = false ->
          OnOne2
            (fun x y : def term =>
               red1 Σ (Γ ,,, fix_context defs) (dbody x) (dbody y) *
               ((dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)))
            defs mfix1 ->
          P (tFix defs i) (tFix mfix1 i))
      (Hcase_params : forall i p c brs params',
          whne flags Σ Γ c ->
          OnOne2 (red1 Σ Γ) p.(pparams) params' ->
          P (tCase i p c brs) (tCase i (set_pparams p params') c brs))
      (Hcase_motive : forall i  p c brs p',
          whne flags Σ Γ c ->
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) p' ->
          P (tCase i p c brs) (tCase i (set_preturn p p') c brs))
      (Hcase_discr : forall i p c brs c',
          whne flags Σ Γ c ->
          red1 Σ Γ c c' ->
          P c c' ->
          P (tCase i p c brs) (tCase i p c' brs))
      (Hcase_branch : forall i p c brs brs',
          whne flags Σ Γ c ->
          OnOne2 (fun br br' =>
            let ctx := inst_case_branch_context p br in
            (on_Trel_eq (red1 Σ (Γ ,,, ctx)) bbody bcontext br br')%type)
            brs brs' ->
          P (tCase i p c brs) (tCase i p c brs'))
      (Hcase_noiota : forall t' i p c brs,
          RedFlags.iota flags = false ->
          red1 Σ Γ (tCase i p c brs) t' ->
          P (tCase i p c brs) t')
      (Hproj : forall p c c',
          whne flags Σ Γ c ->
          red1 Σ Γ c c' ->
          P c c' ->
          P (tProj p c) (tProj p c'))
      (Hproj_cofix_noiota : forall p mfix idx args narg fn,
          RedFlags.iota flags = false ->
          unfold_cofix mfix idx = Some (narg, fn) ->
          P (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args)))
      (Hproj_noiota : forall p args u arg,
          RedFlags.iota flags = false ->
          nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
          P (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg)
      (Hproj_discr_noiota : forall p c c',
          RedFlags.iota flags = false ->
          red1 Σ Γ c c' ->
          P (tProj p c) (tProj p c'))
      (Hprimapp_stuck : forall c u decl op ls a rest t',
          lookup_env Σ c = Some (ConstantDecl decl) ->
          decl.(cst_body) = None ->
          prim_op_of Σ c = Some op ->
          #|ls| + S #|rest| = arity op ->
          whne flags Σ Γ a ->
          (forall a', red1 Σ Γ a a' -> P a a') ->
          red1 Σ Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) t' ->
          P (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) t')
      (Hprimapp_inert : forall c u decl op ls t',
          lookup_env Σ c = Some (ConstantDecl decl) ->
          decl.(cst_body) = None ->
          prim_op_of Σ c = Some op ->
          #|ls| = arity op ->
          prim_reduct Σ op (map term_of_lit ls) = None ->
          red1 Σ Γ (mkApps (tConst c u) (map term_of_lit ls)) t' ->
          P (mkApps (tConst c u) (map term_of_lit ls)) t')
      (* Under [nodelta] every constant is neutral ([whne_const_nodelta]), so a
         registered application is neutral there too, and the rule still fires:
         [red1] does not read the flags.  Vacuous at [RedFlags.default]. *)
      (Hprimapp_nodelta : forall c u decl op ls r v,
          RedFlags.delta flags = false ->
          prim_op_of Σ c = Some op ->
          declared_constant Σ c decl ->
          cst_body decl = None ->
          prim_op_denote op ls = Some r ->
          readback Σ (po_shape (info op)) r = Some v ->
          P (mkApps (tConst c u) (map term_of_lit ls)) v) :
  forall t t', whne flags Σ Γ t -> red1 Σ Γ t t' -> P t t'.
Proof using Type.
  intros t t' wh r.
  induction wh in t, t', wh, r |- *; cbn in *.
  - depelim r; try congruence; solve_discr.
  - depelim r; solve_discr; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; eauto.
  - eauto.
  - depelim r; solve_discr; try congruence.
    unshelve eapply declared_constant_to_gen in isdecl; try exact wfΣ.
    unfold declared_constant, declared_constant_gen in isdecl.
    rewrite e in isdecl.
    inv isdecl.
    congruence.
  - eauto.
  - depelim r; eauto.
    + depelim wh; solve_discr.
      now apply Hbeta_nobeta.
    + unfold unfold_fix in *.
      destruct args as [|? ? _] using MRList.rev_ind; [now solve_discr|].
      rewrite mkApps_app in x.
      cbn in *.
      inv x.
      eapply whne_mkApps_inv in wh as [wh|(? & ? & ? & ? & e3 & _)]; [|discriminate|easy].
      destruct wh as [|].
      * depelim w; try congruence.
        all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                  try reflexivity; cbn in x; noconf x).
        -- exfalso. match goal with H : nth_error [] ?n = Some _ |- _ =>
             now rewrite nth_error_nil in H end.
        -- rewrite <- mkApps_snoc.
           case_eq (nth_error mfix idx); [intros d H|intros H];
             rewrite H in e; [|discriminate].
           noconf e. eapply Hfix_nofix; eauto.
      * destruct s as (?&?&?&?&?&?&?&?).
        inv e1.
        rewrite e2 in e.
        inv e.
        unfold is_constructor in e0.
        erewrite nth_error_app_left in e0 by eassumption.
        now apply whne_isConstruct_app in w; auto.
    + (* red_prim_op: the head would have to be neutral, but it is an
         unsaturated application of a registered operation. *)
      destruct ls as [|l ls _] using MRList.rev_ind; [now cbn in x|].
      rewrite map_app mkApps_app /= in x. noconf x.
      case_eq (RedFlags.delta flags); intros hd.
      2:{ pose proof (Hprimapp_nodelta c u decl op (ls ++ [l]) r v0 hd e d e0 e1 e2) as hp.
          rewrite map_app mkApps_app /= in hp. exact hp. }
      exfalso.
      pose proof (prim_op_denote_args _ _ _ e1) as hargs.
      rewrite map_app /= in hargs.
      assert (harity : arity op = S #|ls|)
        by (unfold arity; rewrite -hargs length_app length_map /=; lia).
      eapply whne_mkApps_inv in wh
        as [[w|(? & ? & ? & ? & e3 & _)]|(? & ? & ? & op' & e3 & _ & _ & hop' & hle & _)];
        try reflexivity; try discriminate.
      * eapply whne_tConst_prim with (op := op); [exact hd|exact e| |exact w]. lia.
      * noconf e3. rewrite e in hop'. noconf hop'.
        rewrite length_map in hle. lia.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { unfold unfold_fix. rewrite e.
         unfold is_constructor.
         rewrite e0.
         destruct isConstruct_app eqn:ctor; [|easy].
         now eapply whne_isConstruct_app in ctor. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
  - depelim r; eauto.
    all: try solve [help].
    destruct args using MRList.rev_ind; [|rewrite mkApps_app in x; cbn in x; discriminate].
    cbn in *.
    unfold is_constructor in e1.
    rewrite nth_error_nil in e1; discriminate.
  - depelim r; eauto. all: try solve [help].
    + eapply whne_mkApps_inv in wh as [wh|(? & ? & ? & ? & e3 & _)]; [|discriminate|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w; try help.
      all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                try reflexivity; cbn in x; noconf x).
    + try solve_discr.
      all: eapply whne_mkApps_inv in wh as [[w|(? & ? & ? & ? & e3 & _)]|(? & ? & ? & ? & e3 & _)];
        try reflexivity; try discriminate.
      all: depelim w; help.
  - eauto.
  - depelim r; eauto. all: try solve [help].
    + try solve_discr.
      all: eapply whne_mkApps_inv in wh as [[w|(? & ? & ? & ? & e3 & _)]|(? & ? & ? & ? & e3 & _)];
        try reflexivity; try discriminate.
      all: depelim w; help.
    + eapply whne_mkApps_inv in wh as [wh|(? & ? & ? & ? & e3 & _)]; [|discriminate|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w; try help.
      all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                try reflexivity; cbn in x; noconf x).
  - depelim r; eauto. all: try solve [help|solve_discr].
  - (* whne_primapp_stuck *)
    eapply Hprimapp_stuck; eauto.
  - (* whne_primapp_inert *)
    eapply Hprimapp_inert; eauto.
Qed.
End whne_red1_ind.

Lemma whne_pres1 {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red1 Σ Γ t t' ->
  whne RedFlags.default Σ Γ t ->
  whne RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  apply (whne_red1_ind RedFlags.default Σ Γ (fun _ => whne RedFlags.default Σ Γ))
         with (t := t) (t' := t'); intros; try easy.
  - eapply OnOne2_nth_error in H0; eauto.
    destruct H0 as (?&?&[->|]).
    + eapply whne_fixapp; eauto.
    + apply X1 in r0.
      eapply whne_fixapp; eauto.
  - unfold unfold_fix in *.
    destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply OnOne2_nth_error in nth; eauto.
    inv H.
    destruct nth as (?&?&[->|(?&?)]).
    + eapply whne_fixapp; eauto.
    + eapply whne_fixapp; eauto.
      now inv e0.
  - destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply OnOne2_nth_error in nth; eauto.
    inv H.
    destruct nth as (?&?&[->|(?&?)]).
    + eapply whne_fixapp; eauto.
    + eapply whne_fixapp; eauto.
      now inv e0.
  - (* Hprimapp_stuck: a stuck primitive application steps inside an argument *)
    clear r wh.
    rename c into c0, u into u0, decl into decl0, op into op0,
           ls into ls0, a into a0, rest into rest0.
    match goal with [ H : lookup_env _ _ = _ |- _ ] => rename H into hl0 end.
    match goal with [ H : cst_body _ = None |- _ ] => rename H into hb0 end.
    match goal with [ H : prim_op_of _ _ = Some _ |- _ ] => rename H into hop0 end.
    match goal with [ H : _ + S _ = arity _ |- _ ] => rename H into hlen0 end.
    match goal with [ H : red1 _ _ (mkApps _ _) _ |- _ ] => rename H into hr0 end.
    assert (hle : #|map term_of_lit ls0 ++ a0 :: rest0| <= arity op0)
      by (rewrite length_app length_map /=; lia).
    assert (ha0 : lit_of_term a0 = None)
      by (eapply whne_not_lit; eassumption).
    assert (hcf : prim_reduct Σ op0 (map term_of_lit ls0 ++ a0 :: rest0) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app ha0) //).
    eapply red1_mkApps_tConst_inv in hr0 as (args' & -> & ho); try eassumption.
    assert (hnolit : forall l t, red1 Σ Γ (term_of_lit l) t -> False)
      by (intros ? ? Hl; eapply red1_term_of_lit; exact Hl).
    destruct (OnOne2_primapp_split _ _ _ _ hnolit ho) as [(a'&->&ra)|(rest'&->&ho')].
    + eapply whne_primapp_stuck; [ eassumption .. | ].
      match goal with
      | [ Hih : forall _, red1 _ _ _ _ -> whne _ _ _ _ |- _ ] => eapply Hih; exact ra
      end.
    + eapply whne_primapp_stuck; [ eassumption | eassumption | eassumption | | eassumption ].
      now rewrite -(OnOne2_length ho').
  - (* Hprimapp_inert: a literal application cannot step *)
    exfalso.
    match goal with
    | [ Hr : red1 _ _ (mkApps (tConst _ _) (map term_of_lit ?ls0)) _ |- _ ] =>
        eapply (red1_mkApps_tConst_inv _ _ _ _ _ _ (map term_of_lit ls0))
          in Hr as (args' & _ & ho)
    end.
    2-4: eassumption.
    2: rewrite length_map; lia.
    2: eassumption.
    eapply OnOne2_map_term_of_lit; exact ho.
Qed.

Lemma whne_pres {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red Σ Γ t t' ->
  whne RedFlags.default Σ Γ t -> whne RedFlags.default Σ Γ t'.
Proof.
  induction 1 using red_rect_n1; eauto using whne_pres1.
Qed.

(** The named rigidity obligation of [whnf_primapp_rigid]: a default weak-head
    normal form that is not a literal never [red1]-steps to a literal.  Every
    [red1] rule whose reduct is a [tPrim] integer or string literal has a
    non-whnf left-hand side (it is a root redex), so a whnf only steps inside a
    subterm and keeps its head; the sole head that reads back as such a literal
    is [tPrim], which a non-literal whnf does not have.  Stated and proved as a
    lemma (not read off a proof), as the soundness review required. *)
Lemma whnf_lit_pres1 {cf:checker_flags} Σ {wfΣ : wf Σ} Γ a a' :
  whnf RedFlags.default Σ Γ a ->
  lit_of_term a = None ->
  red1 Σ Γ a a' ->
  lit_of_term a' = None.
Proof.
  intros wh hlit r. destruct wh.
  - (* neutral: a' is neutral, hence not a literal *)
    eapply whne_not_lit. eapply whne_pres1; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; reflexivity.
  - depelim r; solve_discr; reflexivity.
  - apply red1_mkApps_tConstruct_inv in r as (v'&->&_).
    destruct v' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
  - apply red1_mkApps_tInd_inv in r as (v'&->&_).
    destruct v' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
  - assert (hnc : match unfold_fix mfix idx with
                  | Some (rarg, _) => is_constructor rarg args = false
                  | None => True end).
    { unfold unfold_fix. destruct o as [[? [-> ?]]|hn];
      [now unfold is_constructor; rewrite H|now rewrite hn]. }
    eapply red1_mkApps_tFix_inv in r as [[(v'&->&_)|(mfix'&->&_)]|(mfix'&->&_)]; tea.
    all: match goal with |- lit_of_term (mkApps _ ?l) = None =>
           destruct l using MRList.rev_ind end; rewrite ?mkApps_snoc; reflexivity.
  - apply red1_mkApps_tCoFix_inv in r as [[(v'&->&_)|(mfix'&->&_)]|(mfix'&->&_)];
      match goal with |- lit_of_term (mkApps _ ?l) = None =>
        destruct l using MRList.rev_ind end; rewrite ?mkApps_snoc; reflexivity.
  - cbn in hlit. depelim r; solve_discr; cbn; reflexivity.
  - (* partial: cannot fire (too few arguments); reduces inside an argument *)
    assert (hcf : prim_reduct Σ op args = None) by now apply prim_reduct_short.
    assert (hle : #|args| <= arity op) by lia.
    eapply red1_mkApps_tConst_inv in r as (args'&->&_); try eassumption.
    destruct args' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
  - (* rigid: cannot fire (a non-literal argument); reduces inside an argument *)
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    assert (hcf : prim_reduct Σ op (map term_of_lit ls ++ a :: rest) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app e3) //).
    eapply red1_mkApps_tConst_inv in r as (args'&->&_); try eassumption.
    destruct args' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
Qed.

Lemma whnf_pres1 {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red1 Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t ->
  whnf RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  induction wh in wh, t, t', r |- *; cbn in *.
  - constructor.
    now eapply whne_pres1.
  - depelim r; solve_discr.
  - depelim r; try easy; solve_discr.
  - depelim r; try easy; solve_discr.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_cstrapp.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_indapp.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { unfold unfold_fix. destruct o as [[? [-> ?]] | ];
        unfold is_constructor; now rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_fixapp. destruct o as [[d [? ?]] | ]; [left ; exists d| easy].
      split; eauto.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H0.
      lia.
    + apply whnf_fixapp.
      destruct o as [[d [? ?]] | ]; [left| right].
      eapply OnOne2_sym in o0.
      eapply OnOne2_nth_error_r in o0; eauto.
      destruct o0 as [? [? ?]]. eexists; split; eauto.
      destruct s as [| [? ?]]. now subst. now inv e0.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
    + apply whnf_fixapp.
      destruct o as [[d [? ?]] | ]; [left| right].
      eapply OnOne2_sym in o0.
      eapply OnOne2_nth_error_r in o0; eauto.
      destruct o0 as [? [? ?]]. eexists; split; eauto.
      destruct s as [| [? ?]]. now subst. now inv e0.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
  - eapply red1_mkApps_tCoFix_inv in r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
  - depelim r; solve_discr; eapply whnf_prim.
  - (* whnf_primapp_partial: still unsaturated after a step inside an argument *)
    assert (hle : #|args| <= arity op) by lia.
    assert (hcf : prim_reduct Σ op args = None) by now apply prim_reduct_short.
    eapply red1_mkApps_tConst_inv in r as (args'&->&ho); try eassumption.
    eapply whnf_primapp_partial; try eassumption.
    apply OnOne2_length in ho; lia.
  - (* whnf_primapp_rigid: still blocked on a whnf non-literal after a step *)
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    assert (hcf : prim_reduct Σ op (map term_of_lit ls ++ a :: rest) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app e3) //).
    eapply red1_mkApps_tConst_inv in r as (args'&->&ho); try eassumption.
    assert (hnolit : forall l t, red1 Σ Γ (term_of_lit l) t -> False)
      by (intros ? ? Hl; eapply red1_term_of_lit; exact Hl).
    destruct (OnOne2_primapp_split _ _ _ _ hnolit ho) as [(a'&->&ra)|(rest'&->&ho')].
    + eapply whnf_primapp_rigid; try eassumption.
      * match goal with
        | [ H : forall _, red1 _ _ a _ -> whnf _ _ _ _ |- _ ] => eapply H; exact ra
        end.
      * eapply whnf_lit_pres1; try eassumption.
    + eapply whnf_primapp_rigid; try eassumption.
      now rewrite -(OnOne2_length ho').
Qed.

Lemma whnf_pres {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  red Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t -> whnf RedFlags.default Σ Γ t'.
Proof.
  induction 1 using red_rect_n1; eauto using whnf_pres1.
Qed.

#[global]
Hint Resolve All2_same All2_firstn All2_skipn OnOne2_All2 red_mkApps All2_app : pcuic.

(* For terms in whnf we have a very useful inversion lemma for reductions.
   This next relation is a subrelation of red that classifies how whnf terms reduce. *)
Inductive whnf_red Σ Γ : term -> term -> Type :=
| whnf_red_tRel i :
    option_map decl_body (nth_error Γ i) = Some None ->
    whnf_red Σ Γ (tRel i) (tRel i)
| whnf_red_tVar id : whnf_red Σ Γ (tVar id) (tVar id)
| whnf_red_tEvar n l l' :
    All2 (red Σ Γ) l l' ->
    whnf_red Σ Γ (tEvar n l) (tEvar n l')
| whnf_red_tConst kn u decl :
    lookup_env Σ kn = Some (ConstantDecl decl) ->
    cst_body decl = None ->
    whnf_red Σ Γ (tConst kn u) (tConst kn u)
| whnf_red_tApp hd hd' arg arg' :
    whnf_red Σ Γ hd hd' ->
    red Σ Γ arg arg' ->
    whnf_red Σ Γ (tApp hd arg) (tApp hd' arg')
| whnf_red_tFix mfix mfix' idx :
    All2 (fun d d' => dname d = dname d' ×
                      rarg d = rarg d' ×
                      red Σ Γ (dtype d) (dtype d') ×
                      red Σ (Γ,,, fix_context mfix) (dbody d) (dbody d'))
         mfix mfix' ->
    whnf_red Σ Γ (tFix mfix idx) (tFix mfix' idx)
| whnf_red_tCase ci motive motivepars motiveret discr discr' brs brs' :
    All2 (red Σ Γ) motive.(pparams) motivepars ->

    red Σ (Γ ,,, inst_case_predicate_context motive) motive.(preturn) motiveret ->
    red Σ Γ discr discr' ->
    All2 (fun br br' =>
      red Σ (Γ ,,, inst_case_branch_context motive br) br.(bbody) br'.(bbody) ×
      bcontext br = bcontext br') brs brs' ->
    whnf_red Σ Γ (tCase ci motive discr brs)
      (tCase ci {| pparams := motivepars;
                  puinst := motive.(puinst);
                  pcontext := motive.(pcontext);
                  preturn := motiveret |} discr' brs')
| whnf_red_tProj p c c' :
    red Σ Γ c c' ->
    whnf_red Σ Γ (tProj p c) (tProj p c')
| whnf_red_tSort s : whnf_red Σ Γ (tSort s) (tSort s)
| whnf_red_tProd na A A' B B' :
    red Σ Γ A A' ->
    red Σ (Γ,, vass na A) B B' ->
    whnf_red Σ Γ (tProd na A B) (tProd na A' B')
| whnf_red_tLambda na A A' B B' :
    red Σ Γ A A' ->
    red Σ (Γ,, vass na A) B B' ->
    whnf_red Σ Γ (tLambda na A B) (tLambda na A' B')
| whnf_red_tConstruct i n u :
    whnf_red Σ Γ (tConstruct i n u) (tConstruct i n u)
| whnf_red_tInd i u :
    whnf_red Σ Γ (tInd i u) (tInd i u)
| whnf_red_tCoFix mfix mfix' idx :
    All2 (fun d d' => dname d = dname d' ×
                      rarg d = rarg d' ×
                      red Σ Γ (dtype d) (dtype d') ×
                      red Σ (Γ,,, fix_context mfix) (dbody d) (dbody d'))
         mfix mfix' ->
    whnf_red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx)
| whnf_red_tPrim i i' :
  onPrims (red Σ Γ) eq i i' ->
  whnf_red Σ Γ (tPrim i) (tPrim i').

Derive Signature for whnf_red.

#[global]
Hint Constructors whnf_red : pcuic.

Lemma All3_impl {A B C} (P Q : A -> B -> C -> Type) {l l' l''}
  (a : All3 P l l' l'') :
  (forall x y z, P x y z -> Q x y z) ->
  All3 Q l l' l''.
Proof.
  intros HPQ; induction a; constructor; auto.
Qed.

Lemma whnf_red_red Σ Γ t t' :
  whnf_red Σ Γ t t' ->
  red Σ Γ t t'.
Proof.
  intros wh.
  induction wh; eauto with pcuic.
  - apply red_evar; auto.
  - apply red_app; auto.
  - apply red_fix_congr.
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&r1&r2).
    eauto.
  - eapply red_case; eauto.
  - apply red_proj_c; auto.
  - apply red_prod; auto.
  - apply red_abs; auto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; [|constructor].
    apply All2_fold_refl.
    reflexivity.
  - apply red_cofix_congr.
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&r1&r2).
    eauto.
  - depelim o. 1-3: reflexivity.
    eapply red_primArray_congr; eauto.
    now eapply Universe.make'_inj in e.
Qed.

#[global]
Hint Resolve whnf_red_red : pcuic.

Lemma whnf_red_mkApps Σ Γ hd hd' args args' :
  whnf_red Σ Γ hd hd' ->
  All2 (red Σ Γ) args args' ->
  whnf_red Σ Γ (mkApps hd args) (mkApps hd' args').
Proof.
  intros r ra.
  induction ra using All2_rect_rev; auto.
  rewrite !mkApps_app.
  cbn.
  constructor; auto.
Qed.

#[global]
Hint Resolve whnf_red_mkApps : pcuic.

Lemma whnf_red_mkApps_l_inv Σ Γ hd args t :
  whnf_red Σ Γ (mkApps hd args) t ->
  ∑ hd' args',
    t = mkApps hd' args' × whnf_red Σ Γ hd hd' × All2 (red Σ Γ) args args'.
Proof.
  intros r.
  revert hd t r.
  induction args using MRList.rev_ind; intros hd t r.
  - cbn in *.
    eexists _, []; split; [reflexivity|].
    eauto with pcuic.
  - rewrite mkApps_app in r.
    cbn in r.
    depelim r.
    apply IHargs in r as (?&?&->&?&?); auto.
    exists x0, (x1 ++ [arg']).
    rewrite mkApps_app.
    eauto with pcuic.
Qed.

Lemma whnf_red_mkApps_r_inv Σ Γ t hd' args' :
  whnf_red Σ Γ t (mkApps hd' args') ->
  ∑ hd args,
    t = mkApps hd args × whnf_red Σ Γ hd hd' × All2 (red Σ Γ) args args'.
Proof.
  intros r.
  revert hd' t r.
  induction args' using MRList.rev_ind; intros hd' t r.
  - cbn in *.
    eexists _, []; split; [reflexivity|].
    eauto with pcuic.
  - rewrite mkApps_app in r.
    cbn in r.
    depelim r.
    apply IHargs' in r as (?&?&->&?&?); auto.
    exists x0, (x1 ++ [arg]).
    rewrite mkApps_app.
    eauto with pcuic.
Qed.

Lemma whnf_red_mkApps_inv Σ Γ hd args hd' args' :
  whnf_red Σ Γ (mkApps hd args) (mkApps hd' args') ->
  isApp hd = false ->
  isApp hd' = false ->
  whnf_red Σ Γ hd hd' × All2 (red Σ Γ) args args'.
Proof.
  intros r notapp notapp'.
  apply whnf_red_mkApps_l_inv in r as (?&?&eq&?&?); auto.
  apply mkApps_notApp_inj in eq as (->&->); auto.
  now depelim w.
Qed.

Lemma whnf_red_refl_whne Σ Γ t :
  whne RedFlags.default Σ Γ t ->
  whnf_red Σ Γ t t.
Proof.
  intros wh.
  induction wh; cbn in *; try discriminate; eauto using whnf_red with pcuic.
  - apply whnf_red_mkApps; auto.
     2: apply All2_same; auto.
    constructor.
    apply All2_same; auto.
  - destruct p. econstructor; simpl; eauto.
    * eapply All2_same; auto.
    * eapply All2_same; intuition auto.
Qed.

Lemma whnf_red_refl Σ Γ t :
  whnf RedFlags.default Σ Γ t ->
  whnf_red Σ Γ t t.
Proof.
  intros wh.
  induction wh; cbn in *; try discriminate; eauto with pcuic.
  - eapply whnf_red_refl_whne; eauto.
  - apply whnf_red_mkApps; auto.
    2: apply All2_same; auto.
    constructor.
    apply All2_same; auto.
  - apply whnf_red_mkApps; auto.
    2: apply All2_same; auto.
    constructor.
    apply All2_same; auto.
  - constructor. destruct p as [? []]; constructor; eauto. eapply All2_same; auto.
Qed.

Ltac inv_on_free_vars :=
  match goal with
  | [ H : is_true (on_free_vars_decl _ _) |- _ ] => progress cbn in H
  | [ H : is_true (on_free_vars_decl _ (vdef _ _ _)) |- _ ] => unfold on_free_vars_decl, test_decl in H
  | [ H : is_true (_ && _) |- _ ] =>
    move/andP: H => []; intros
  | [ H : is_true (on_free_vars ?P ?t) |- _ ] =>
    progress (cbn in H || rewrite on_free_vars_mkApps in H);
    (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] ||
      eapply forallb_All in H); intros
  | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
    move/andP: H => []; rewrite ?shiftnP_xpredT; intros
  | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
    rewrite -> test_context_k_closed_on_free_vars_ctx in H
  end.

From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity PCUICOnFreeVars PCUICConfluence PCUICSR PCUICConversion PCUICSubstitution.

Lemma red_ctx_rel_subst {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} P Γ Γ' s s' Δ :
  All2 (red Σ Γ) s s' ->
  All (on_free_vars (shiftnP #|Γ| P)) s ->
  untyped_subslet Γ s Γ' ->
  on_free_vars_ctx P (Γ ,,, Γ' ,,, Δ) ->
  red_context_rel Σ Γ (subst_context s 0 Δ) (subst_context s' 0 Δ).
Proof.
  intros Hs ons subs onctx.
  induction Δ; cbn.
  * rewrite !subst_context_nil. constructor.
  * move: onctx => /=. rewrite on_free_vars_ctx_snoc => /andP[] onctx ona.
    rewrite !subst_context_snoc !Nat.add_0_r.
    constructor; eauto.
    now apply IHΔ.
    destruct a as [na [b|] ty]; constructor; cbn.
    relativize #|Δ|. eapply red_red; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
    relativize #|Δ|. eapply red_red; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
    relativize #|Δ|. eapply red_red; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
Qed.

Definition fake_params n : context :=
    unfold n (fun x => {| decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                          decl_body := None;
                          decl_type := tSort Sort.type0 |}).

Lemma fake_params_length n : #|fake_params n| = n.
Proof.
  induction n; simpl; auto. cbn.
  now rewrite length_app IHn /= Nat.add_1_r.
Qed.

Lemma params_subslet {cf:checker_flags} Γ pars :
  untyped_subslet Γ pars (List.rev (fake_params #|pars|)).
Proof.
  induction pars; cbn. constructor.
  rewrite List.rev_app_distr /=. constructor; auto.
Qed.

Lemma closed_fake_params n P :
  on_free_vars_ctx P (List.rev (fake_params n)).
Proof.
  unfold on_free_vars_ctx. generalize 0. rewrite List.rev_involutive.
  induction n; cbn => //.
  intros n'.
  rewrite alli_app IHn /= //.
Qed.

Lemma red_terms_on_free_vars {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ ts us}:
  is_closed_context Γ ->
  forallb (is_open_term Γ) ts ->
  All2 (red Σ Γ) ts us ->
  forallb (is_open_term Γ) us.
Proof.
  solve_all. eapply red_on_free_vars; tea.
  now rewrite on_free_vars_ctx_on_ctx_free_vars.
Qed.

Definition br_fvs (Γ : context) (motive : predicate term) br :=
  test_context_k (fun k : nat => on_free_vars (closedP k xpredT))
    #|pparams motive| (bcontext br) &&
  on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br).

Lemma br_fvs_pres {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ motive brs brs' :
  is_closed_context Γ ->
  forallb (is_open_term Γ) (pparams motive) ->
  All (br_fvs Γ motive) brs ->
  All2
    (fun br br' : branch term =>
    red Σ (Γ,,, inst_case_branch_context motive br)
       (bbody br) (bbody br') * (bcontext br = bcontext br')) brs brs' ->
  All (br_fvs Γ motive) brs'.
Proof.
  intros clΓ clpars.
  unfold br_fvs; solve_all.
  now rewrite b0 in H.
  rewrite -b0. eapply red_on_free_vars; tea.
  rewrite shiftnP_add. relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
  2:len.
  rewrite on_free_vars_ctx_app clΓ /=.
  eapply on_free_vars_ctx_inst_case_context; trea. solve_all.
Qed.

Lemma whnf_red_trans {cf:checker_flags} {Σ : global_env_ext} Γ x y z : wf Σ ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  whnf_red Σ Γ x y ->
  whnf_red Σ Γ y z ->
  whnf_red Σ Γ x z.
Proof.
  intros wf onΓ onx xy yz.
  revert onx z yz.
  (* [Equations.Prop.DepElim.depelim] is written out here and below on purpose. In this file a plain
     [depelim] is Stdlib Program's, because [Program] is imported after [Equations]; Program's version
     discharges the [existT] equations with [simplification_existT2], which uses the axiom
     [Eqdep.Eq_rect_eq.eq_rect_eq] (UIP). Equations' version needs no axiom here. Do not shorten it
     back to [depelim]: that silently puts the axiom back into every checker that uses this lemma. *)
  induction xy; intros onx z yz; Equations.Prop.DepElim.depelim yz; repeat inv_on_free_vars; eauto using whnf_red.
  - constructor.
    eapply All2_trans; eauto.
    typeclasses eauto.
  - constructor; eauto.
    all: try etransitivity; eauto.
  - constructor.
    eapply All2_trans; eauto.
    1: { intros ? ? ? (->&->&?&?) (->&->&?&?).
         do 2 (split; auto).
         split; etransitivity; eauto. }
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&?&?).
    do 3 (split; auto).
    eapply context_pres_let_bodies_red; eauto.
    apply fix_context_pres_let_bodies.
    now apply All2_length in a.
  - simpl in *.
    constructor; try solve [etransitivity; eauto].
    + eapply All2_trans; eauto.
      typeclasses eauto.
    + etransitivity; [eassumption|].
      have clp: on_ctx_free_vars (closedP #|Γ,,, inst_case_predicate_context motive| xpredT)
        (Γ,,, inst_case_predicate_context motive).
      { rewrite closedP_shiftnP_eq on_free_vars_ctx_on_ctx_free_vars.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
        rewrite test_context_k_closed_on_free_vars_ctx //. }
      eapply red_red_ctx. 5:tea. all:eauto; revgoals.
      apply red_context_app_right; eauto.
      * apply red_context_refl.
      * rewrite /inst_case_predicate_context /=.
        rewrite /inst_case_context.
        eapply (red_ctx_rel_subst (Σ := empty_ext Σ)).
        eapply All2_rev => //.
        eapply All_rev. solve_all.
        instantiate (1 := List.rev (fake_params #|pparams motive|)).
        rewrite -(List.length_rev (pparams motive)).
        eapply params_subslet.
        rewrite !on_free_vars_ctx_app onΓ /=. len.
        rewrite on_free_vars_ctx_subst_instance.
        rewrite closed_fake_params /=.
        setoid_rewrite closedP_shiftnP_eq in p1.
        eapply on_free_vars_ctx_impl; tea.
        rewrite /shiftnP. intros i. rewrite !orb_false_r.
        move/Nat.ltb_lt => ?. apply Nat.ltb_lt. lia.
      * eapply red_on_free_vars; tea.
        len. rewrite closedP_shiftnP_eq -shiftnP_add //.
      * rewrite closedP_shiftnP_eq.
        relativize #|Γ ,,, _|; [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //. cbn.
        eapply red_terms_on_free_vars; tea.
        rewrite test_context_k_closed_on_free_vars_ctx -(All2_length a) //.

    + eapply forallb_All in p3.
      epose proof (br_fvs_pres _ _ _ _ onΓ p p3 a0).
      eapply (All2_impl (P:=fun br br' => br_fvs Γ motive br ×
        red Σ (Γ,,, inst_case_branch_context motive br) (bbody br) (bbody br') *
            (bcontext br = bcontext br'))).
      2:intuition.
      eapply All2_trans with brs'.
      { clear -wf p.
        intros br br' br''. intuition auto. 2:congruence.
        etransitivity; tea. unfold inst_case_branch_context in *. now rewrite -b1 in a2. }
      1:solve_all.
      eapply All2_All_mix_left in a2; tea. eapply All2_impl; tea.
      intros br br'; cbn. intuition auto.
      unfold br_fvs in a3.
      move/andP: a3 => [] fvbctx fvbr.
      eapply red_red_ctx. 5:tea. all:eauto; revgoals.
      apply red_context_app_right; eauto.
      * rewrite closedP_shiftnP_eq on_free_vars_ctx_on_ctx_free_vars.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
      * apply red_context_refl.
      * rewrite /inst_case_branch_context /=.
        rewrite /inst_case_context.
        eapply (red_ctx_rel_subst (Σ := empty_ext Σ)).
        eapply All2_rev => //.
        eapply All_rev. solve_all.
        instantiate (1 := List.rev (fake_params #|pparams motive|)).
        rewrite -(List.length_rev (pparams motive)).
        eapply params_subslet.
        rewrite !on_free_vars_ctx_app onΓ /=. len.
        rewrite on_free_vars_ctx_subst_instance.
        rewrite closed_fake_params /=.
        move: fvbctx.
        rewrite test_context_k_closed_on_free_vars_ctx closedP_shiftnP_eq => H.
        eapply on_free_vars_ctx_impl; tea.
        rewrite /shiftnP. intros i. rewrite !orb_false_r.
        move/Nat.ltb_lt => ?. apply Nat.ltb_lt. lia.
      * rewrite shiftnP_add.
        relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
      * rewrite shiftnP_add.
        relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
        eapply red_terms_on_free_vars; tea.
        now rewrite -(All2_length a).
  - constructor.
    etransitivity; eauto.
  - constructor; etransitivity; eauto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; eauto; [|constructor].
    apply All2_fold_refl.
    intros _ ?. reflexivity.
  - constructor; etransitivity; eauto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; eauto; [|constructor].
    apply All2_fold_refl.
    intros _ ?; reflexivity.
  - constructor.
    eapply All2_trans; eauto.
    1: { intros ? ? ? (->&->&?&?) (->&->&?&?).
         do 2 (split; auto).
         split; etransitivity; eauto. }
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&?&?).
    do 3 (split; auto).
    eapply context_pres_let_bodies_red; eauto.
    apply fix_context_pres_let_bodies.
    now apply All2_length in a.
  - (* One sentence: a sentence that starts with [Equations.] parses as the [Equations] command. *)
    constructor; Equations.Prop.DepElim.depelim o; Equations.Prop.DepElim.depelim o0; constructor; eauto.
    * etransitivity; tea.
    * etransitivity; tea.
    * etransitivity; tea.
    * eapply All2_trans; eauto.
      tc.
Qed.

Lemma whne_red1_inv {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  whne RedFlags.default Σ Γ t ->
  red1 Σ Γ t t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wh r.
  apply (whne_red1_ind
           RedFlags.default Σ Γ
           (whnf_red Σ Γ)); intros; cbn in *; try easy; eauto using whnf_red.
  - constructor.
    eapply OnOne2_All2; eauto.
  - constructor; auto.
    now apply whnf_red_refl_whne.
  - apply whnf_red_mkApps; eauto.
    1: constructor; apply All2_same; auto.
    eapply OnOne2_All2; eauto.
  - apply whnf_red_mkApps; eauto.
    + constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply All2_same; auto.
  - apply whnf_red_mkApps; eauto.
    + constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply All2_same; auto.
  - constructor; auto.
    * eapply OnOne2_All2; eauto.
    * eapply All2_same; intuition auto.
  - econstructor; auto. apply All2_same; auto.
    eapply All2_same; intuition auto.
  - destruct p; econstructor; eauto; simpl.
    * eapply All2_same; auto.
    * eapply All2_same; intuition auto.
  - destruct p;  econstructor; eauto; simpl.
    * eapply All2_same; reflexivity.
    * eapply OnOne2_All2; eauto.
      cbn. intros ? ? [? <-].
      intuition eauto; try reflexivity.
  - (* Hprimapp_stuck: the step is inside an argument; the head stays *)
    rename c into c0, u into u0, decl into decl0, op into op0,
           ls into ls0, a into a0, rest into rest0.
    match goal with [ H : red1 _ _ (mkApps _ _) _ |- _ ] => rename H into hr0 end.
    match goal with [ H : whne _ _ _ a0 |- _ ] => rename H into hw0 end.
    assert (hle : #|map term_of_lit ls0 ++ a0 :: rest0| <= arity op0)
      by (rewrite length_app length_map /=; lia).
    assert (ha0 : lit_of_term a0 = None) by (eapply whne_not_lit; exact hw0).
    assert (hcf : prim_reduct Σ op0 (map term_of_lit ls0 ++ a0 :: rest0) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app ha0) //).
    eapply red1_mkApps_tConst_inv in hr0 as (args' & -> & ho); try eassumption.
    apply whnf_red_mkApps; [econstructor; eassumption|eapply OnOne2_All2; eauto].
  - (* Hprimapp_inert: a literal application cannot step *)
    exfalso.
    rename c into c0, u into u0, decl into decl0, op into op0, ls into ls0.
    match goal with [ H : red1 _ _ (mkApps _ _) _ |- _ ] => rename H into hr0 end.
    match goal with [ H : prim_reduct _ _ _ = None |- _ ] => rename H into hcf end.
    assert (hle : #|map term_of_lit ls0| <= arity op0)
      by (rewrite length_map; lia).
    eapply red1_mkApps_tConst_inv in hr0 as (args' & _ & ho); try eassumption.
    eapply OnOne2_map_term_of_lit; exact ho.
Qed.

Lemma whnf_red1_inv {cf:checker_flags} Σ {wfΣ : wf Σ} Γ t t' :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wh r.
  destruct wh.
  - eapply whne_red1_inv; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; constructor; eauto using whnf_red.
  - depelim r; solve_discr; constructor; eauto using whnf_red.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_red_mkApps; eauto using whnf_red.
    eapply OnOne2_All2; eauto.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_red_mkApps; eauto using whnf_red.
    eapply OnOne2_All2; eauto.
  - apply red1_mkApps_tFix_inv in r.
    2: { unfold unfold_fix. destruct o as [[? [-> ?]]|];
         now unfold is_constructor; rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_red_mkApps; auto.
      2: eapply OnOne2_All2; eauto.
      constructor.
      apply All2_same; auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
  - apply red1_mkApps_tCoFix_inv in r.
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_red_mkApps; auto.
      2: eapply OnOne2_All2; eauto.
      constructor.
      apply All2_same; auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
  - depelim r; solve_discr; constructor; eauto.
    * constructor; eauto. eapply OnOne2_All2; eauto.
    * constructor; eauto. cbn. eapply All2_same; eauto.
    * constructor; eauto. cbn. eapply All2_same; eauto.
  - (* whnf_primapp_partial: the step is inside an argument; the head stays *)
    assert (hle : #|args| <= arity op) by lia.
    assert (hcf : prim_reduct Σ op args = None) by now apply prim_reduct_short.
    eapply red1_mkApps_tConst_inv in r as (args'&->&ho); try eassumption.
    apply whnf_red_mkApps; [ econstructor; eassumption | eapply OnOne2_All2; eauto ].
  - (* whnf_primapp_rigid: the step is inside an argument; the head stays *)
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    assert (hcf : prim_reduct Σ op (map term_of_lit ls ++ a :: rest) = None)
      by (rewrite /prim_reduct /lits_of_args split_lits_app //).
    eapply red1_mkApps_tConst_inv in r as (args'&->&ho); try eassumption.
    apply whnf_red_mkApps; [ econstructor; eassumption | eapply OnOne2_All2; eauto ].
Qed.

Lemma whnf_red_inv {cf:checker_flags} {Σ : global_env_ext} Γ t t' :
  wf Σ ->
  whnf RedFlags.default Σ Γ t ->
  Σ ;;; Γ ⊢ t ⇝ t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wf wh [clΓ clt r].
  induction r using red_rect_n1.
  - apply whnf_red_refl; auto.
  - eapply whnf_red1_inv in X; eauto.
    + eapply whnf_red_trans; tea.
    + eapply whnf_pres; eauto.
Qed.

Lemma whnf_red_isApp Σ Γ t t' :
  whnf_red Σ Γ t t' ->
  isApp t' = isApp t.
Proof.
  intros r.
  now depelim r.
Qed.

(** An integer or string literal is rigid under [eq_term_upto_univ]: its payload
    is compared by equality ([onPrims]), so a literal list is matched only by
    itself.  This is what keeps the literal prefix of a stuck or inert primitive
    application in place. *)
Lemma All2_eq_term_map_term_of_lit Σ cmp_universe cmp_sort ls l' :
  All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) (map term_of_lit ls) l' ->
  l' = map term_of_lit ls.
Proof.
  induction ls as [|l ls ih] in l' |- *; cbn; intros a; depelim a; [reflexivity|].
  f_equal; [|now apply ih].
  destruct l; cbn in *; depelim e; now depelim o.
Qed.

(** [eq_term_upto_univ] keeps the head, so it keeps "is not a literal". *)
Lemma eq_term_lit_of_term Σ cmp_universe cmp_sort pb napp a a' :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp a a' ->
  lit_of_term a = None ->
  lit_of_term a' = None.
Proof.
  intros e ha. destruct a' => //.
  depelim e. cbn in ha |- *.
  now depelim o.
Qed.

Lemma whne_eq_term_upto_univ_napp f Σ Γ t cmp_universe cmp_sort pb napp t' :
  whne f Σ Γ t ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t' ->
  whne f Σ Γ t'.
Proof.
  intros wh eq.
  induction wh in pb, napp, t, t', eq, wh |- *;
    try (depelim eq; solve [eauto using whne; depelim wh; solve_discr; eauto using whne]).
  - depelim eq; try solve [eauto using whne; depelim wh; solve_discr; eauto using whne].
    destruct args as [|? ? _] using MRList.rev_ind; [discriminate x|].
    rewrite mkApps_app in x; cbn in x; inv x.
    apply eq_term_upto_univ_napp_mkApps_l_inv in eq1 as (?&?&(eq_hds&?)&->).
    depelim eq_hds.
    rewrite <- mkApps_snoc.
    assert (All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Conv) (args ++ [x0]) (x1 ++ [u']))
           by (now apply All2_app).
    unfold unfold_fix in *.
    destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply All2_nth_error_Some in nth; eauto.
    destruct nth as (?&?&?&?).
    eapply All2_nth_error_Some in e0; eauto.
    inv e.
    destruct e0 as (?&?&?).
    eapply whne_fixapp.
    + unfold unfold_fix.
      rewrite e2.
      reflexivity.
    + rewrite <- e.
      destruct p as (?& eqrarg &?). rewrite eqrarg. reflexivity.
    + eapply IHwh; eauto.
    + destruct args using MRList.rev_ind;
        [now rewrite nth_error_nil in e0
        |rewrite mkApps_app in x; discriminate x].
  - (* whne_primapp_stuck: the literal prefix and the blocking argument persist *)
    apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (hd'&args'&(eq_hd&eq_args)&->).
    depelim eq_hd.
    apply All2_app_inv_l in eq_args as (l1 & l2 & -> & eqA & eqB).
    apply All2_eq_term_map_term_of_lit in eqA as ->.
    depelim eqB.
    eapply whne_primapp_stuck; tea.
    + apply All2_length in eqB. lia.
    + eapply IHwh; tea.
  - (* whne_primapp_inert: every argument is a literal, so the list is unchanged *)
    apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (hd'&args'&(eq_hd&eq_args)&->).
    depelim eq_hd.
    apply All2_eq_term_map_term_of_lit in eq_args as ->.
    now eapply whne_primapp_inert.
Qed.

Lemma whnf_eq_term_upto_univ_napp f Σ Γ t cmp_universe cmp_sort pb napp t' :
  whnf f Σ Γ t ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp t t' ->
  whnf f Σ Γ t'.
Proof.
  intros wh eq.
  induction wh in pb, napp, t, t', eq, wh |- *.
  - constructor.
    eapply whne_eq_term_upto_univ_napp; eauto.
  - depelim eq.
    apply whnf_sort.
  - depelim eq.
    apply whnf_prod.
  - depelim eq.
    apply whnf_lam.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_cstrapp.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_indapp.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_fixapp. destruct o as [[? [? ?]] |].
    eapply All2_nth_error_Some in e; eauto.
    destruct e as (? & e & ? & ? & e2 & ?).
    rewrite e. left; eexists; split; eauto. rewrite <- e2.
    eapply All2_nth_error_None; eauto.
    apply All2_length in e.
    right. apply nth_error_None.
    apply nth_error_None in H.
    lia.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (?&?&(?&?)&->).
    depelim e.
    apply whnf_cofixapp.
  - depelim eq; auto.
  - (* whnf_primapp_partial: the argument count does not change *)
    apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (hd'&args'&(eq_hd&eq_args)&->).
    depelim eq_hd.
    eapply whnf_primapp_partial; tea.
    apply All2_length in eq_args. lia.
  - (* whnf_primapp_rigid: the literal prefix and the blocking non-literal persist *)
    apply eq_term_upto_univ_napp_mkApps_l_inv in eq as (hd'&args'&(eq_hd&eq_args)&->).
    depelim eq_hd.
    apply All2_app_inv_l in eq_args as (l1 & l2 & -> & eqA & eqB).
    apply All2_eq_term_map_term_of_lit in eqA as ->.
    depelim eqB.
    eapply whnf_primapp_rigid; tea.
    + apply All2_length in eqB. lia.
    + eapply IHwh; tea.
    + eapply eq_term_lit_of_term; tea.
Qed.

Lemma whnf_eq_term {cf:checker_flags} f Σ φ Γ t t' :
  whnf f Σ Γ t ->
  eq_term Σ φ t t' ->
  whnf f Σ Γ t'.
Proof.
  apply whnf_eq_term_upto_univ_napp.
Qed.


Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  (* Relative to reduction flags *)
  Inductive ne (Γ : context) : term -> Prop :=
  | ne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      ne Γ (tRel i)

  | ne_var v :
      ne Γ (tVar v)

  | ne_evar n l :
    All (ne Γ) l ->
    ne Γ (tEvar n l)

  | ne_app f a :
    ne Γ f ->
    nf Γ a ->
    ne Γ (tApp f a)

  (* | nf_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t) *)

  | ne_const c u decl :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    ne Γ (tConst c u)

  (* | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u) *)

  (* Stuck fixpoints are neutrals *)
  | ne_fixapp mfix idx args d arg :
     nth_error mfix idx = Some d ->
     nth_error args (rarg d) = Some arg ->
     All (nf Γ) args ->
     ne Γ arg ->
     All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype)) mfix ->
     ne Γ (mkApps (tFix mfix idx) args)

  | ne_case i p c brs :
    ne Γ c ->
    All (fun br => nf (Γ ,,, inst_case_branch_context p br) br.(bbody)) brs ->
    All (nf Γ) (pparams p) ->
    onctx_rel nf Γ (inst_case_predicate_context p) ->
    nf (Γ,,, inst_case_context (pparams p) (puinst p) (pcontext p)) (preturn p) ->
    ne Γ (tCase i p c brs)

  | ne_proj p c :
    ne Γ c ->
    ne Γ (tProj p c)

  with nf (Γ : context) : term -> Prop :=
  | ne_nf t : ne Γ t -> nf Γ t

  | nf_lam na A b :
    nf Γ A ->
    nf (Γ ,, vass na A) b ->
    nf Γ (tLambda na A b)

  | nf_construct ind k u :
    nf Γ (tConstruct ind k u)

  | nf_cofix mfix idx args :
    All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype)) mfix ->
    All (nf Γ) args ->
    nf Γ (mkApps (tCoFix mfix idx) args)

  | nf_tind ind u : nf Γ (tInd ind u)
  | nf_tProd na dom codom : nf Γ dom -> nf (Γ ,, vass na dom) codom -> nf Γ (tProd na dom codom).

  Scheme nf_ne_ind := Minimality for ne Sort Prop
  with ne_nf_ind := Minimality for nf Sort Prop.

  Section nf_ne_ind.
    Context (P P0 : context -> term -> Prop).
    Context (hrel : (forall (Γ : context) (i : nat),
    option_map decl_body (nth_error Γ i) = Some None -> P Γ (tRel i)))
    (hvar : (forall (Γ : context) (v : ident), P Γ (tVar v)))
    (hevar : (forall (Γ : context) (n : nat) (l : list term),
    All (fun x => ne Γ x × P Γ x) l -> P Γ (tEvar n l)))
    (happ : (forall (Γ : context) (f2 a : term),
    ne Γ f2 -> P Γ f2 -> nf Γ a -> P0 Γ a -> P Γ (tApp f2 a)))
    (hcst : (forall (Γ : context) (c : kername) (u : Instance.t) (decl : constant_body),
    lookup_env Σ c = Some (ConstantDecl decl) ->
    cst_body decl = None -> P Γ (tConst c u)))
    (hfix :
    (forall (Γ : context) (mfix : list (def term)) (idx : nat)
      (args : list term) (d : def term) (arg : term),
    nth_error mfix idx = Some d ->
    nth_error args (rarg d) = Some arg ->
    All (fun x => nf Γ x /\ P0 Γ x) args -> ne Γ arg -> P Γ arg ->
    All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ P0 (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype) /\ P0 Γ d.(dtype)) mfix ->

    P Γ (mkApps (tFix mfix idx) args)))

    (hcase : (forall (Γ : context) (i : case_info) (p : predicate term)
      (c : term) (brs : list (branch term)),
    ne Γ c ->
    P Γ c ->
    All
      (fun br : branch term =>
      nf (Γ,,, inst_case_branch_context p br) (bbody br) /\ P0 (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ->
    All (nf Γ) (pparams p) ->
    onctx_rel nf Γ (inst_case_predicate_context p) ->
    nf (Γ,,, inst_case_context (pparams p) (puinst p) (pcontext p)) (preturn p) ->
    All (P0 Γ) (pparams p) ->
    onctx_rel P0 Γ (inst_case_predicate_context p) ->
    P0 (Γ,,, inst_case_context (pparams p) (puinst p) (pcontext p)) (preturn p) ->
    P Γ (tCase i p c brs)))

    (hproj : (forall (Γ : context) (p : projection) (c : term),
    ne Γ c -> P Γ c -> P Γ (tProj p c)))
    (hne : (forall (Γ : context) (t : term), ne Γ t -> P Γ t -> P0 Γ t))
    (hlam : (forall (Γ : context) (na : aname) (A b : term),
    nf Γ A ->
    P0 Γ A ->
    nf (Γ,, vass na A) b -> P0 (Γ,, vass na A) b -> P0 Γ (tLambda na A b)))
    (hconstruct : (forall (Γ : context) (ind : inductive) (k : nat) (u : Instance.t),
    P0 Γ (tConstruct ind k u)))

    (hcofix : (forall (Γ : context) mfix idx args,

    All (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ P0 (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype) /\ P0 Γ d.(dtype)) mfix ->
    All (fun t => nf Γ t /\ P0 Γ t) args ->
    P0 Γ (mkApps (tCoFix mfix idx) args)))

    (hind : (forall (Γ : context) (ind : inductive) (u : Instance.t), P0 Γ (tInd ind u)))

    (hprod : forall Γ na dom codom,
      nf Γ dom -> P0 Γ dom ->
      nf (Γ ,, vass na dom) codom ->
      P0 (Γ ,, vass na dom) codom ->
      P0 Γ (tProd na dom codom)).

    Lemma ne_ind_all : forall (Γ : context) (t : term), ne Γ t -> P Γ t
    with nf_ind_all : forall (Γ : context) (t : term), nf Γ t -> P0 Γ t.
    Proof.
      destruct 1; [eapply hrel|eapply hvar|eapply hevar|eapply happ|eapply hcst|eapply hfix|eapply hcase|eapply hproj]; eauto.
      * induction X; constructor; eauto.
      * clear -X nf_ind_all. induction X; constructor; eauto.
      * clear -X0 nf_ind_all; revert X0; generalize (fix_context mfix); induction 1; constructor; intuition eauto.
      * clear -X nf_ind_all; revert X; induction 1; constructor; intuition eauto.
      * clear -X0 nf_ind_all. revert X0; induction 1; constructor; intuition eauto.
      * clear -X1 nf_ind_all; revert X1; induction 1; constructor; unfold on_local_decl, lift_wf_term in *; cbn in *; intuition eauto.
      * destruct 1; [eapply hne|eapply hlam|eapply hconstruct|eapply hcofix|eapply hind|eapply hprod]; eauto.
        clear -X nf_ind_all. revert X; generalize (fix_context mfix); induction 1; constructor; intuition eauto.
        clear -X0 nf_ind_all. induction X0; constructor; eauto.
    Qed.

    Lemma ne_nf_ind_all : forall Γ t, (ne Γ t -> P Γ t) /\ (nf Γ t -> P0 Γ t).
    Proof.
      split; apply ne_ind_all || apply nf_ind_all.
    Qed.

  End nf_ne_ind.

  Lemma ne_mkApps_inv Γ f args :
    ~~ isApp f ->
    ne Γ (mkApps f args) ->
    (~~ isFix f /\ ne Γ f /\ Forall (nf Γ) args) \/
    (exists c u decl, f = tConst c u /\ lookup_env Σ c = Some (ConstantDecl decl) /\
      decl.(cst_body) = None) \/
    (exists mfix idx d arg, f = tFix mfix idx /\
      nth_error mfix idx = Some d /\
      nth_error args (rarg d) = Some arg /\
      Forall (nf Γ) args /\
      Forall (fun d => nf (Γ ,,, fix_context mfix) d.(dbody) /\ nf Γ d.(dtype)) mfix /\
      ne Γ arg).
  Proof.
    revert f. induction args using rev_ind; cbn.
    - intros f napp. intros ne; depelim ne; try solve [left; split; [|split]; constructor; eauto; constructor].
      right. left. do 2 eexists; eauto.
      right; right. do 4 eexists. eapply nisApp_mkApps in napp as [? ->]. intuition eauto.

      - intros. specialize (IHargs f H).
        rewrite mkApps_app /= in H0.
        depelim H0. specialize (IHargs H0). intuition eauto.
        * left. intuition auto. eapply app_Forall; eauto.
        * right; right. destruct H3 as [mfix [idx [d [arg []]]]]. exists mfix, idx, d, arg. intuition eauto. erewrite nth_error_app_left; tea. reflexivity.
          eapply app_Forall; eauto.
        * destruct args0 using rev_case. cbn in x. noconf x. rewrite mkApps_app in x; noconf x.
          eapply mkApps_eq_inj in H3 => //. destruct H3; subst.
          right; right. exists mfix, idx, d, arg. intuition auto.
  Qed.

  Lemma OnOne2_nth_error {A} (l l' : list A) P :
    OnOne2 P l l' ->
    ∑ n t t', [× nth_error l n = Some t, nth_error l' n = Some t' & P t t'].
  Proof.
    induction 1 in |- *.
    - exists 0, hd, hd'; intuition auto.
    - destruct IHX as [n [t [t' []]]]. exists (S n), t, t'; intuition auto.
  Qed.

  Lemma ne_tConstruct_app Γ c k u args : ne Γ (mkApps (tConstruct c k u) args) -> False.
  Proof.
    induction args using rev_ind; cbn; intros hne; depelim hne; solve_discr.
    rewrite mkApps_app /= in x; noconf x; eauto.
  Qed.

  Lemma ne_tCoFix_app Γ mfix idx args : ne Γ (mkApps (tCoFix mfix idx) args) -> False.
  Proof.
    induction args using rev_ind; cbn; intros hne; depelim hne; solve_discr.
    rewrite mkApps_app /= in x; noconf x; eauto.
  Qed.

  Lemma isConstruct_app_ne Γ t : isConstruct_app t -> ne Γ t -> False.
  Proof.
    rewrite /isConstruct_app.
    destruct decompose_app eqn:ht. cbn.
    destruct t0 => //. eapply decompose_app_inv in ht; subst.
    intros _ hne. now apply ne_tConstruct_app in hne.
  Qed.

  Lemma ne_nisConstruct_app Γ t : ne Γ t -> ~~ isConstruct_app t.
  Proof.
    rewrite /isConstruct_app.
    destruct decompose_app eqn:ht. cbn.
    destruct t0 => //. eapply decompose_app_inv in ht; subst.
    intros hne. now apply ne_tConstruct_app in hne.
  Qed.

  (** No literal is in [ne] or [nf]: neither has a [tPrim] case. *)
  Lemma ne_tPrim Γ p : ne Γ (tPrim p) -> False.
  Proof. intros h; depelim h; solve_discr. Qed.

  Lemma nf_tPrim Γ p : nf Γ (tPrim p) -> False.
  Proof. intros h; depelim h; try solve_discr; eapply ne_tPrim; eassumption. Qed.

  (** The outermost argument of a [red_prim_op] redex with arguments is a
      literal, which [ne_app]'s premise [nf Γ a] excludes.  The rule is exact
      saturation, so an over-applied redex is reached through [app_red_l] and
      handled by the induction on the head.  The zero-argument case is
      [prim_op_denote_nil].  So [nf_no_red] needs no guard on [ne_const]. *)
  Lemma nf_red_prim_op_last Γ f a c u ls :
    mkApps (tConst c u) (map term_of_lit ls) = tApp f a -> nf Γ a -> False.
  Proof.
    intros e ha.
    destruct ls as [|l ls _] using MRList.rev_ind; [discriminate e|].
    rewrite map_app mkApps_app in e; cbn in e. noconf e.
    rewrite /term_of_lit in ha. now eapply nf_tPrim.
  Qed.

  (** Pin: a registered bodiless operation is neutral as a bare constant.
      Erasure's [nisErasable] relies on [nf] covering it (design change log
      17(b)); re-adding a [prim_op_of Σ c = None] guard to [ne_const] makes this
      lemma fail to build. *)
  Lemma ne_tConst_registered Γ c u decl op :
    lookup_env Σ c = Some (ConstantDecl decl) ->
    decl.(cst_body) = None ->
    prim_op_of Σ c = Some op ->
    ne Γ (tConst c u).
  Proof. intros hl hb _. now eapply ne_const. Qed.

  Lemma nf_no_red {cf : checker_flags} Γ t : wf Σ ->
    (ne Γ t -> (forall u, red1 Σ Γ t u -> False)) /\
    (nf Γ t -> (forall u, red1 Σ Γ t u -> False)).
  Proof.
    intros wfΣ.
    refine (ne_nf_ind_all (fun Γ t => forall u, red1 Σ Γ t u -> False) (fun Γ t => forall u, red1 Σ Γ t u -> False) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros; try solve [depelim X; solve_discr; eauto].
    - depelim X; try congruence; try solve_discr.
    - depelim X0; try solve_discr.
      all: induction o; [depelim X; intuition eauto|apply IHo; now depelim X].
    - depelim X; solve_discr.
      all: try solve [exfalso; eapply nf_red_prim_op_last; eassumption].
      depelim H; solve_discr.
      destruct args using rev_case; solve_discr. noconf x.
      rewrite mkApps_app in x; noconf x.
      eapply ne_mkApps_inv in H as [H|[H|H]]; intuition eauto.
      now destruct H as [? [? []]].
      destruct H as [mfix' [idx' [d [arg []]]]]. noconf H. intuition eauto.
      rewrite /unfold_fix in e. rewrite H in e. noconf e. rewrite /is_constructor in e0. erewrite nth_error_app_left in e0; tea.
      now eapply isConstruct_app_ne in e0.
      eauto. eauto.
    - depelim X; solve_discr.
      all: try solve [match goal with
        | [ hd : prim_op_denote _ ?l = Some _ |- _ ] =>
            destruct l; [now rewrite prim_op_denote_nil in hd|cbn in *; solve_discr]
        end].
      unshelve eapply declared_constant_to_gen in isdecl; tea. rewrite /declared_constant_gen H in isdecl.
      noconf isdecl. congruence.
      all: destruct ls; [now rewrite prim_op_denote_nil in e1|discriminate H2].
    - eapply red1_mkApps_tFix_inv in X1 as [[Hr|Hr]|Hr].
      * destruct Hr as [v' [-> a]]. eapply OnOne2_nth_error in a as [n [? [? []]]].
        eapply nth_error_all in X; tea. cbn in X. intuition eauto.
      * destruct Hr as [mfix' []]. subst u.
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
      * destruct Hr as [mfix' []]. subst.
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
      * rewrite /unfold_fix H /is_constructor H0. eapply ne_nisConstruct_app in H1.
        now move/negPf: H1.
    - depelim X4; solve_discr.
      * eapply isConstruct_app_ne in H => //.
        rewrite /isConstruct_app decompose_app_mkApps //.
      * now eapply ne_tCoFix_app in H.
      * eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
      * eauto.
      * eauto.
      * eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]].
        intuition eauto.
    - depelim X; solve_discr; eauto.
      * now eapply ne_tCoFix_app in H.
      * eapply isConstruct_app_ne in H => //.
        rewrite /isConstruct_app decompose_app_mkApps //.
    - eauto.
    - eapply red1_mkApps_tCoFix_inv in X1 as [[]|].
      * destruct s as [v' [-> ?]].
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]]. intuition eauto.
      * destruct s as [mfix' [-> o]].
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]]. intuition eauto.
      * destruct s as [mfix' [-> o]].
        eapply OnOne2_All_mix_left in o; tea.
        eapply OnOne2_nth_error in o as [n [? [? []]]]. intuition eauto.
  Qed.

  Lemma nf_red {cf : checker_flags} Γ t : wf Σ ->
    (ne Γ t -> (forall u, red Σ Γ t u -> u = t))
   /\ (nf Γ t -> (forall u, red Σ Γ t u -> u = t)).
  Proof.
    intros wfΣ. split.
    - intros ne u hu.
      induction hu. eapply (proj1 (nf_no_red _ _ _)) in r; eauto. reflexivity.
      specialize (IHhu1 ne). subst.
      specialize (IHhu2 ne). subst. reflexivity.
    - intros ne u hu.
      induction hu.
      eapply (proj2 (nf_no_red _ _ _)) in r; eauto. reflexivity.
      specialize (IHhu1 ne). subst.
      specialize (IHhu2 ne). subst. reflexivity.
  Qed.

End Normal.
