(* Distributed under the terms of the MIT license. *)

(** * C1c for [eta1]: an η step commutes with the F-inst comparison

    [eta1_finst_l] : eta1 a b -> on_free_vars P a -> a ≈F[pb,napp] a' ->
                     ∑ b', eta1 a' b' × b ≈F[pb,napp] b'

  Base has no η, so nothing here transports. Every congruence case is the obvious
  one; the induction hypothesis is taken at the subterm's own [(pb, napp)]
  position. A3 ([PCUICEtaI5Trans]) consumes it.

  **The root case, and why there is a scoping premise.** If
  [a = λx:A. (lift0 1 m) (tRel 0)] and [a ≈F a'], then [a' = λx:A'. X' (tRel 0)]
  with [lift0 1 m ≈F[Conv,1] X']. For [a'] to be an η-redex, [X'] must be
  [lift0 1 m'], that is, variable 0 must not be free in [X']. The comparison
  preserves free variables (base's [eq_term_upto_univ_napp_on_free_vars],
  transported at [Conv]), but every [on_free_vars] fact also demands closed case
  contexts, so the free-variable fact about [lift0 1 m] cannot be produced from
  nothing: it comes from [on_free_vars P a]. A3 only ever applies this to scoped
  terms, so the premise costs nothing there. Then [m' := unlift 1 0 X'],
  [X' = lift0 1 m'] (renaming extensionality on the free variables), and
  [m ≈F m'] by renaming both sides with [unlift] (base [eq_term_upto_univ_rename],
  transported), lifted from [(Conv,1)] to [(pb,napp)] by [finst_term_Conv_pb].

  **The hypotheses are satisfiable:** [on_free_vars P a] by any scoped [a]
  ([P := shiftnP #|Γ| xpred0]); the subrelations by [compare_universe φ] and
  [compare_sort φ]; the comparison by any related pair.

  Reaches base [PCUICConfluence] through the transport. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICLiftSubst PCUICSigmaCalculus PCUICOnFreeVars PCUICOnFreeVarsConv
     PCUICRenameConv PCUICConfluence PCUICEtaDefs PCUICEtaStrengthening
     PCUICEtaFInst PCUICEtaFInstTransport PCUICEtaFInstC1c.

(** ** One-element simulation through an [OnOne2] against an [All2] *)

Lemma OnOne2_All2_sim {A} (Q : A -> Type) (T E : A -> A -> Type) (S : A -> A -> Type) l l1 l' :
  All Q l ->
  OnOne2 (fun x y => S x y × (forall x', Q x -> E x x' -> ∑ y', T x' y' × E y y')) l l1 ->
  All2 E l l' ->
  ∑ l1', OnOne2 T l' l1' × All2 E l1 l1'.
Proof.
  intros hQ h. revert l' hQ.
  induction h as [hd hd' tl [_ IH]|hd tl tl' h IHh]; intros [|x' l'] hQ e;
    try solve [inversion e]; inversion e as [|? ? ? ? hE hA]; subst; inversion hQ as [|? ? hq hQ']; subst.
  - destruct (IH x' hq hE) as (y' & hT & hE').
    exists (y' :: l'). split; constructor; assumption.
  - destruct (IHh l' hQ' hA) as (l1' & hO & hA').
    exists (x' :: l1'). split; [now apply OnOne2_tl|now constructor].
Qed.

(** ** [lift0 1] versus free variables and renaming *)

Lemma on_free_vars_lift01 P t : on_free_vars P (lift0 1 t) = on_free_vars (P ∘ lift_renaming 1 0) t.
Proof. now rewrite lift_rename on_free_vars_rename. Qed.

Lemma shiftnP1_lift P : shiftnP 1 P ∘ lift_renaming 1 0 =1 P.
Proof. intros i. rewrite /shiftnP /lift_renaming /=. repeat nat_compare_specs; cbn; lia_f_equal. Qed.

Lemma strengthenP01_xpredT P i : strengthenP 0 1 P i -> strengthenP 0 1 xpredT i.
Proof. rewrite /strengthenP. repeat nat_compare_specs => //. Qed.

(** A term free of variable 0 is a lift. *)
Lemma unlift_lift_eq P X : on_free_vars (strengthenP 0 1 P) X -> lift0 1 (unlift 1 0 X) = X.
Proof.
  intros h. rewrite lift_rename /unlift (rename_compose _ _ _).
  transitivity (rename ren_id X); [|apply rename_ren_id].
  eapply rename_ext_cond; [|exact h].
  intros i hi. exact (lift_unlift_renaming 1 0 i (strengthenP01_xpredT _ _ hi)).
Qed.

Section EtaC1c.

  Context (r : finst_construct_rule) (Σ' : global_env)
          (cu : conv_pb -> Universe.t -> Universe.t -> Prop)
          (cs : conv_pb -> sort -> sort -> Prop).

  Local Notation RF pb n := (eq_term_upto_univ_eta_napp r Σ' cu cs pb n).

  (** Free variables are preserved, at [Conv] (transported). *)
  Lemma finst_on_free_vars {cf : checker_flags} P n t u :
    RF Conv n t u -> on_free_vars P t -> on_free_vars P u.
  Proof. intros e. apply finst_Conv_to_base in e. exact (eq_term_upto_univ_napp_on_free_vars e). Qed.

  (** Renaming is preserved, at [Conv] (transported). *)
  Lemma finst_rename n t u f : RF Conv n t u -> RF Conv n (rename f t) (rename f u).
  Proof.
    intros e. apply finst_Conv_of_base. apply eq_term_upto_univ_rename. now apply finst_Conv_to_base.
  Qed.

  (** The root of the η-C1c: a comparison partner of an η-redex is an η-redex. *)
  Lemma finst_eta_root {cf : checker_flags} P pb napp m X' :
    RelationClasses.subrelation (cu Conv) (cu pb) ->
    RelationClasses.subrelation (cs Conv) (cs pb) ->
    on_free_vars P m ->
    RF Conv 1 (lift0 1 m) X' ->
    ∑ m', (X' = lift0 1 m') × RF pb napp m m'.
  Proof.
    intros hsu hss hm e.
    have hX : on_free_vars (strengthenP 0 1 P) X'.
    { eapply finst_on_free_vars; [exact e|]. now rewrite on_free_vars_lift. }
    exists (unlift 1 0 X'). split; [symmetry; exact (unlift_lift_eq P X' hX)|].
    have e' := finst_rename _ _ _ (unlift_renaming 1 0) e.
    rewrite -/(unlift 1 0 (lift0 1 m)) lift_unlift_term in e'.
    exact (finst_term_Conv_pb r Σ' cu cs _ _ _ _ e' eq_refl pb napp hsu hss).
  Qed.

  (** The comparison hypothesis whose LEFT term is [t]: picked by TYPE, because
      [depelim]'s premise names are not stable. *)
  Local Ltac rfh t :=
    match goal with h : eq_term_upto_univ_eta_napp _ _ _ _ _ _ t _ |- _ => exact h end.

  (** The (co)fixpoint step and comparison relations, as notations so that
      [fix_eta_ty]/[fix_eta_body] unify with them syntactically. *)
  Local Notation fty_step := (fun d0 d1 : def term => eta1 (dtype d0) (dtype d1) ×
    ((dname d0, dbody d0, rarg d0) = (dname d1, dbody d1, rarg d1))).
  Local Notation fbody_step := (fun d0 d1 : def term => eta1 (dbody d0) (dbody d1) ×
    ((dname d0, dtype d0, rarg d0) = (dname d1, dtype d1, rarg d1))).
  Local Notation fdef_rel := (fun d d' : def term =>
    RF Conv 0 (dtype d) (dtype d') × RF Conv 0 (dbody d) (dbody d') ×
    (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')).

  (** **η-C1c, left.** *)
  Theorem eta1_finst_l {cf : checker_flags} a b :
    eta1 a b ->
    forall P pb napp a',
      RelationClasses.subrelation (cu Conv) (cu pb) ->
      RelationClasses.subrelation (cs Conv) (cs pb) ->
      on_free_vars P a -> RF pb napp a a' -> ∑ b', eta1 a' b' × RF pb napp b b'.
  Proof.
    revert a b.
    apply (eta1_ind_all (fun a b => forall P pb napp a',
      RelationClasses.subrelation (cu Conv) (cu pb) ->
      RelationClasses.subrelation (cs Conv) (cs pb) ->
      on_free_vars P a -> RF pb napp a a' -> ∑ b', eta1 a' b' × RF pb napp b b')).
    (* One bullet per eta1 case, in eta1_ind_all's order, no prelude. Scoping is
       unfolded with [cbn [on_free_vars]] only, so [shiftnP] and [lift] stay folded. *)
    - (* eta_red: the root *)
      intros na t A P pb napp a' hsu hss ha e.
      depelim e.
      match goal with hb : eq_term_upto_univ_eta_napp _ _ _ _ Conv 0 (tApp (lift0 1 t) (tRel 0)) _ |- _ =>
        depelim hb end.
      match goal with h0 : eq_term_upto_univ_eta_napp _ _ _ _ Conv 0 (tRel 0) _ |- _ =>
        depelim h0 end.
      cbn [on_free_vars] in ha. move/andP: ha => [_ hb]. move/andP: hb => [hl _].
      (* [shiftnP1_lift] is pointwise ([=1]); the predicate is unapplied, so use
         [on_free_vars_ext] rather than an ssreflect rewrite. *)
      rewrite on_free_vars_lift01 (on_free_vars_ext _ _ _ (shiftnP1_lift P)) in hl.
      match goal with h1 : eq_term_upto_univ_eta_napp _ _ _ _ Conv 1 (lift0 1 t) ?X' |- _ =>
        destruct (finst_eta_root P pb napp t X' hsu hss hl h1) as (m' & -> & em) end.
      exists m'. split; [apply eta_red|exact em].
    - (* abs_eta_l *)
      intros na M M' N _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/andP: ha => [hM _].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) hM ltac:(rfh M)) as (A1 & h1 & e1').
      eexists. split; [apply abs_eta_l; exact h1|constructor; assumption].
    - (* abs_eta_r *)
      (* abs_eta_r steps the BODY [M] of [tLambda na N M]. *)
      intros na M M' N _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/andP: ha => [_ hM].
      destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hM ltac:(rfh M)) as (B1 & h1 & e1').
      eexists. split; [apply abs_eta_r; exact h1|constructor; assumption].
    - (* letin_eta_def *)
      intros na b t b' r0 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and3P: ha => [hb _ _].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) hb ltac:(rfh b)) as (b1 & h1 & e1').
      eexists. split; [apply letin_eta_def; exact h1|constructor; assumption].
    - (* letin_eta_ty *)
      intros na b t b' r0 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and3P: ha => [_ ht _].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) ht ltac:(rfh t)) as (t1 & h1 & e1').
      eexists. split; [apply letin_eta_ty; exact h1|constructor; assumption].
    - (* letin_eta_body *)
      intros na b t b' r0 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and3P: ha => [_ _ hc].
      destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hc ltac:(rfh b')) as (c1 & h1 & e1').
      eexists. split; [apply letin_eta_body; exact h1|constructor; assumption].
    - (* case_eta_param *)
      intros ci p params' c brs X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and5P: ha => [hp _ _ _ _].
      match goal with h : eq_predicate _ _ p _ |- _ => destruct h as (epar & eu & ectx & eret) end.
      destruct (OnOne2_All2_sim (on_free_vars P) eta1 (RF Conv 0) eta1 _ _ _
                  (forallb_All _ _ hp)
                  (OnOne2_impl X (fun x y '(h, IH) => (h, fun x' hx ex =>
                     IH P Conv 0 x' (fun x y h => h) (fun x y h => h) hx ex))) epar)
        as (l1' & hO & hA).
      eexists. split.
      + eapply case_eta_param. exact hO.
      + constructor; [|assumption|assumption]. repeat split; cbn; assumption.
    - (* case_eta_return *)
      intros ci p preturn' c brs _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and5P: ha => [_ hr _ _ _].
      match goal with h : eq_predicate _ _ p _ |- _ => destruct h as (epar & eu & ectx & eret) end.
      destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hr eret) as (r1 & h1 & e1').
      eexists. split.
      + eapply case_eta_return. exact h1.
      + constructor; [|assumption|assumption]. repeat split; cbn; assumption.
    - (* case_eta_discr *)
      intros ci p c c' brs _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and5P: ha => [_ _ _ hd _].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) hd ltac:(rfh c)) as (d1 & h1 & e1').
      eexists. split; [apply case_eta_discr; exact h1|constructor; assumption].
    - (* case_eta_brs *)
      intros ci p c brs brs' X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/and5P: ha => [_ _ _ _ hbrs].
      have hb : All (fun br => on_free_vars (shiftnP #|bcontext br| P) (bbody br)) brs
        := All_impl (forallb_All _ _ hbrs) (fun br h => proj2 (andP h)).
      (* State the simulation result with its explicit type, then prove it by
         [eapply]: the callback becomes an ordinary goal whose type is known. *)
      match goal with hE : eq_branches _ brs ?brs2 |- _ =>
        assert (hsim : ∑ l1', OnOne2 (fun br br' => on_Trel_eq eta1 bbody bcontext br br') brs2 l1'
                              × All2 (eq_branch (RF Conv 0)) brs' l1');
        [ eapply (OnOne2_All2_sim (fun br => on_free_vars (shiftnP #|bcontext br| P) (bbody br))
                    (fun br br' => on_Trel_eq eta1 bbody bcontext br br')
                    (eq_branch (RF Conv 0))
                    (fun br br' => on_Trel_eq eta1 bbody bcontext br br'));
          [ exact hb
          | eapply OnOne2_impl; [exact X|];
            cbn; intros x y [[h IH] hc]; split; [split; assumption|];
            intros x' hx exx; hnf in exx; destruct exx as [ec eb];
            destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hx eb) as (b1 & hb1 & eb1);
            exists {| bcontext := bcontext x'; bbody := b1 |};
            (* the step keeps the context ([hc]); the comparison is [ec] *)
            split; [split; [exact hb1|reflexivity]|split; [cbn; rewrite -hc; exact ec|exact eb1]]
          | exact hE ]
        | ] end.
      destruct hsim as (l1' & hO & hA).
      eexists. split; [eapply case_eta_brs; exact hO|constructor; assumption].
    - (* proj_eta *)
      intros pr c c' _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha.
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) ha ltac:(rfh c)) as (c1 & h1 & e1').
      eexists. split; [apply proj_eta; exact h1|constructor; assumption].
    - (* app_eta_l: the function part, at (pb, S napp) *)
      intros M1 N1 M2 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/andP: ha => [h1 _].
      destruct (IH P pb _ _ hsu hss h1 ltac:(rfh M1)) as (f1 & hf & ef).
      eexists. split; [apply app_eta_l; exact hf|constructor; assumption].
    - (* app_eta_r *)
      intros M2 N2 M1 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/andP: ha => [_ h2].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) h2 ltac:(rfh M2)) as (x1 & hx & ex).
      eexists. split; [apply app_eta_r; exact hx|constructor; assumption].
    - (* prod_eta_l *)
      intros na M1 M2 N1 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/andP: ha => [hA _].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) hA ltac:(rfh M1)) as (A1 & hA1 & eA).
      eexists. split; [apply prod_eta_l; exact hA1|constructor; assumption].
    - (* prod_eta_r: the codomain, at (pb, 0) *)
      intros na M2 N2 M1 _ IH P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha. move/andP: ha => [_ hB].
      destruct (IH _ pb 0 _ hsu hss hB ltac:(rfh M2)) as (B1 & hB1 & eB).
      eexists. split; [apply prod_eta_r; exact hB1|constructor; assumption].
    - (* evar_eta *)
      intros ev l l' X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha.
      destruct (OnOne2_All2_sim (on_free_vars P) eta1 (RF Conv 0) eta1 _ _ _
                  (forallb_All _ _ ha)
                  (OnOne2_impl X (fun x y '(h, IH) => (h, fun x' hx ex =>
                     IH P Conv 0 x' (fun x y h => h) (fun x y h => h) hx ex)))
                  ltac:(match goal with h : All2 _ l _ |- _ => exact h end))
        as (l1' & hO & hA).
      eexists. split; [apply evar_eta; exact hO|constructor; exact hA].
    - (* fix_eta_ty *)
      intros mfix0 mfix1 idx X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha.
      match goal with hE : eq_mfixpoint _ mfix0 ?mf2 |- _ =>
        assert (hsim : ∑ l1', OnOne2 fty_step mf2 l1' × All2 fdef_rel mfix1 l1');
        [ eapply (OnOne2_All2_sim (fun d => on_free_vars P (dtype d)) fty_step fdef_rel fty_step);
          [ exact (All_impl (forallb_All _ _ ha) (fun d h => proj1 (andP h)))
          | eapply OnOne2_impl; [exact X|];
            cbn; intros x y [[h IH] he]; split; [split; assumption|];
            intros x' hx exx; hnf in exx; destruct exx as (ety & ebo & er & en);
            destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hx ety) as (t1 & ht1 & et1);
            injection he as hn hb hr;
            exists {| dname := dname x'; dtype := t1; dbody := dbody x'; rarg := rarg x' |};
            split; [split; [exact ht1|reflexivity]|];
            cbn; refine (et1, (_, (_, _)));
            [rewrite -hb; exact ebo|rewrite -hr; exact er|rewrite -hn; exact en]
          | exact hE ]
        | ] end.
      destruct hsim as (l1' & hO & hA).
      eexists. split; [apply fix_eta_ty; exact hO|constructor; exact hA].
    - (* fix_eta_body *)
      intros mfix0 mfix1 idx X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha.
      match goal with hE : eq_mfixpoint _ mfix0 ?mf2 |- _ =>
        assert (hsim : ∑ l1', OnOne2 fbody_step mf2 l1' × All2 fdef_rel mfix1 l1');
        [ eapply (OnOne2_All2_sim (fun d => on_free_vars (shiftnP #|mfix0| P) (dbody d))
                    fbody_step fdef_rel fbody_step);
          [ exact (All_impl (forallb_All _ _ ha) (fun d h => proj2 (andP h)))
          | eapply OnOne2_impl; [exact X|];
            cbn; intros x y [[h IH] he]; split; [split; assumption|];
            intros x' hx exx; hnf in exx; destruct exx as (ety & ebo & er & en);
            destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hx ebo) as (b1 & hb1 & eb1);
            injection he as hn ht hr;
            exists {| dname := dname x'; dtype := dtype x'; dbody := b1; rarg := rarg x' |};
            split; [split; [exact hb1|reflexivity]|];
            cbn; refine (_, (eb1, (_, _)));
            [rewrite -ht; exact ety|rewrite -hr; exact er|rewrite -hn; exact en]
          | exact hE ]
        | ] end.
      destruct hsim as (l1' & hO & hA).
      eexists. split; [apply fix_eta_body; exact hO|constructor; exact hA].
    - (* cofix_eta_ty *)
      intros mfix0 mfix1 idx X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha.
      match goal with hE : eq_mfixpoint _ mfix0 ?mf2 |- _ =>
        assert (hsim : ∑ l1', OnOne2 fty_step mf2 l1' × All2 fdef_rel mfix1 l1');
        [ eapply (OnOne2_All2_sim (fun d => on_free_vars P (dtype d)) fty_step fdef_rel fty_step);
          [ exact (All_impl (forallb_All _ _ ha) (fun d h => proj1 (andP h)))
          | eapply OnOne2_impl; [exact X|];
            cbn; intros x y [[h IH] he]; split; [split; assumption|];
            intros x' hx exx; hnf in exx; destruct exx as (ety & ebo & er & en);
            destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hx ety) as (t1 & ht1 & et1);
            injection he as hn hb hr;
            exists {| dname := dname x'; dtype := t1; dbody := dbody x'; rarg := rarg x' |};
            split; [split; [exact ht1|reflexivity]|];
            cbn; refine (et1, (_, (_, _)));
            [rewrite -hb; exact ebo|rewrite -hr; exact er|rewrite -hn; exact en]
          | exact hE ]
        | ] end.
      destruct hsim as (l1' & hO & hA).
      eexists. split; [apply cofix_eta_ty; exact hO|constructor; exact hA].
    - (* cofix_eta_body *)
      intros mfix0 mfix1 idx X P pb napp a' hsu hss ha e. depelim e.
      cbn [on_free_vars] in ha.
      match goal with hE : eq_mfixpoint _ mfix0 ?mf2 |- _ =>
        assert (hsim : ∑ l1', OnOne2 fbody_step mf2 l1' × All2 fdef_rel mfix1 l1');
        [ eapply (OnOne2_All2_sim (fun d => on_free_vars (shiftnP #|mfix0| P) (dbody d))
                    fbody_step fdef_rel fbody_step);
          [ exact (All_impl (forallb_All _ _ ha) (fun d h => proj2 (andP h)))
          | eapply OnOne2_impl; [exact X|];
            cbn; intros x y [[h IH] he]; split; [split; assumption|];
            intros x' hx exx; hnf in exx; destruct exx as (ety & ebo & er & en);
            destruct (IH _ Conv 0 _ (fun x y h => h) (fun x y h => h) hx ebo) as (b1 & hb1 & eb1);
            injection he as hn ht hr;
            exists {| dname := dname x'; dtype := dtype x'; dbody := b1; rarg := rarg x' |};
            split; [split; [exact hb1|reflexivity]|];
            cbn; refine (_, (eb1, (_, _)));
            [rewrite -ht; exact ety|rewrite -hr; exact er|rewrite -hn; exact en]
          | exact hE ]
        | ] end.
      destruct hsim as (l1' & hO & hA).
      eexists. split; [apply cofix_eta_body; exact hO|constructor; exact hA].
    - (* array_eta_val *)
      intros arr value X P pb napp a' hsu hss ha e. depelim e.
      match goal with o : onPrims _ _ _ _ |- _ => depelim o end.
      cbn [on_free_vars] in ha. simp test_prim in ha. cbn in ha. move/andP: ha => [/andP [hv _] _].
      destruct (OnOne2_All2_sim (on_free_vars P) eta1 (RF Conv 0) eta1 _ _ _
                  (forallb_All _ _ hv)
                  (OnOne2_impl X (fun x y '(h, IH) => (h, fun x' hx ex =>
                     IH P Conv 0 x' (fun x y h => h) (fun x y h => h) hx ex)))
                  ltac:(match goal with h : All2 _ (array_value arr) _ |- _ => exact h end))
        as (l1' & hO & hA).
      eexists. split.
      + eapply array_eta_val. exact hO.
      + constructor. constructor; cbn; assumption.
    - (* array_eta_def *)
      intros arr d _ IH P pb napp a' hsu hss ha e. depelim e.
      match goal with o : onPrims _ _ _ _ |- _ => depelim o end.
      cbn [on_free_vars] in ha. simp test_prim in ha. cbn in ha. move/andP: ha => [/andP [_ hd] _].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) hd ltac:(rfh (array_default arr)))
        as (d1 & hd1 & ed).
      eexists. split.
      + eapply array_eta_def. exact hd1.
      + constructor. constructor; cbn; assumption.
    - (* array_eta_type *)
      intros arr ty _ IH P pb napp a' hsu hss ha e. depelim e.
      match goal with o : onPrims _ _ _ _ |- _ => depelim o end.
      cbn [on_free_vars] in ha. simp test_prim in ha. cbn in ha. move/andP: ha => [_ hty].
      destruct (IH P Conv 0 _ (fun x y h => h) (fun x y h => h) hty ltac:(rfh (array_type arr)))
        as (t1 & ht1 & et).
      eexists. split.
      + eapply array_eta_type. exact ht1.
      + constructor. constructor; cbn; assumption.
  Qed.

End EtaC1c.
