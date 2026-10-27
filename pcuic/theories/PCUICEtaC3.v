(* Distributed under the terms of the MIT license. *)

(** * C3 — Hindley strong commutation of β-reduction with one η step, mod domains

  (BET-315 eta lane, plan §3 row C3; prover C3Prover1.)

  Target (plan line 546):
    red1 Σ Γ t v -> eta1 t u ->
      ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.

  Route: a dedicated [red1_ind_all] induction with this stronger conclusion
  (C2's statement is too weak). The FOUR UNLOCKING CASES come first —
  [red_proj], [red_fix], [red_cofix_case], [red_cofix_proj]. Per the lane lead's
  falsifier-verified structural fact: eta_red is the only redex-creating
  constructor, and its exposed body [tApp (lift0 1 s) (tRel 0)] has a tApp head,
  on which only red_beta/red_fix fire; so an η-unlocked redex sits strictly below
  a proj_red/case_red node. Hence [red_proj]/[red_cofix_case]/[red_cofix_proj]
  are independent-position (congruence) cases and [red_fix] is the ONE genuine
  one-step-each collision.

  Everything below is "proved, CONDITIONAL on the closure facts CH1, CH2"
  ([upto_domain_refl], [eta_subst] — L2-owned U-rows, Context parameters here,
  invisible to [Print Assumptions]). All other helpers are proved from the
  shared [PCUICEtaDefs] definitions. Shared [eta1]/[upto_domain] are NOT retyped. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICCases PCUICReduction PCUICEtaDefs.
From MetaRocq.PCUIC Require Import PCUICInduction.

Import ListNotations.

Set Default Goal Selector "!".

Local Ltac invs H := inversion H; subst; clear H.

(** ** Inversion of one η step on an application spine (9.2 port of the 2020
    [eta1_mkApps_inv]). *)
Lemma eta1_mkApps_inv M l N :
  eta1 (mkApps M l) N ->
  (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l in M, N |- *; cbn.
  - left; now exists N.
  - intro H; apply IHl in H as [[M' [e ?]]|[l' [o ?]]]; subst.
    + invs e.
      * left; now exists N1.
      * right; exists (N2 :: l). split; now constructor.
    + right; exists (a :: l'). split; now constructor.
Defined.

(** A rigid constructor head admits no η step. *)
Lemma eta1_tConstruct_inv ind k u N : eta1 (tConstruct ind k u) N -> False.
Proof. intro H; invs H. Qed.

(** One η step on a [tFix]: it rewrites a dtype or a dbody of one definition. *)
Lemma eta1_tFix_inv mfix idx N :
  eta1 (tFix mfix idx) N ->
  ∑ mfix1, (N = tFix mfix1 idx) ×
    (OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix1
     + OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix mfix1).
Proof.
  intro H; invs H.
  - eexists; split; [reflexivity | left; eassumption].
  - eexists; split; [reflexivity | right; eassumption].
Qed.

(** One η step on a [tCoFix]: it rewrites a dtype or a dbody of one definition. *)
Lemma eta1_tCoFix_inv mfix idx N :
  eta1 (tCoFix mfix idx) N ->
  ∑ mfix1, (N = tCoFix mfix1 idx) ×
    (OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix1
     + OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix mfix1).
Proof.
  intro H; invs H.
  - eexists; split; [reflexivity | left; eassumption].
  - eexists; split; [reflexivity | right; eassumption].
Qed.

(** ** η congruences on an application spine. *)
Lemma eta1_mkApps_f M M' l : eta1 M M' -> eta1 (mkApps M l) (mkApps M' l).
Proof.
  induction l in M, M' |- *; cbn; auto. intro H. apply IHl. now constructor.
Qed.

Lemma eta_mkApps_f M M' l : eta M M' -> eta (mkApps M l) (mkApps M' l).
Proof.
  induction 1.
  - apply rt_step. now apply eta1_mkApps_f.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma eta1_mkApps_args M l l' : OnOne2 eta1 l l' -> eta1 (mkApps M l) (mkApps M l').
Proof.
  induction 1 in M |- *; cbn.
  - apply eta1_mkApps_f. now apply app_eta_r.
  - apply IHX.
Qed.

Lemma eta_case_discr ip p c c' brs :
  eta c c' -> eta (tCase ip p c brs) (tCase ip p c' brs).
Proof.
  induction 1.
  - apply rt_step. now apply case_eta_discr.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma eta_proj_c pr c c' : eta c c' -> eta (tProj pr c) (tProj pr c').
Proof.
  induction 1.
  - apply rt_step. now apply proj_eta.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** ** A one-η step preserves a constructor head. *)
Lemma isConstruct_app_App M N : isConstruct_app (tApp M N) = isConstruct_app M.
Proof. rewrite /isConstruct_app /decompose_app /= fst_decompose_app_rec //. Qed.

Lemma eta1_isConstruct_app a a' :
  eta1 a a' -> isConstruct_app a = true -> isConstruct_app a' = true.
Proof.
  intros He Hc. unfold isConstruct_app in Hc.
  destruct (decompose_app a) as [f l] eqn:Hda.
  destruct f; try discriminate Hc.
  apply decompose_app_inv in Hda; subst a.
  apply eta1_mkApps_inv in He as [[M' [e ?]]|[l' [o ?]]]; subst.
  - now apply eta1_tConstruct_inv in e.
  - rewrite /isConstruct_app decompose_app_mkApps //.
Qed.

Lemma is_constructor_OnOne2 n args args' :
  OnOne2 eta1 args args' -> is_constructor n args = true -> is_constructor n args' = true.
Proof.
  intros o H. unfold is_constructor in *.
  destruct (nth_error args n) as [a|] eqn:e; [|discriminate H].
  eapply OnOne2_nth_error in o as [a' [e' [<-|he]]]; tea; rewrite e'; auto.
  now eapply eta1_isConstruct_app in he.
Qed.

(** η on the fix/cofix substitution vectors, from the fix/cofix congruences
    (C3Prover3's CH4; derived, not assumed). *)
Lemma eta_fix_subst mfix mfix' :
  #|mfix| = #|mfix'| ->
  (forall i, eta (tFix mfix i) (tFix mfix' i)) ->
  All2 eta (fix_subst mfix) (fix_subst mfix').
Proof.
  intros Hlen Hi. unfold fix_subst. rewrite Hlen.
  generalize (#|mfix'|). induction n; cbn; constructor; auto.
Qed.

Lemma eta_cofix_subst mfix mfix' :
  #|mfix| = #|mfix'| ->
  (forall i, eta (tCoFix mfix i) (tCoFix mfix' i)) ->
  All2 eta (cofix_subst mfix) (cofix_subst mfix').
Proof.
  intros Hlen Hi. unfold cofix_subst. rewrite Hlen.
  generalize (#|mfix'|). induction n; cbn; constructor; auto.
Qed.

Section C3Cases.
  (* ASSUMED CLOSURE FACTS (lemma parameters — invisible to Print Assumptions).
     Everything in this Section is "proved, conditional on CH1, CH2".
     Names and types are EtaL2's authoritative ones (frac/eta-l2), so the final
     assembly Requires PCUICEtaConfluence's versions with no rename. *)

  (* CH1 (U1): upto_domain reflexive. LANDED green on frac/eta-l2 @ e49648c4. *)
  Context (upto_domain_refl : forall t, upto_domain t t).

  (* CH2 (U2+U4): eta commutes with parallel substitution. In progress on
     frac/eta-l2 (PCUICEtaConfluence.v); exact type agreed with EtaL2. *)
  Context (eta_subst : forall (s s' : list term) (b b' : term),
      All2 eta s s' -> eta b b' -> eta (subst0 s b) (subst0 s' b')).

  Context {Σ : global_env} {Γ : context}.

  (** ** Unlocking case 1: [red_proj] (independent position)

    [t = tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)], [red_proj] fires
    to [arg]. An η step from [t] stays inside the spine (rigid constructor head),
    so [red_proj] re-fires and the projected argument moves by ≤1 η step. Uses CH1. *)
  Lemma C3_red_proj p args u arg :
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    forall w,
      eta1 (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) w ->
      ∑ a b, clos_refl (red1 Σ Γ) w a
           × clos_refl_trans eta1 arg b
           × upto_domain a b.
  Proof.
    intros hnth w He.
    invs He.
    match goal with
    | H : eta1 (mkApps _ _) _ |- _ =>
        apply eta1_mkApps_inv in H as [[M0 [e ?]]|[args' [o ?]]]
    end; subst.
    - now apply eta1_tConstruct_inv in e.
    - eapply OnOne2_nth_error in o as [arg' [hnth' [heq | hstep]]]; tea.
      + subst arg'.
        exists arg, arg. split; [|split].
        * apply r_step. eapply red_proj; exact hnth'.
        * apply rt_refl.
        * apply upto_domain_refl.
      + exists arg', arg'. split; [|split].
        * apply r_step. eapply red_proj; exact hnth'.
        * apply rt_step. exact hstep.
        * apply upto_domain_refl.
  Qed.

  (** ** Unlocking case 2: [red_fix] (the one genuine collision)

    [t = mkApps (tFix mfix idx) args], [red_fix] fires to [mkApps fn args] with
    [unfold_fix mfix idx = Some (narg, fn)] and [is_constructor narg args]. An η
    step either sits in the spine (congruence; [red_fix] re-fires, join is
    [mkApps fn args'] up to one η step) or rewrites the fix body/type (both legs
    meet at [mkApps fn' args] where [fn'] is the η-reduct of [fn], via CH2). *)
  Lemma C3_red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    forall w,
      eta1 (mkApps (tFix mfix idx) args) w ->
      ∑ a b, clos_refl (red1 Σ Γ) w a
           × clos_refl_trans eta1 (mkApps fn args) b
           × upto_domain a b.
  Proof.
    intros Hunf Hic w He.
    apply eta1_mkApps_inv in He as [[M' [e ?]]|[args' [o ?]]]; subst.
    - (* η in the fix head *)
      unfold unfold_fix in Hunf.
      destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate Hunf].
      invs Hunf.
      apply eta1_tFix_inv in e as [mfix1 [-> Hor]].
      (* common join: both legs reach [mkApps fn' args], fn' the η-reduct of fn *)
      assert (Hjoin :
        #|mfix| = #|mfix1| ->
        (forall i, eta (tFix mfix i) (tFix mfix1 i)) ->
        (∑ d1, nth_error mfix1 idx = Some d1
               × rarg d1 = rarg d × eta (dbody d) (dbody d1)) ->
        ∑ a b,
          clos_refl (red1 Σ Γ) (mkApps (tFix mfix1 idx) args) a
          × clos_refl_trans eta1
              (mkApps (subst0 (fix_subst mfix) (dbody d)) args) b
          × upto_domain a b).
      { intros Hlen Hfix (d1 & Hd1 & Hrarg & Hbody).
        exists (mkApps (subst0 (fix_subst mfix1) (dbody d1)) args),
               (mkApps (subst0 (fix_subst mfix1) (dbody d1)) args).
        split; [|split].
        - apply r_step. eapply red_fix.
          + unfold unfold_fix. rewrite Hd1. reflexivity.
          + rewrite Hrarg. exact Hic.
        - apply eta_mkApps_f. apply eta_subst; [|exact Hbody].
          apply eta_fix_subst; [exact Hlen | exact Hfix].
        - apply upto_domain_refl. }
      destruct Hor as [Hty | Hbody].
      + apply Hjoin.
        * now apply OnOne2_length in Hty.
        * intro i. apply rt_step. now apply fix_eta_ty.
        * pose proof Hty as Hn. eapply OnOne2_nth_error in Hn as [d1 [Hd1 Hr]]; [|exact Hd].
          exists d1. split; [exact Hd1|]. destruct Hr as [<-|[_ Heq]].
          -- split; [reflexivity | apply rt_refl].
          -- assert (Hdb : dbody d = dbody d1) by congruence.
             assert (Hrg : rarg d = rarg d1) by congruence.
             split; [now symmetry | rewrite Hdb; apply rt_refl].
      + apply Hjoin.
        * now apply OnOne2_length in Hbody.
        * intro i. apply rt_step. now apply fix_eta_body.
        * pose proof Hbody as Hn. eapply OnOne2_nth_error in Hn as [d1 [Hd1 Hr]]; [|exact Hd].
          exists d1. split; [exact Hd1|]. destruct Hr as [<-|[Hb Heq]].
          -- split; [reflexivity | apply rt_refl].
          -- assert (Hrg : rarg d = rarg d1) by congruence.
             split; [now symmetry | apply rt_step; exact Hb].
    - (* η in the spine: red_fix re-fires *)
      exists (mkApps fn args'), (mkApps fn args'). split; [|split].
      + apply r_step. eapply red_fix; [exact Hunf | ].
        eapply is_constructor_OnOne2; eassumption.
      + apply rt_step. now apply eta1_mkApps_args.
      + apply upto_domain_refl.
  Qed.

  (** ** Unlocking case 3: [red_cofix_case] (independent position / benign head)

    [t = tCase ip p (mkApps (tCoFix mfix idx) args) brs], [red_cofix_case] fires
    to [tCase ip p (mkApps fn args) brs]. An η step in the predicate, branches or
    spine is an independent-position case ([red_cofix_case] re-fires, v does the
    same η step); an η step in the cofix body/type joins both legs at
    [tCase ip p (mkApps fn' args) brs] via CH2 (no [is_constructor] guard). *)
  Lemma C3_red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    forall w,
      eta1 (tCase ip p (mkApps (tCoFix mfix idx) args) brs) w ->
      ∑ a b, clos_refl (red1 Σ Γ) w a
           × clos_refl_trans eta1 (tCase ip p (mkApps fn args) brs) b
           × upto_domain a b.
  Proof.
    intros Hunf w He. invs He.
    - (* case_eta_param: independent *)
      match goal with o : OnOne2 eta1 _ ?params' |- _ =>
        exists (tCase ip (set_pparams p params') (mkApps fn args) brs),
               (tCase ip (set_pparams p params') (mkApps fn args) brs);
        split; [|split];
        [ apply r_step; eapply red_cofix_case; exact Hunf
        | apply rt_step; eapply case_eta_param; exact o
        | apply upto_domain_refl ] end.
    - (* case_eta_return: independent *)
      match goal with e : eta1 _ ?pret' |- _ =>
        exists (tCase ip (set_preturn p pret') (mkApps fn args) brs),
               (tCase ip (set_preturn p pret') (mkApps fn args) brs);
        split; [|split];
        [ apply r_step; eapply red_cofix_case; exact Hunf
        | apply rt_step; eapply case_eta_return; exact e
        | apply upto_domain_refl ] end.
    - (* case_eta_discr: η in the discriminee *)
      match goal with e : eta1 (mkApps _ _) _ |- _ =>
        apply eta1_mkApps_inv in e as [[M' [e2 ?]]|[args' [o ?]]] end; subst.
      + (* η in the cofix head *)
        unfold unfold_cofix in Hunf.
        destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate Hunf].
        invs Hunf.
        apply eta1_tCoFix_inv in e2 as [mfix1 [-> Hor]].
        assert (Hjoin :
          #|mfix| = #|mfix1| ->
          (forall i, eta (tCoFix mfix i) (tCoFix mfix1 i)) ->
          (∑ d1, nth_error mfix1 idx = Some d1 × eta (dbody d) (dbody d1)) ->
          ∑ a b,
            clos_refl (red1 Σ Γ)
              (tCase ip p (mkApps (tCoFix mfix1 idx) args) brs) a
            × clos_refl_trans eta1
                (tCase ip p (mkApps (subst0 (cofix_subst mfix) (dbody d)) args) brs) b
            × upto_domain a b).
        { intros Hlen Hcofix (d1 & Hd1 & Hbody).
          exists (tCase ip p (mkApps (subst0 (cofix_subst mfix1) (dbody d1)) args) brs),
                 (tCase ip p (mkApps (subst0 (cofix_subst mfix1) (dbody d1)) args) brs).
          split; [|split].
          - apply r_step. eapply red_cofix_case.
            unfold unfold_cofix. rewrite Hd1. reflexivity.
          - apply eta_case_discr. apply eta_mkApps_f. apply eta_subst; [|exact Hbody].
            apply eta_cofix_subst; [exact Hlen | exact Hcofix].
          - apply upto_domain_refl. }
        destruct Hor as [Hty | Hbody].
        * apply Hjoin.
          -- now apply OnOne2_length in Hty.
          -- intro i. apply rt_step. now apply cofix_eta_ty.
          -- pose proof Hty as Hn. eapply OnOne2_nth_error in Hn as [d1 [Hd1 Hr]]; [|exact Hd].
             exists d1. split; [exact Hd1|]. destruct Hr as [<-|[_ Heq]].
             ++ apply rt_refl.
             ++ assert (Hdb : dbody d = dbody d1) by congruence.
                rewrite Hdb; apply rt_refl.
        * apply Hjoin.
          -- now apply OnOne2_length in Hbody.
          -- intro i. apply rt_step. now apply cofix_eta_body.
          -- pose proof Hbody as Hn. eapply OnOne2_nth_error in Hn as [d1 [Hd1 Hr]]; [|exact Hd].
             exists d1. split; [exact Hd1|]. destruct Hr as [<-|[Hb Heq]].
             ++ apply rt_refl.
             ++ apply rt_step; exact Hb.
      + (* η in the discriminee spine *)
        exists (tCase ip p (mkApps fn args') brs), (tCase ip p (mkApps fn args') brs).
        split; [|split].
        * apply r_step. eapply red_cofix_case; exact Hunf.
        * apply rt_step. apply case_eta_discr. now apply eta1_mkApps_args.
        * apply upto_domain_refl.
    - (* case_eta_brs: independent *)
      match goal with o : OnOne2 (on_Trel_eq eta1 bbody bcontext) _ ?brs' |- _ =>
        exists (tCase ip p (mkApps fn args) brs'),
               (tCase ip p (mkApps fn args) brs');
        split; [|split];
        [ apply r_step; eapply red_cofix_case; exact Hunf
        | apply rt_step; eapply case_eta_brs; exact o
        | apply upto_domain_refl ] end.
  Qed.

  (** ** Unlocking case 4: [red_cofix_proj] (independent position / benign head)

    [t = tProj pr (mkApps (tCoFix mfix idx) args)]; symmetric to case 3 with a
    [tProj] wrapper (η can only sit in the discriminee). *)
  Lemma C3_red_cofix_proj pr mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    forall w,
      eta1 (tProj pr (mkApps (tCoFix mfix idx) args)) w ->
      ∑ a b, clos_refl (red1 Σ Γ) w a
           × clos_refl_trans eta1 (tProj pr (mkApps fn args)) b
           × upto_domain a b.
  Proof.
    intros Hunf w He. invs He.
    match goal with e : eta1 (mkApps _ _) _ |- _ =>
      apply eta1_mkApps_inv in e as [[M' [e2 ?]]|[args' [o ?]]] end; subst.
    - (* η in the cofix head *)
      unfold unfold_cofix in Hunf.
      destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate Hunf].
      invs Hunf.
      apply eta1_tCoFix_inv in e2 as [mfix1 [-> Hor]].
      assert (Hjoin :
        #|mfix| = #|mfix1| ->
        (forall i, eta (tCoFix mfix i) (tCoFix mfix1 i)) ->
        (∑ d1, nth_error mfix1 idx = Some d1 × eta (dbody d) (dbody d1)) ->
        ∑ a b,
          clos_refl (red1 Σ Γ) (tProj pr (mkApps (tCoFix mfix1 idx) args)) a
          × clos_refl_trans eta1
              (tProj pr (mkApps (subst0 (cofix_subst mfix) (dbody d)) args)) b
          × upto_domain a b).
      { intros Hlen Hcofix (d1 & Hd1 & Hbody).
        exists (tProj pr (mkApps (subst0 (cofix_subst mfix1) (dbody d1)) args)),
               (tProj pr (mkApps (subst0 (cofix_subst mfix1) (dbody d1)) args)).
        split; [|split].
        - apply r_step. eapply red_cofix_proj.
          unfold unfold_cofix. rewrite Hd1. reflexivity.
        - apply eta_proj_c. apply eta_mkApps_f. apply eta_subst; [|exact Hbody].
          apply eta_cofix_subst; [exact Hlen | exact Hcofix].
        - apply upto_domain_refl. }
      destruct Hor as [Hty | Hbody].
      + apply Hjoin.
        * now apply OnOne2_length in Hty.
        * intro i. apply rt_step. now apply cofix_eta_ty.
        * pose proof Hty as Hn. eapply OnOne2_nth_error in Hn as [d1 [Hd1 Hr]]; [|exact Hd].
          exists d1. split; [exact Hd1|]. destruct Hr as [<-|[_ Heq]].
          -- apply rt_refl.
          -- assert (Hdb : dbody d = dbody d1) by congruence.
             rewrite Hdb; apply rt_refl.
      + apply Hjoin.
        * now apply OnOne2_length in Hbody.
        * intro i. apply rt_step. now apply cofix_eta_body.
        * pose proof Hbody as Hn. eapply OnOne2_nth_error in Hn as [d1 [Hd1 Hr]]; [|exact Hd].
          exists d1. split; [exact Hd1|]. destruct Hr as [<-|[Hb Heq]].
          -- apply rt_refl.
          -- apply rt_step; exact Hb.
    - (* η in the discriminee spine *)
      exists (tProj pr (mkApps fn args')), (tProj pr (mkApps fn args')).
      split; [|split].
      + apply r_step. eapply red_cofix_proj; exact Hunf.
      + apply rt_step. apply proj_eta. now apply eta1_mkApps_args.
      + apply upto_domain_refl.
  Qed.

End C3Cases.
