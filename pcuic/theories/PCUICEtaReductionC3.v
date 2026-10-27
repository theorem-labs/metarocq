(* Distributed under the terms of the MIT license. *)

(* C3 (BET-315 eta lane): Hindley strong commutation of one beta-step with one
   eta-step, modulo upto_domain -- the FOUR UNLOCKING CASES (C3Prover3).
   Statement (against the shared PCUICEtaDefs):
     red1 Sigma Gamma t v -> eta1 t u ->
       exists w w', clos_refl (red1 Sigma Gamma) u w
                  * clos_refl_trans eta1 v w' * upto_domain w w'.
   Proves red_fix, red_cofix_case, red_cofix_proj, red_proj, each standalone, to be
   reused in the four fix/cofix/proj branches of the full red1_ind_all assembly.
   Route: C3 inducts on t's pre-existing beta-redex; the eta-step is orthogonal to
   it or inside its head definitions and never creates it, so postponement's
   counterexample does not transfer (lanes/eta/C3Prover3.md). Hence the beta-reduct
   side carries only eta* and the eta-reduct side one re-fire (clos_refl red1).
   The structural eta-closure lemmas CH1/CH5/CH6 are PROVED here from PCUICEtaDefs;
   the substitution-level U-rows CH2/CH3/CH4 are Section Context hypotheses (U1/U4,
   owned by L2/L7). No Admitted, no Axiom. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICCases
     PCUICInduction PCUICLiftSubst PCUICEquality PCUICReduction PCUICEtaDefs
     PCUICEtaConfluence.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.

Derive Signature for eta1.

Set Default Goal Selector "!".
Import ListNotations.

(* ======================================================================= *)
(** ** Structural η / mkApps / OnOne2 lemmas (context-free; no [Σ]).
    These discharge the U4 closure facts CH1, CH5a, CH5b, CH6 directly from
    [PCUICEtaDefs]'s [eta1] congruences. *)

Lemma eta_step {x y} : eta1 x y -> eta x y.
Proof. intro. now constructor. Qed.

Lemma eta_refl {x} : eta x x.
Proof. apply rt_refl. Qed.

Lemma eta_trans {x y z} : eta x y -> eta y z -> eta x z.
Proof. intros. eapply rt_trans; eauto. Qed.

(* One-hole η congruence: Required from EtaL2's PCUICEtaConfluence as [eta_cong1]
   — not re-derived here. *)

(** CH1 (U4): η under a spine moves the head or exactly one argument.
    PROVED here; = origin/eta_postpo:PCUICEtaReduction.v:1223-1234 (old AST). *)
Lemma eta1_mkApps_inv M l N : eta1 (mkApps M l) N ->
    (∑ M', eta1 M M' × N = mkApps M' l)
  + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l in M, N |- *; cbn.
  - intro H. left. exists N. split; [exact H|reflexivity].
  - intro H. apply IHl in H as [[M' [hM e]]|[l' [hl e]]].
    + subst N. depelim hM.
      * left. exists N1. split; [assumption|reflexivity].
      * right. exists (N2 :: l). split; [constructor; assumption|reflexivity].
    + subst N. right. exists (a :: l'). split; [constructor; assumption|reflexivity].
Defined.

(** η at the head lifts under a fixed spine (one step). *)
Lemma eta1_mkApps_f l : forall f f', eta1 f f' -> eta1 (mkApps f l) (mkApps f' l).
Proof.
  induction l; cbn; intros f f' H.
  - exact H.
  - apply IHl. now constructor.
Qed.

(** CH5a (U4): η* at the head lifts under a fixed spine. *)
Lemma eta_mkApps_head f f' l : eta f f' -> eta (mkApps f l) (mkApps f' l).
Proof.
  intro H. induction H.
  - apply eta_step. now apply eta1_mkApps_f.
  - apply eta_refl.
  - eapply eta_trans; eauto.
Qed.

(** One OnOne2 in the spine is one η step on [mkApps]. *)
Lemma eta1_mkApps_args l l' : OnOne2 eta1 l l' -> forall f, eta1 (mkApps f l) (mkApps f l').
Proof.
  induction 1 as [hd hd' tl p|hd tl tl' X IH]; cbn; intro f.
  - apply eta1_mkApps_f. now constructor.
  - now apply IH.
Qed.

(** CH5b (U4): one η-OnOne2 in the spine lifts under a fixed head. *)
Lemma eta_mkApps_args f l l' : OnOne2 eta1 l l' -> eta (mkApps f l) (mkApps f l').
Proof. intro. apply eta_step. now apply eta1_mkApps_args. Qed.

(** CH6 (U4): [OnOne2 R] tracks [nth_error] up to a reflexive [R]-step (any [R]). *)
Lemma OnOne2_nth_error_rc {A} (R : A -> A -> Type) (l l' : list A) (H : OnOne2 R l l') :
  forall k a, nth_error l k = Some a ->
    ∑ a', nth_error l' k = Some a' × clos_refl R a a'.
Proof.
  induction H as [hd hd' tl p|hd tl tl' X IH]; intros [|k] a; cbn.
  - intro e; noconf e. exists hd'. split; [reflexivity| now constructor].
  - intro e. exists a. split; [exact e| apply r_refl].
  - intro e; noconf e. exists hd. split; [reflexivity| apply r_refl].
  - intro e. destruct (IH k a e) as [a' [? ?]]. exists a'. now split.
Qed.
Notation onone2_eta_nth_error := (OnOne2_nth_error_rc eta1).

(* CH2 upto_domain_refl: Required from EtaL2's PCUICEtaConfluence
   (#[global] Instance Reflexive upto_domain) — not re-derived here. *)

(** CH3 (U4): η keeps a constructor-headed term constructor-headed. PROVED here
    from [eta1_mkApps_inv]: a constructor head is a [tConstruct], which has no
    [eta1] step, so η can only touch the arguments. *)
Lemma eta1_isConstruct_app a a' :
  eta1 a a' -> isConstruct_app a = true -> isConstruct_app a' = true.
Proof.
  intros he hc. unfold isConstruct_app in hc |- *.
  destruct (decompose_app a) as [f l] eqn:da. cbn in hc.
  destruct f; try discriminate hc.
  apply decompose_app_inv in da. subst a.
  eapply eta1_mkApps_inv in he as [[M' [hM e]]|[l' [hl ->]]].
  - depelim hM.
  - rewrite decompose_app_mkApps; reflexivity.
Qed.

(** fix_subst / cofix_subst congruence: one η in the mfix gives η* on every
    substitution entry (each entry [tFix mfix j -> tFix mfix' j] is one [eta1]). *)
Lemma All2_eta_fix_subst (m m' : mfixpoint term) :
  #|m| = #|m'| -> (forall j, eta1 (tFix m j) (tFix m' j)) ->
  All2 eta (fix_subst m) (fix_subst m').
Proof.
  intros Hlen Hj. unfold fix_subst. rewrite Hlen.
  generalize #|m'|. intro n. induction n; simpl.
  - constructor.
  - constructor; [apply eta_step, Hj| exact IHn].
Qed.

Lemma All2_eta_cofix_subst (m m' : mfixpoint term) :
  #|m| = #|m'| -> (forall j, eta1 (tCoFix m j) (tCoFix m' j)) ->
  All2 eta (cofix_subst m) (cofix_subst m').
Proof.
  intros Hlen Hj. unfold cofix_subst. rewrite Hlen.
  generalize #|m'|. intro n. induction n; simpl.
  - constructor.
  - constructor; [apply eta_step, Hj| exact IHn].
Qed.

(** Inversion of [eta1] out of a [tFix]: the result is a [tFix] of the same index
    and length, each def's [rarg] preserved and [dbody] moved by η*. *)
Lemma eta1_tFix_inv mfix idx N :
  eta1 (tFix mfix idx) N ->
  ∑ mfix', (N = tFix mfix' idx) × (#|mfix| = #|mfix'|) ×
           (forall j, eta1 (tFix mfix j) (tFix mfix' j)) ×
           All2 (fun d d' => (rarg d = rarg d') × eta (dbody d) (dbody d')) mfix mfix'.
Proof.
  intro he. depelim he.
  - assert (HA : All2 (fun d d' => (rarg d = rarg d') × eta (dbody d) (dbody d')) mfix mfix1).
    { eapply OnOne2_All2; [eassumption| |].
      * intros x y [? Heq]. split; [congruence|].
        assert (Hd : dbody x = dbody y) by congruence. rewrite Hd. apply eta_refl.
      * intros x. split; [reflexivity| apply eta_refl]. }
    exists mfix1.
    split; [reflexivity|].
    split; [pose proof (All2_length HA) as Hl; congruence|].
    split; [intro j; now apply fix_eta_ty| exact HA].
  - assert (HA : All2 (fun d d' => (rarg d = rarg d') × eta (dbody d) (dbody d')) mfix mfix1).
    { eapply OnOne2_All2; [eassumption| |].
      * intros x y [Hb Heq]. split; [congruence| apply eta_step, Hb].
      * intros x. split; [reflexivity| apply eta_refl]. }
    exists mfix1.
    split; [reflexivity|].
    split; [pose proof (All2_length HA) as Hl; congruence|].
    split; [intro j; now apply fix_eta_body| exact HA].
Qed.

Lemma eta1_tCoFix_inv mfix idx N :
  eta1 (tCoFix mfix idx) N ->
  ∑ mfix', (N = tCoFix mfix' idx) × (#|mfix| = #|mfix'|) ×
           (forall j, eta1 (tCoFix mfix j) (tCoFix mfix' j)) ×
           All2 (fun d d' => (rarg d = rarg d') × eta (dbody d) (dbody d')) mfix mfix'.
Proof.
  intro he. depelim he.
  - assert (HA : All2 (fun d d' => (rarg d = rarg d') × eta (dbody d) (dbody d')) mfix mfix1).
    { eapply OnOne2_All2; [eassumption| |].
      * intros x y [? Heq]. split; [congruence|].
        assert (Hd : dbody x = dbody y) by congruence. rewrite Hd. apply eta_refl.
      * intros x. split; [reflexivity| apply eta_refl]. }
    exists mfix1.
    split; [reflexivity|].
    split; [pose proof (All2_length HA) as Hl; congruence|].
    split; [intro j; now apply cofix_eta_ty| exact HA].
  - assert (HA : All2 (fun d d' => (rarg d = rarg d') × eta (dbody d) (dbody d')) mfix mfix1).
    { eapply OnOne2_All2; [eassumption| |].
      * intros x y [Hb Heq]. split; [congruence| apply eta_step, Hb].
      * intros x. split; [reflexivity| apply eta_refl]. }
    exists mfix1.
    split; [reflexivity|].
    split; [pose proof (All2_length HA) as Hl; congruence|].
    split; [intro j; now apply cofix_eta_body| exact HA].
Qed.

(** CH4f (U2/U4): one η-step out of a fixpoint keeps unfolding enabled; the
    unfolded body moves by η*. PROVED from [eta_subst] + fix_subst congruence. *)
Lemma eta1_fix_unfold mfix idx N narg fn :
  eta1 (tFix mfix idx) N -> unfold_fix mfix idx = Some (narg, fn) ->
  ∑ mfix' fn', [× N = tFix mfix' idx, unfold_fix mfix' idx = Some (narg, fn') & eta fn fn'].
Proof.
  intro he. apply eta1_tFix_inv in he as (mfix' & -> & Hlen & Hj & HA).
  unfold unfold_fix. destruct (nth_error mfix idx) as [d|] eqn:hd; [|discriminate].
  intro E; noconf E.
  eapply All2_nth_error_Some in HA as (d' & hd' & Hrarg & Hbody); [|exact hd].
  exists mfix', (subst0 (fix_subst mfix') (dbody d')). split.
  - reflexivity.
  - rewrite hd'. now rewrite <- Hrarg.
  - apply eta_subst; [now apply All2_eta_fix_subst| exact Hbody].
Qed.

Lemma eta1_cofix_unfold mfix idx N narg fn :
  eta1 (tCoFix mfix idx) N -> unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ mfix' fn', [× N = tCoFix mfix' idx, unfold_cofix mfix' idx = Some (narg, fn') & eta fn fn'].
Proof.
  intro he. apply eta1_tCoFix_inv in he as (mfix' & -> & Hlen & Hj & HA).
  unfold unfold_cofix. destruct (nth_error mfix idx) as [d|] eqn:hd; [|discriminate].
  intro E; noconf E.
  eapply All2_nth_error_Some in HA as (d' & hd' & Hrarg & Hbody); [|exact hd].
  exists mfix', (subst0 (cofix_subst mfix') (dbody d')). split.
  - reflexivity.
  - rewrite hd'. now rewrite <- Hrarg.
  - apply eta_subst; [now apply All2_eta_cofix_subst| exact Hbody].
Qed.

(* ======================================================================= *)
Section C3Unlocking.
  Context {cf : checker_flags}.
  Context (Σ : global_env).

  (* All closure facts (CH1-CH6, CH4f/CH4c) are proved globally above and in
     EtaL2's PCUICEtaConfluence (Required). This section is now hypothesis-free
     apart from the ambient Σ. *)

  (** is_constructor preserved by an η-OnOne2 on the spine (CH3 + CH6). *)
  Lemma onone2_eta_is_constructor n l l' :
    OnOne2 eta1 l l' -> is_constructor n l = true -> is_constructor n l' = true.
  Proof.
    intros H. unfold is_constructor.
    destruct (nth_error l n) eqn:e; [|discriminate].
    intro hc. eapply onone2_eta_nth_error in e as [a' [e' r]]; tea.
    rewrite e'. destruct r as [? r|]; [|assumption].
    now eapply eta1_isConstruct_app.
  Qed.

  (* ====================================================================== *)
  (** ** red_fix *)
  Lemma C3_red_fix Γ mfix idx args narg fn u :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    eta1 (mkApps (tFix mfix idx) args) u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w × eta (mkApps fn args) w' × upto_domain w w'.
  Proof.
    intros huf hic he.
    eapply eta1_mkApps_inv in he as [[M' [hM ->]]|[l' [hl ->]]].
    - destruct (eta1_fix_unfold _ _ _ _ _ hM huf) as [mfix' [fn' [-> huf' hfn]]].
      exists (mkApps fn' args), (mkApps fn' args). split; [|split].
      + constructor. now eapply red_fix.
      + now eapply eta_mkApps_head.
      + apply upto_domain_refl.
    - exists (mkApps fn l'), (mkApps fn l'). split; [|split].
      + constructor. eapply red_fix; tea. now eapply onone2_eta_is_constructor.
      + now eapply eta_mkApps_args.
      + apply upto_domain_refl.
  Qed.

  (* ====================================================================== *)
  (** ** red_cofix_case *)
  Lemma C3_red_cofix_case Γ ci p mfix idx args narg fn brs u :
    unfold_cofix mfix idx = Some (narg, fn) ->
    eta1 (tCase ci p (mkApps (tCoFix mfix idx) args) brs) u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w
          × eta (tCase ci p (mkApps fn args) brs) w' × upto_domain w w'.
  Proof.
    intros huf he. depelim he.
    - exists (tCase ci (set_pparams p params') (mkApps fn args) brs),
             (tCase ci (set_pparams p params') (mkApps fn args) brs).
      split; [|split].
      + constructor. now eapply red_cofix_case.
      + eapply eta_step. now eapply case_eta_param.
      + apply upto_domain_refl.
    - exists (tCase ci (set_preturn p preturn') (mkApps fn args) brs),
             (tCase ci (set_preturn p preturn') (mkApps fn args) brs).
      split; [|split].
      + constructor. now eapply red_cofix_case.
      + eapply eta_step. now eapply case_eta_return.
      + apply upto_domain_refl.
    - eapply eta1_mkApps_inv in he as [[M' [hM ->]]|[l' [hl ->]]].
      + destruct (eta1_cofix_unfold _ _ _ _ _ hM huf) as [mfix' [fn' [-> huf' hfn]]].
        exists (tCase ci p (mkApps fn' args) brs), (tCase ci p (mkApps fn' args) brs).
        split; [|split].
        * constructor. now eapply red_cofix_case.
        * apply eta_Case_discr. now eapply eta_mkApps_head.
        * apply upto_domain_refl.
      + exists (tCase ci p (mkApps fn l') brs), (tCase ci p (mkApps fn l') brs).
        split; [|split].
        * constructor. now eapply red_cofix_case.
        * apply eta_Case_discr. now eapply eta_mkApps_args.
        * apply upto_domain_refl.
    - exists (tCase ci p (mkApps fn args) brs'), (tCase ci p (mkApps fn args) brs').
      split; [|split].
      + constructor. now eapply red_cofix_case.
      + eapply eta_step. now eapply case_eta_brs.
      + apply upto_domain_refl.
  Qed.

  (* ====================================================================== *)
  (** ** red_cofix_proj *)
  Lemma C3_red_cofix_proj Γ pr mfix idx args narg fn u :
    unfold_cofix mfix idx = Some (narg, fn) ->
    eta1 (tProj pr (mkApps (tCoFix mfix idx) args)) u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w
          × eta (tProj pr (mkApps fn args)) w' × upto_domain w w'.
  Proof.
    intros huf he. depelim he.
    eapply eta1_mkApps_inv in he as [[M' [hM ->]]|[l' [hl ->]]].
    - destruct (eta1_cofix_unfold _ _ _ _ _ hM huf) as [mfix' [fn' [-> huf' hfn]]].
      exists (tProj pr (mkApps fn' args)), (tProj pr (mkApps fn' args)).
      split; [|split].
      + constructor. now eapply red_cofix_proj.
      + apply eta_Proj. now eapply eta_mkApps_head.
      + apply upto_domain_refl.
    - exists (tProj pr (mkApps fn l')), (tProj pr (mkApps fn l')).
      split; [|split].
      + constructor. now eapply red_cofix_proj.
      + apply eta_Proj. now eapply eta_mkApps_args.
      + apply upto_domain_refl.
  Qed.

  (* ====================================================================== *)
  (** ** red_proj *)
  Lemma C3_red_proj Γ pr args ui arg u :
    nth_error args (pr.(proj_npars) + pr.(proj_arg)) = Some arg ->
    eta1 (tProj pr (mkApps (tConstruct pr.(proj_ind) 0 ui) args)) u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w × eta arg w' × upto_domain w w'.
  Proof.
    intros hnth he. depelim he.
    eapply eta1_mkApps_inv in he as [[M' [hM ->]]|[l' [hl ->]]].
    - depelim hM.
    - destruct (onone2_eta_nth_error _ _ hl _ _ hnth) as [arg' [hnth' r]].
      exists arg', arg'. split; [|split].
      + constructor. now eapply red_proj.
      + destruct r as [? r|]; [apply eta_step; exact r| apply eta_refl].
      + apply upto_domain_refl.
  Qed.

End C3Unlocking.
