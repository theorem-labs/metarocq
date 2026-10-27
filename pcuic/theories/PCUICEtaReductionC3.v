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
   U-row Context hypotheses: standard eta-closure, plan rows U1/U2/U4, PROVED on the
   2020 AST, discharged by L2/L7 with the definitions. No Admitted, no Axiom. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICCases
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICEtaDefs.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.

Derive Signature for eta1.

Set Default Goal Selector "!".
Import ListNotations.

Section C3Unlocking.
  Context {cf : checker_flags}.
  Context (Σ : global_env).

  (* ---- U-row Context hypotheses (all on C3Prover3.md's declared list) ---- *)

  (** CH1 (U4): η under a spine moves the head or exactly one argument.
      PROVED origin/eta_postpo:PCUICEtaReduction.v:1223-1234 (old AST). *)
  Context (eta1_mkApps_inv :
    forall M l N, eta1 (mkApps M l) N ->
      (∑ M', eta1 M M' × N = mkApps M' l)
    + (∑ l', OnOne2 eta1 l l' × N = mkApps M l')).

  (** CH2 (U1): [upto_domain] is reflexive. PROVED 2020. *)
  Context (upto_domain_refl : forall t, upto_domain t t).

  (** CH3 (U4): η keeps a constructor-headed term constructor-headed. *)
  Context (eta1_isConstruct_app :
    forall a a', eta1 a a' -> isConstruct_app a = true -> isConstruct_app a' = true).

  (** CH4f (U2/U4): one η-step out of a fixpoint keeps it a fixpoint of the same
      index, unfolding stays enabled, and the unfolded body moves by η*. *)
  Context (eta1_fix_unfold :
    forall mfix idx N narg fn,
      eta1 (tFix mfix idx) N ->
      unfold_fix mfix idx = Some (narg, fn) ->
      ∑ mfix' fn', [× N = tFix mfix' idx, unfold_fix mfix' idx = Some (narg, fn') & eta fn fn']).

  (** CH4c (U2/U4): the cofix twin. *)
  Context (eta1_cofix_unfold :
    forall mfix idx N narg fn,
      eta1 (tCoFix mfix idx) N ->
      unfold_cofix mfix idx = Some (narg, fn) ->
      ∑ mfix' fn', [× N = tCoFix mfix' idx, unfold_cofix mfix' idx = Some (narg, fn') & eta fn fn']).

  (** CH5a (U4 congruence): η* in the head lifts under a fixed spine. *)
  Context (eta_mkApps_head :
    forall f f' l, eta f f' -> eta (mkApps f l) (mkApps f' l)).

  (** CH5b (U4 congruence): one η-OnOne2 in the spine lifts under a fixed head. *)
  Context (eta_mkApps_args :
    forall f l l', OnOne2 eta1 l l' -> eta (mkApps f l) (mkApps f l')).

  (** CH6 (U4): [OnOne2 eta1] tracks [nth_error] up to a reflexive η-step. *)
  Context (onone2_eta_nth_error :
    forall (l l' : list term) k a, OnOne2 eta1 l l' -> nth_error l k = Some a ->
      ∑ a', nth_error l' k = Some a' × clos_refl eta1 a a').

  (* ---- local helpers ---- *)

  Lemma eta_step {x y} : eta1 x y -> eta x y.
  Proof. intro. now constructor. Qed.

  Lemma eta_refl {x} : eta x x.
  Proof. apply rt_refl. Qed.

  Lemma eta_trans {x y z} : eta x y -> eta y z -> eta x z.
  Proof. intros. eapply rt_trans; eauto. Qed.

  (** Lift any one-step η congruence [f] to the reflexive-transitive closure. *)
  Lemma eta_congr (f : term -> term) :
    (forall x y, eta1 x y -> eta1 (f x) (f y)) ->
    forall x y, eta x y -> eta (f x) (f y).
  Proof.
    intros Hf x y H. induction H.
    - apply eta_step. now apply Hf.
    - apply eta_refl.
    - eapply eta_trans; eauto.
  Qed.

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
    - (* η in the head tFix: re-fire red_fix on mfix', body joins by η* *)
      destruct (eta1_fix_unfold _ _ _ _ _ hM huf) as [mfix' [fn' [-> huf' hfn]]].
      exists (mkApps fn' args), (mkApps fn' args). split; [|split].
      + constructor. now eapply red_fix.
      + now eapply eta_mkApps_head.
      + apply upto_domain_refl.
    - (* η in one argument: re-fire red_fix on args', spine joins by η* *)
      exists (mkApps fn l'), (mkApps fn l'). split; [|split].
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
    - (* case_eta_param *)
      exists (tCase ci (set_pparams p params') (mkApps fn args) brs),
             (tCase ci (set_pparams p params') (mkApps fn args) brs).
      split; [|split].
      + constructor. now eapply red_cofix_case.
      + eapply eta_step. now eapply case_eta_param.
      + apply upto_domain_refl.
    - (* case_eta_return *)
      exists (tCase ci (set_preturn p preturn') (mkApps fn args) brs),
             (tCase ci (set_preturn p preturn') (mkApps fn args) brs).
      split; [|split].
      + constructor. now eapply red_cofix_case.
      + eapply eta_step. now eapply case_eta_return.
      + apply upto_domain_refl.
    - (* case_eta_discr : η inside the discriminee *)
      eapply eta1_mkApps_inv in he as [[M' [hM ->]]|[l' [hl ->]]].
      + destruct (eta1_cofix_unfold _ _ _ _ _ hM huf) as [mfix' [fn' [-> huf' hfn]]].
        exists (tCase ci p (mkApps fn' args) brs), (tCase ci p (mkApps fn' args) brs).
        split; [|split].
        * constructor. now eapply red_cofix_case.
        * eapply (eta_congr (fun z => tCase ci p z brs)); [| now eapply eta_mkApps_head].
          intros ?? h. now eapply case_eta_discr.
        * apply upto_domain_refl.
      + exists (tCase ci p (mkApps fn l') brs), (tCase ci p (mkApps fn l') brs).
        split; [|split].
        * constructor. now eapply red_cofix_case.
        * eapply (eta_congr (fun z => tCase ci p z brs)); [| now eapply eta_mkApps_args].
          intros ?? h. now eapply case_eta_discr.
        * apply upto_domain_refl.
    - (* case_eta_brs *)
      exists (tCase ci p (mkApps fn args) brs'), (tCase ci p (mkApps fn args) brs').
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
      + eapply (eta_congr (fun z => tProj pr z)); [| now eapply eta_mkApps_head].
        intros ?? h. now eapply proj_eta.
      + apply upto_domain_refl.
    - exists (tProj pr (mkApps fn l')), (tProj pr (mkApps fn l')).
      split; [|split].
      + constructor. now eapply red_cofix_proj.
      + eapply (eta_congr (fun z => tProj pr z)); [| now eapply eta_mkApps_args].
        intros ?? h. now eapply proj_eta.
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
    - (* η in the tConstruct head is impossible *)
      depelim hM.
    - (* η in one argument: re-fire red_proj, selected arg joins by ≤1 η *)
      destruct (onone2_eta_nth_error _ _ _ _ hl hnth) as [arg' [hnth' r]].
      exists arg', arg'. split; [|split].
      + constructor. now eapply red_proj.
      + destruct r as [? r|]; [apply eta_step; exact r| apply eta_refl].
      + apply upto_domain_refl.
  Qed.

End C3Unlocking.
