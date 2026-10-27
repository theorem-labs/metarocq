(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, row C3 (prover C, branch frac/eta-c3-c)

  Hindley strong commutation of one [red1] step with one [eta1] step, modulo
  [upto_domain]:

  [[
  C3_statement :=
    forall Σ (wfΣ : wf Σ) Γ t u v,
      red1 Σ Γ t v -> eta1 t u ->
      ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
  ]]

  [eta1], [eta1_ind_all], [eta] and [upto_domain] are the SHARED definitions of
  [PCUICEtaDefs] (plan rows U1/U3); this file ports a proof to THOSE, never a
  variant.  The running log of sources read, routes tried, cases closed and cases
  that failed is [lanes/eta/EtaC3C.md].

  Route (prover C): induction on [red1] via [red1_ind_all], inverting [eta1] in
  each case, reusing the *structure* of [origin/eta_postpo]'s [red1_eta1_diamond]
  ([PCUICEtaReduction.v:1471-2198]) but with the one-sided conclusion (≤1 red1 on
  the η side, eta* on the red side).  The four unlocking cases ([red_fix],
  [red_cofix_case], [red_cofix_proj], [red_proj]) come before the congruences. *)

From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Reflect.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICCases
     PCUICLiftSubst PCUICUnivSubst PCUICOnFreeVars PCUICSigmaCalculus
     PCUICReduction PCUICEtaDefs PCUICInduction PCUICTyping.

From Stdlib Require Import ssreflect ssrbool.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

Derive Signature for eta1.
Derive Signature for upto_domain.
Derive Signature for clos_refl.
Derive Signature for clos_refl_trans.

(** ** [upto_domain] is reflexive (plan U1). *)

Lemma upto_domain_refl t : upto_domain t t.
Proof.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. induction X; constructor; auto.
  - destruct X as [IHpars [IHctx IHret]]. constructor; auto; try reflexivity.
    + induction IHpars; constructor; auto.
    + induction X0 as [|?? [? ?]]; constructor; auto. split; [reflexivity|assumption].
  - constructor. induction X; constructor; auto. split; [|split]; auto. 1-2:apply p.
  - constructor. induction X; constructor; auto. split; [|split]; auto. 1-2:apply p.
  - destruct p as [? p]; destruct p; cbn in X; try solve [constructor; constructor].
    constructor. destruct X as [hd [hty hval]]. constructor; auto.
    induction hval; constructor; auto.
Qed.

#[global] Instance upto_domain_Reflexive : Reflexive upto_domain := upto_domain_refl.

(** ** Congruence lemmas for [eta] (the reflexive-transitive closure). *)

Lemma eta_App_l M N a : eta M N -> eta (tApp M a) (tApp N a).
Proof.
  induction 1.
  - apply rt_step. now apply app_eta_l.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma eta_App_r M a b : eta a b -> eta (tApp M a) (tApp M b).
Proof.
  induction 1.
  - apply rt_step. now apply app_eta_r.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma eta_mkApps_f M N l : eta M N -> eta (mkApps M l) (mkApps N l).
Proof.
  intros H. induction l using rev_ind.
  - exact H.
  - rewrite !mkApps_app /=. now apply eta_App_l.
Qed.

Lemma eta1_mkApps_f M N l : eta1 M N -> eta1 (mkApps M l) (mkApps N l).
Proof.
  intros H. induction l using rev_ind.
  - exact H.
  - rewrite !mkApps_app /=. now apply app_eta_l.
Qed.

Lemma eta_mkApps_args M l l' : All2 eta l l' -> eta (mkApps M l) (mkApps M l').
Proof.
  induction 1 in M |- *; cbn.
  - apply rt_refl.
  - eapply rt_trans; [|apply IHX]. now apply eta_mkApps_f, eta_App_r.
Qed.

Lemma eta_mkApps M N l l' : eta M N -> All2 eta l l' ->
  eta (mkApps M l) (mkApps N l').
Proof.
  intros HMN Hll'. eapply rt_trans.
  - apply eta_mkApps_f, HMN.
  - now apply eta_mkApps_args.
Qed.

Lemma eta1_eta M N : eta1 M N -> eta M N.
Proof. apply rt_step. Qed.

(** ** Inversion of one [eta1] step on a [mkApps].  (2020 [eta1_mkApps_inv].) *)

Lemma eta1_mkApps_inv M l N :
  eta1 (mkApps M l) N ->
  (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l in M, N |- *; cbn.
  - intros H. left. now exists N.
  - intros H. apply IHl in H as [[M' [He ->]]|[l' [Hl ->]]].
    + depelim He.
      * left. now exists N1.
      * right. exists (N2 :: l). split; now constructor.
    + right. exists (a :: l'). split; now constructor.
Qed.

(** ** One [eta1] step commutes with [subst] and [lift] (plan rows U2-ish). *)

Lemma eta1_subst s t t' : eta1 t t' -> forall k, eta1 (subst s k t) (subst s k t').
Proof.
  intros H. revert t t' H.
  apply (eta1_ind_all (fun t t' => forall k, eta1 (subst s k t) (subst s k t')));
    intros; cbn.
  - rewrite commut_lift_subst. apply eta_red.
  - apply abs_eta_l; auto.
  - apply abs_eta_r; auto.
  - apply letin_eta_def; auto.
  - apply letin_eta_ty; auto.
  - apply letin_eta_body; auto.
  - replace (map_predicate_k id (subst s) k (set_pparams p params'))
      with (set_pparams (map_predicate_k id (subst s) k p) (map (subst s k) params'))
      by reflexivity.
    eapply case_eta_param. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy k).
  - replace (map_predicate_k id (subst s) k (set_preturn p preturn'))
      with (set_preturn (map_predicate_k id (subst s) k p)
                        (subst s (#|pcontext p| + k) preturn'))
      by reflexivity.
    eapply case_eta_return. cbn. auto.
  - apply case_eta_discr; auto.
  - eapply case_eta_brs. induction X; cbn.
    + constructor. destruct p0 as [[He HP] Heq]. split; cbn.
      * rewrite Heq. apply (HP (#|bcontext hd'| + k)).
      * now rewrite Heq.
    + now constructor.
  - apply proj_eta; auto.
  - apply app_eta_l; auto.
  - apply app_eta_r; auto.
  - apply prod_eta_l; auto.
  - apply prod_eta_r; auto.
  - eapply evar_eta. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy k).
  - cbn. rewrite (OnOne2_length X). eapply fix_eta_ty.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP k).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. rewrite (OnOne2_length X). eapply fix_eta_body.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP D).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. rewrite (OnOne2_length X). eapply cofix_eta_ty.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP k).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. rewrite (OnOne2_length X). eapply cofix_eta_body.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP D).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - eapply array_eta_val. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy k).
  - eapply array_eta_def; cbn; auto.
  - eapply array_eta_type; cbn; auto.
Qed.

Lemma eta1_lift n t t' : eta1 t t' -> forall k, eta1 (lift n k t) (lift n k t').
Proof.
  intros H. revert t t' H.
  apply (eta1_ind_all (fun t t' => forall k, eta1 (lift n k t) (lift n k t')));
    intros; cbn.
  - assert (E : lift n (S k) (lift0 1 t) = lift0 1 (lift n k t)).
    { rewrite (permute_lift t n k 1 0); [lia|]. f_equal. lia. }
    rewrite E. apply eta_red.
  - apply abs_eta_l; auto.
  - apply abs_eta_r; auto.
  - apply letin_eta_def; auto.
  - apply letin_eta_ty; auto.
  - apply letin_eta_body; auto.
  - replace (map_predicate_k id (lift n) k (set_pparams p params'))
      with (set_pparams (map_predicate_k id (lift n) k p) (map (lift n k) params'))
      by reflexivity.
    eapply case_eta_param. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy k).
  - replace (map_predicate_k id (lift n) k (set_preturn p preturn'))
      with (set_preturn (map_predicate_k id (lift n) k p)
                        (lift n (#|pcontext p| + k) preturn'))
      by reflexivity.
    eapply case_eta_return. cbn. auto.
  - apply case_eta_discr; auto.
  - eapply case_eta_brs. induction X; cbn.
    + constructor. destruct p0 as [[He HP] Heq]. split; cbn.
      * rewrite Heq. apply (HP (#|bcontext hd'| + k)).
      * now rewrite Heq.
    + now constructor.
  - apply proj_eta; auto.
  - apply app_eta_l; auto.
  - apply app_eta_r; auto.
  - apply prod_eta_l; auto.
  - apply prod_eta_r; auto.
  - eapply evar_eta. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy k).
  - cbn. rewrite (OnOne2_length X). eapply fix_eta_ty.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP k).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. rewrite (OnOne2_length X). eapply fix_eta_body.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP D).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. rewrite (OnOne2_length X). eapply cofix_eta_ty.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP k).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - cbn. rewrite (OnOne2_length X). eapply cofix_eta_body.
    set (D := #|mfix1| + k). clearbody D. induction X; cbn.
    + constructor. destruct p as [[He HP] Heq]. split.
      * apply (HP D).
      * revert Heq; unfold map_def; cbn; congruence.
    + now constructor.
  - eapply array_eta_val. eapply OnOne2_map.
    eapply OnOne2_impl; [exact X|]. intros x y Hxy. exact (snd Hxy k).
  - eapply array_eta_def; cbn; auto.
  - eapply array_eta_type; cbn; auto.
Qed.

Lemma eta1_lift0 n t t' : eta1 t t' -> eta1 (lift0 n t) (lift0 n t').
Proof. intros H. now apply eta1_lift. Qed.

(** ** The C3 statement (plan §3 row C3). *)

Definition C3_statement {cf : checker_flags} :=
  forall (Σ : global_env) (wfΣ : wf Σ) (Γ : context) (t u v : term),
    red1 Σ Γ t v -> eta1 t u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
