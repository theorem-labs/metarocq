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

(** ** [eta] (rt-closure) under [lift]/[subst], and congruence lemmas. *)

Lemma eta_lift n k t t' : eta t t' -> eta (lift n k t) (lift n k t').
Proof.
  induction 1.
  - apply rt_step. now apply eta1_lift.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma eta_lift0 n t t' : eta t t' -> eta (lift0 n t) (lift0 n t').
Proof. apply eta_lift. Qed.

Lemma eta_subst_r s k t t' : eta t t' -> eta (subst s k t) (subst s k t').
Proof.
  induction 1.
  - apply rt_step. now apply eta1_subst.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma eta_Lambda_l na A A' b : eta A A' -> eta (tLambda na A b) (tLambda na A' b).
Proof.
  induction 1; [apply rt_step; now apply abs_eta_l|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_Lambda_r na A b b' : eta b b' -> eta (tLambda na A b) (tLambda na A b').
Proof.
  induction 1; [apply rt_step; now apply abs_eta_r|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_Lambda na A A' b b' : eta A A' -> eta b b' ->
  eta (tLambda na A b) (tLambda na A' b').
Proof. intros. eapply rt_trans; [apply eta_Lambda_l|apply eta_Lambda_r]; eauto. Qed.

Lemma eta_Prod_l na A A' b : eta A A' -> eta (tProd na A b) (tProd na A' b).
Proof.
  induction 1; [apply rt_step; now apply prod_eta_l|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_Prod_r na A b b' : eta b b' -> eta (tProd na A b) (tProd na A b').
Proof.
  induction 1; [apply rt_step; now apply prod_eta_r|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_Prod na A A' b b' : eta A A' -> eta b b' ->
  eta (tProd na A b) (tProd na A' b').
Proof. intros. eapply rt_trans; [apply eta_Prod_l|apply eta_Prod_r]; eauto. Qed.

Lemma eta_LetIn_b na b b' t c : eta b b' -> eta (tLetIn na b t c) (tLetIn na b' t c).
Proof.
  induction 1; [apply rt_step; now apply letin_eta_def|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_LetIn_t na b t t' c : eta t t' -> eta (tLetIn na b t c) (tLetIn na b t' c).
Proof.
  induction 1; [apply rt_step; now apply letin_eta_ty|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_LetIn_c na b t c c' : eta c c' -> eta (tLetIn na b t c) (tLetIn na b t c').
Proof.
  induction 1; [apply rt_step; now apply letin_eta_body|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma eta_LetIn na b b' t t' c c' : eta b b' -> eta t t' -> eta c c' ->
  eta (tLetIn na b t c) (tLetIn na b' t' c').
Proof.
  intros. eapply rt_trans; [apply eta_LetIn_b; eauto|].
  eapply rt_trans; [apply eta_LetIn_t; eauto|apply eta_LetIn_c; eauto].
Qed.

Lemma eta_Proj p c c' : eta c c' -> eta (tProj p c) (tProj p c').
Proof.
  induction 1; [apply rt_step; now apply proj_eta|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma eta_App a a' b b' : eta a a' -> eta b b' -> eta (tApp a b) (tApp a' b').
Proof. intros. eapply rt_trans; [apply eta_App_l|apply eta_App_r]; eauto. Qed.

(** List congruences, via [All2_many_OnOne2] + a single-position helper. *)

Lemma eta_Evar_pos ev pre post X Y : eta X Y ->
  eta (tEvar ev (pre ++ X :: post)) (tEvar ev (pre ++ Y :: post)).
Proof.
  induction 1.
  - apply rt_step. apply evar_eta. induction pre; cbn.
    + now constructor.
    + now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Evar ev l l' : All2 eta l l' -> eta (tEvar ev l) (tEvar ev l').
Proof.
  intros h. apply All2_many_OnOne2 in h. induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & He & -> & ->).
    now apply eta_Evar_pos.
Qed.

Lemma eta_Case_discr ci p c c' brs : eta c c' ->
  eta (tCase ci p c brs) (tCase ci p c' brs).
Proof.
  induction 1; [apply rt_step; now apply case_eta_discr|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma eta_Case_preturn ci p r c brs : eta p.(preturn) r ->
  eta (tCase ci p c brs) (tCase ci (set_preturn p r) c brs).
Proof.
  intros h. remember (preturn p) as pr eqn:E. revert p E.
  induction h; intros p E; subst.
  - apply rt_step. now apply case_eta_return.
  - destruct p; apply rt_refl.
  - eapply rt_trans.
    + now apply (IHh1 p).
    + assert (set_preturn p z = set_preturn (set_preturn p y) z) as -> by (now destruct p).
      apply (IHh2 (set_preturn p y)). now destruct p.
Qed.

Lemma eta_Case_pars_pos ci p c brs pre post X Y : eta X Y ->
  eta (tCase ci (set_pparams p (pre ++ X :: post)) c brs)
      (tCase ci (set_pparams p (pre ++ Y :: post)) c brs).
Proof.
  induction 1.
  - apply rt_step.
    assert (E : set_pparams (set_pparams p (pre ++ x :: post)) (pre ++ y :: post)
                = set_pparams p (pre ++ y :: post)) by (now destruct p).
    rewrite <- E. apply case_eta_param. cbn. induction pre; cbn; now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Case_pars_gen ci p c brs L0 L1 :
  clos_refl_trans_n1 (OnOne2 eta) L0 L1 ->
  eta (tCase ci (set_pparams p L0) c brs) (tCase ci (set_pparams p L1) c brs).
Proof.
  intros h; induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (x & y' & u & v & He & -> & ->).
    now apply eta_Case_pars_pos.
Qed.
Lemma eta_Case_pars ci p c brs pars' : All2 eta p.(pparams) pars' ->
  eta (tCase ci p c brs) (tCase ci (set_pparams p pars') c brs).
Proof.
  intros h. apply All2_many_OnOne2 in h.
  assert (tCase ci p c brs = tCase ci (set_pparams p (pparams p)) c brs) as ->.
  { f_equal. now destruct p. }
  now apply eta_Case_pars_gen.
Qed.

(** Case branches (change one [bbody] by [eta], [bcontext] preserved). *)
Lemma eta_Case_brs_pos ci p c pre post na X Y : eta X Y ->
  eta (tCase ci p c (pre ++ {| bcontext := na; bbody := X |} :: post))
      (tCase ci p c (pre ++ {| bcontext := na; bbody := Y |} :: post)).
Proof.
  induction 1.
  - apply rt_step. apply case_eta_brs. induction pre; cbn.
    + constructor. split; [exact r|reflexivity].
    + now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Case_brs_gen ci p c B0 B1 :
  clos_refl_trans_n1 (OnOne2 (on_Trel_eq eta bbody bcontext)) B0 B1 ->
  eta (tCase ci p c B0) (tCase ci p c B1).
Proof.
  intros h; induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & (He & Heq) & -> & ->).
    destruct a as [nx bx], b as [ny by']. cbn in *. subst ny.
    now apply eta_Case_brs_pos.
Qed.
Lemma eta_Case_brs ci p c brs brs' :
  All2 (on_Trel_eq eta bbody bcontext) brs brs' ->
  eta (tCase ci p c brs) (tCase ci p c brs').
Proof. intros h. apply All2_many_OnOne2 in h. now apply eta_Case_brs_gen. Qed.

(** Fix / CoFix (one [dtype] or [dbody] changes by [eta], other fields preserved). *)
Lemma eta_Fix_ty_pos idx na bo ra pre post X Y : eta X Y ->
  eta (tFix (pre ++ mkdef term na X bo ra :: post) idx)
      (tFix (pre ++ mkdef term na Y bo ra :: post) idx).
Proof.
  induction 1.
  - apply rt_step. apply fix_eta_ty. induction pre; cbn.
    + constructor. split; [exact r|reflexivity].
    + now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Fix_ty idx m0 m1 :
  All2 (on_Trel_eq eta dtype (fun x => (dname x, dbody x, rarg x))) m0 m1 ->
  eta (tFix m0 idx) (tFix m1 idx).
Proof.
  intros h. apply All2_many_OnOne2 in h. induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & (He & Heq) & -> & ->).
    destruct a as [nx tx bx rx], b as [ny ty by' ry]. cbn in *.
    inversion Heq; subst. now apply eta_Fix_ty_pos.
Qed.
Lemma eta_Fix_body_pos idx na ty ra pre post X Y : eta X Y ->
  eta (tFix (pre ++ mkdef term na ty X ra :: post) idx)
      (tFix (pre ++ mkdef term na ty Y ra :: post) idx).
Proof.
  induction 1.
  - apply rt_step. apply fix_eta_body. induction pre; cbn.
    + constructor. split; [exact r|reflexivity].
    + now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Fix_body idx m0 m1 :
  All2 (on_Trel_eq eta dbody (fun x => (dname x, dtype x, rarg x))) m0 m1 ->
  eta (tFix m0 idx) (tFix m1 idx).
Proof.
  intros h. apply All2_many_OnOne2 in h. induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & (He & Heq) & -> & ->).
    destruct a as [nx tx bx rx], b as [ny ty by' ry]. cbn in *.
    inversion Heq; subst. now apply eta_Fix_body_pos.
Qed.
Lemma eta_CoFix_ty_pos idx na bo ra pre post X Y : eta X Y ->
  eta (tCoFix (pre ++ mkdef term na X bo ra :: post) idx)
      (tCoFix (pre ++ mkdef term na Y bo ra :: post) idx).
Proof.
  induction 1.
  - apply rt_step. apply cofix_eta_ty. induction pre; cbn.
    + constructor. split; [exact r|reflexivity].
    + now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_CoFix_ty idx m0 m1 :
  All2 (on_Trel_eq eta dtype (fun x => (dname x, dbody x, rarg x))) m0 m1 ->
  eta (tCoFix m0 idx) (tCoFix m1 idx).
Proof.
  intros h. apply All2_many_OnOne2 in h. induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & (He & Heq) & -> & ->).
    destruct a as [nx tx bx rx], b as [ny ty by' ry]. cbn in *.
    inversion Heq; subst. now apply eta_CoFix_ty_pos.
Qed.
Lemma eta_CoFix_body_pos idx na ty ra pre post X Y : eta X Y ->
  eta (tCoFix (pre ++ mkdef term na ty X ra :: post) idx)
      (tCoFix (pre ++ mkdef term na ty Y ra :: post) idx).
Proof.
  induction 1.
  - apply rt_step. apply cofix_eta_body. induction pre; cbn.
    + constructor. split; [exact r|reflexivity].
    + now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_CoFix_body idx m0 m1 :
  All2 (on_Trel_eq eta dbody (fun x => (dname x, dtype x, rarg x))) m0 m1 ->
  eta (tCoFix m0 idx) (tCoFix m1 idx).
Proof.
  intros h. apply All2_many_OnOne2 in h. induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & (He & Heq) & -> & ->).
    destruct a as [nx tx bx rx], b as [ny ty by' ry]. cbn in *.
    inversion Heq; subst. now apply eta_CoFix_body_pos.
Qed.

(** Primitive arrays. *)
Lemma eta_Array_default arr X Y : eta X Y ->
  eta (tPrim (primArray; primArrayModel (set_array_default arr X)))
      (tPrim (primArray; primArrayModel (set_array_default arr Y))).
Proof.
  induction 1.
  - apply rt_step.
    assert (E : set_array_default (set_array_default arr x) y = set_array_default arr y)
      by (now destruct arr).
    rewrite <- E. apply (array_eta_def (set_array_default arr x) y). now destruct arr.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Array_type arr X Y : eta X Y ->
  eta (tPrim (primArray; primArrayModel (set_array_type arr X)))
      (tPrim (primArray; primArrayModel (set_array_type arr Y))).
Proof.
  induction 1.
  - apply rt_step.
    assert (E : set_array_type (set_array_type arr x) y = set_array_type arr y)
      by (now destruct arr).
    rewrite <- E. apply (array_eta_type (set_array_type arr x) y). now destruct arr.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Array_val_pos arr pre post X Y : eta X Y ->
  eta (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ X :: post))))
      (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ Y :: post)))).
Proof.
  induction 1.
  - apply rt_step.
    assert (E : set_array_value (set_array_value arr (pre ++ x :: post)) (pre ++ y :: post)
                = set_array_value arr (pre ++ y :: post)) by (now destruct arr).
    rewrite <- E. apply (array_eta_val (set_array_value arr (pre ++ x :: post)) (pre ++ y :: post)).
    cbn. induction pre; cbn; now constructor.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.
Lemma eta_Array_val_gen arr L0 L1 :
  clos_refl_trans_n1 (OnOne2 eta) L0 L1 ->
  eta (tPrim (primArray; primArrayModel (set_array_value arr L0)))
      (tPrim (primArray; primArrayModel (set_array_value arr L1))).
Proof.
  intros h; induction h.
  - apply rt_refl.
  - eapply rt_trans; [exact IHh|].
    apply OnOne2_split in r as (a & b & u & v & He & -> & ->).
    assert (E0 : set_array_value arr (u ++ a :: v)
                 = set_array_value (set_array_value arr (u ++ a :: v)) (u ++ a :: v))
      by (now destruct arr).
    assert (E1 : set_array_value (set_array_value arr (u ++ a :: v)) (u ++ b :: v)
                 = set_array_value arr (u ++ b :: v)) by (now destruct arr).
    rewrite E0 -E1. now apply eta_Array_val_pos.
Qed.
Lemma eta_Array_val arr value :
  All2 eta arr.(array_value) value ->
  eta (tPrim (primArray; primArrayModel arr))
      (tPrim (primArray; primArrayModel (set_array_value arr value))).
Proof.
  intros h. apply All2_many_OnOne2 in h.
  assert (E : arr = set_array_value arr (array_value arr)) by (now destruct arr).
  rewrite {1}E. now apply eta_Array_val_gen.
Qed.

(** ** The C3 statement (plan §3 row C3)

  AUTHORITATIVE form, as re-hardened by the lane (`agent://ArityLane.EtaL2`,
  2026-10-27): [wf Σ] (C2's premise, [origin/eta_postpo:PCUICEtaReduction.v:1471])
  plus the two scoping premises.  Both hardenings are forced:
  - without [wf Σ] an *open* constant body ([cst_body = Some (tRel 0)]) lets
    [red_delta] destroy the η-redex under a λ, and nothing on the η side can
    recover it (found independently here and by C3Prover1);
  - without the scoping premises the unscoped form is false on ill-scoped branch
    contexts (EtaC3D's tCase model).
  The four unlocking cases ([red_fix], [red_cofix_case], [red_cofix_proj],
  [red_proj]) do not use either premise. *)

Definition C3_statement {cf : checker_flags} :=
  forall (Σ : global_env) (Γ : context) (t u v : term),
    wf Σ ->
    is_closed_context Γ ->
    is_open_term Γ t ->
    red1 Σ Γ t v ->
    eta1 t u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
