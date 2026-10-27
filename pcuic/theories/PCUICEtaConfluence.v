(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane L2: confluence of βη up to [upto_domain].

   Builds on the shared syntactic relations of [PCUICEtaDefs] ([eta1],
   [upto_domain]). This file owns the L2 rows of plan.md rev 11 §3:
   - [upto_domain] is an equivalence (completes U1), and [upto_domain_ctx],
     the declarationwise lift of [upto_domain] to contexts (annotations
     ignored), used as the related-context premise of C1a;
   - C1a/C1b/C1c: the reflexive-closure commutations of [red1]/[eta1] with
     [upto_domain]/[compare_term_eta] (the one-step forms are false, B3(b));
   - C2 [red1_eta1_diamond], U8 [eta_confluence_upto];
   - C4: βη confluence up to [upto_domain] by Hindley–Rosen, once C3 lands. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICPrimitive PCUICInduction PCUICReduction
     PCUICEquality PCUICCases PCUICEtaDefs.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Local Open Scope type_scope.

Set Default Goal Selector "!".

(** ** [upto_domain] is an equivalence (completes U1) *)
Lemma All2_upto_sym {l l'} :
  All (fun t => forall v, upto_domain t v -> upto_domain v t) l ->
  All2 upto_domain l l' -> All2 upto_domain l' l.
Proof.
  intros H a. induction a in H |- *; depelim H; constructor; eauto.
Qed.

Lemma All2_upto_trans {l1 l2 l3} :
  All (fun t => forall v w, upto_domain t v -> upto_domain v w -> upto_domain t w) l1 ->
  All2 upto_domain l1 l2 -> All2 upto_domain l2 l3 -> All2 upto_domain l1 l3.
Proof.
  intros H a b. induction a in l3, H, b |- *; depelim b; depelim H; constructor; eauto.
Qed.

Lemma All2_branch_trans {brs1 brs2 brs3} :
  All (fun x => forall v w, upto_domain x.(bbody) v -> upto_domain v w -> upto_domain x.(bbody) w) brs1 ->
  All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext) × upto_domain x.(bbody) y.(bbody)) brs1 brs2 ->
  All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext) × upto_domain x.(bbody) y.(bbody)) brs2 brs3 ->
  All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext) × upto_domain x.(bbody) y.(bbody)) brs1 brs3.
Proof.
  intros H a b. induction a in brs3, b, H |- *; depelim b; depelim H; constructor.
  2: eapply IHa; eauto.
  repeat match goal with Hp : _ × _ |- _ => destruct Hp end.
  split; [etransitivity; eassumption | eauto].
Qed.

Lemma All2_mfix_trans {m1 m2 m3} :
  All (fun d => (forall v w, upto_domain d.(dtype) v -> upto_domain v w -> upto_domain d.(dtype) w) ×
                (forall v w, upto_domain d.(dbody) v -> upto_domain v w -> upto_domain d.(dbody) w)) m1 ->
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) × x.(rarg) = y.(rarg)) m1 m2 ->
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) × x.(rarg) = y.(rarg)) m2 m3 ->
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) × x.(rarg) = y.(rarg)) m1 m3.
Proof.
  intros H a b. induction a in m3, b, H |- *; depelim b; depelim H; constructor.
  2: eapply IHa; eauto.
  repeat match goal with Hp : _ × _ |- _ => destruct Hp end.
  repeat split; [eauto | eauto | etransitivity; eassumption].
Qed.


#[global] Instance upto_domain_refl : CRelationClasses.Reflexive upto_domain.
Proof.
  intros t.
  induction t using term_forall_list_ind; try solve [constructor; eauto].
  - constructor. eapply All_All2; eauto.
  - destruct X as (Hpars & _ & Hret). constructor; eauto.
    + eapply All_All2; eauto.
    + reflexivity.
    + eapply All_All2; eauto. cbn. intros br [_ Hb]. split; [reflexivity|exact Hb].
  - constructor. eapply All_All2; eauto. intros d [Hty Hbo]. repeat split; auto.
  - constructor. eapply All_All2; eauto. intros d [Hty Hbo]. repeat split; auto.
  - constructor. destruct p as [? m]; destruct m; cbn in X; try solve [constructor].
    destruct X as (Hty & Hdef & Hval). constructor.
    + reflexivity.
    + exact Hdef.
    + exact Hty.
    + eapply All_All2; eauto.
Qed.

#[global] Instance upto_domain_sym : CRelationClasses.Symmetric upto_domain.
Proof.
  intros u v e.
  induction u in v, e |- * using term_forall_list_ind; depelim e.
  all: try solve [constructor; eauto].
  - (* Evar *) constructor. eapply All2_sym; solve_all.
  - (* Case *) destruct X as (Hpar & _ & Hret). constructor.
    + eapply All2_sym; solve_all.
    + now symmetry.
    + now symmetry.
    + now apply Hret.
    + eauto.
    + clear -X0 a1.
      induction a1 in X0 |- *; depelim X0; constructor.
      * destruct r as [Hc Hb], p as [_ HP]. split; [now symmetry|now apply HP].
      * now apply IHa1.
  - (* Fix *) constructor. clear -X a.
    induction a in X |- *; depelim X; constructor.
    * destruct r as (Ht & Hb & Hr), p as [HPt HPb].
      repeat split; [now apply HPt|now apply HPb|now symmetry].
    * now apply IHa.
  - (* CoFix *) constructor. clear -X a.
    induction a in X |- *; depelim X; constructor.
    * destruct r as (Ht & Hb & Hr), p as [HPt HPb].
      repeat split; [now apply HPt|now apply HPb|now symmetry].
    * now apply IHa.
  - (* Prim *) constructor. depelim o; try solve [constructor].
    destruct X as (HPt & HPd & HPv). constructor.
    + now symmetry.
    + now apply HPd.
    + now apply HPt.
    + eapply All2_upto_sym; eauto.
Qed.

#[global] Instance upto_domain_trans : CRelationClasses.Transitive upto_domain.
Proof.
  intros u v w e1 e2.
  induction u in v, w, e1, e2 |- * using term_forall_list_ind;
    depelim e1; depelim e2.
  all: try solve [constructor; eauto].
  - (* Evar *) constructor. eapply All2_upto_trans; eauto.
  - (* Case *) destruct X as (Hpar & _ & Hret). constructor.
    + eapply All2_upto_trans; eauto.
    + etransitivity; eassumption.
    + etransitivity; eassumption.
    + eapply Hret; eassumption.
    + eauto.
    + eapply All2_branch_trans; [| eassumption | eassumption].
      eapply All_impl; [exact X0|]. intros ? []; assumption.
  - (* Fix *) constructor.
    eapply All2_mfix_trans; [exact X | eassumption | eassumption].
  - (* CoFix *) constructor.
    eapply All2_mfix_trans; [exact X | eassumption | eassumption].
  - (* Prim *) constructor. depelim o; depelim o0; try solve [constructor].
    destruct X as (HPt & HPd & HPv). constructor.
    + etransitivity; eassumption.
    + eapply HPd; eassumption.
    + eapply HPt; eassumption.
    + eapply All2_upto_trans; eauto.
Qed.

(** ** [upto_domain_ctx]: declarationwise [upto_domain], binder annotations
   ignored (plan.md §3, C-block preamble). *)

Inductive upto_domain_decl : context_decl -> context_decl -> Type :=
| utd_vass na na' t t' :
    upto_domain t t' ->
    upto_domain_decl (vass na t) (vass na' t')
| utd_vdef na na' b b' t t' :
    upto_domain b b' ->
    upto_domain t t' ->
    upto_domain_decl (vdef na b t) (vdef na' b' t').

Derive Signature for upto_domain_decl.

Definition upto_domain_ctx : context -> context -> Type :=
  All2_fold (fun _ _ => upto_domain_decl).

#[global] Instance upto_domain_decl_refl : CRelationClasses.Reflexive upto_domain_decl.
Proof.
  intros [na [b|] t]; constructor; reflexivity.
Qed.

#[global] Instance upto_domain_decl_sym : CRelationClasses.Symmetric upto_domain_decl.
Proof.
  intros d d' e; depelim e; constructor; now symmetry.
Qed.

#[global] Instance upto_domain_decl_trans : CRelationClasses.Transitive upto_domain_decl.
Proof.
  intros d d' d'' e1 e2; depelim e1; depelim e2; constructor; etransitivity; eassumption.
Qed.

#[global] Instance upto_domain_ctx_refl : CRelationClasses.Reflexive upto_domain_ctx.
Proof.
  intros Γ. induction Γ as [|d Γ IH]; constructor; auto. reflexivity.
Qed.

(** ** U2/U4: [eta1]/[eta] closure under lift and subst.

   [eta1_lift] and [eta1_subst_step] are EtaC3C's green proofs
   (fork frac/eta-c3-c, pcuic/theories/PCUICEtaC3C.v), adopted verbatim and
   credited, so there is one proof of each in the lane. The [eta]-level
   congruence toolkit, [subst_eta] and the public [eta_subst] are L2's. *)

(** *** Generic: moving one list element by a reflexive-transitive relation. *)

Lemma clos_refl_trans_OnOne2_hd {A} (R : A -> A -> Type) x y tl :
  clos_refl_trans R x y -> clos_refl_trans (OnOne2 R) (x :: tl) (y :: tl).
Proof.
  induction 1; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eassumption].
Qed.

Lemma clos_refl_trans_OnOne2_tl {A} (R : A -> A -> Type) hd l l' :
  clos_refl_trans (OnOne2 R) l l' -> clos_refl_trans (OnOne2 R) (hd :: l) (hd :: l').
Proof.
  induction 1; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eassumption].
Qed.

Lemma OnOne2_clos_refl_trans {A} (R : A -> A -> Type) l l' :
  OnOne2 (clos_refl_trans R) l l' -> clos_refl_trans (OnOne2 R) l l'.
Proof.
  induction 1.
  - now apply clos_refl_trans_OnOne2_hd.
  - now apply clos_refl_trans_OnOne2_tl.
Qed.

(** A congruence with one [term] hole. *)
Lemma eta_cong1 (F : term -> term)
  (HF : forall a b, eta1 a b -> eta1 (F a) (F b)) {a b} :
  eta a b -> eta (F a) (F b).
Proof.
  induction 1; [apply rt_step; now apply HF|apply rt_refl|eapply rt_trans; eassumption].
Qed.

(** A congruence with a list hole: one [OnOne2 R] step must be one [eta] step. *)
Lemma eta_list_cong {A} (F : list A -> term) (R : A -> A -> Type)
  (HF : forall l l', OnOne2 R l l' -> eta (F l) (F l')) {l l'} :
  All2 (clos_refl_trans R) l l' -> eta (F l) (F l').
Proof.
  intro H. apply All2_many_OnOne2 in H.
  induction H; [apply rt_refl|].
  eapply rt_trans; [eassumption|].
  apply OnOne2_clos_refl_trans in r.
  clear -r HF. induction r; [now apply HF|apply rt_refl|eapply rt_trans; eassumption].
Qed.

(** *** One [eta1] step commutes with [subst] and [lift].
    Proofs adopted verbatim from EtaC3C (fork frac/eta-c3-c, PCUICEtaC3C.v). *)

Local Open Scope nat_scope.

Lemma eta1_subst_step s t t' : eta1 t t' -> forall k, eta1 (subst s k t) (subst s k t').
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
    { replace (S k) with (k + 1) by lia.
      symmetry. apply (permute_lift t n k 1 0). lia. }
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

(** *** [eta]-level closure (reflexive-transitive). *)

Lemma weakening_eta n k u v : eta u v -> eta (lift n k u) (lift n k v).
Proof.
  induction 1; [apply rt_step; now apply eta1_lift|apply rt_refl|eapply rt_trans; eassumption].
Qed.

Lemma eta_subst_term s k a a' : eta a a' -> eta (subst s k a) (subst s k a').
Proof.
  induction 1; [apply rt_step; now apply eta1_subst_step|apply rt_refl|eapply rt_trans; eassumption].
Qed.

(** The locked public single-step form (name agreed with EtaL1b/C3 provers). *)
Lemma eta1_subst s k a a' : eta1 a a' -> eta (subst s k a) (subst s k a').
Proof.
  intro H. apply rt_step. now apply eta1_subst_step.
Qed.

(** ** [eta] congruence toolkit (adopted verbatim from EtaC3C's green
    frac/eta-c3-c, PCUICEtaC3C.v; credited). Single-position closures plus the
    combined binder congruences, used by [subst_eta]. *)

Lemma eta_App_l a a' b : eta a a' -> eta (tApp a b) (tApp a' b).
Proof. apply (eta_cong1 (fun x => tApp x b)). intros; now apply app_eta_l. Qed.
Lemma eta_App_r a b b' : eta b b' -> eta (tApp a b) (tApp a b').
Proof. apply (eta_cong1 (fun x => tApp a x)). intros; now apply app_eta_r. Qed.

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

Lemma eta_Evar_pos ev pre post X Y : eta X Y ->
  eta (tEvar ev (pre ++ X :: post)) (tEvar ev (pre ++ Y :: post)).
Proof.
  induction 1.
  - apply rt_step. apply evar_eta. induction pre; cbn; now constructor.
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

(** Combined congruences (all affected subterms move at once), for [subst_eta]. *)

Lemma eta_Case ci p p' c c' brs brs' :
  All2 eta (pparams p) (pparams p') -> puinst p = puinst p' -> pcontext p = pcontext p' ->
  eta (preturn p) (preturn p') -> eta c c' ->
  All2 (on_Trel_eq eta bbody bcontext) brs brs' ->
  eta (tCase ci p c brs) (tCase ci p' c' brs').
Proof.
  intros Hpars Hu Hctx Hret Hc Hbrs.
  eapply rt_trans; [apply (eta_Case_pars ci p c brs (pparams p')); exact Hpars|].
  eapply rt_trans;
    [apply (eta_Case_preturn ci (set_pparams p (pparams p')) (preturn p') c brs); cbn; exact Hret|].
  eapply rt_trans;
    [apply (eta_Case_discr ci (set_preturn (set_pparams p (pparams p')) (preturn p')) c c' brs); exact Hc|].
  assert (Hp : set_preturn (set_pparams p (pparams p')) (preturn p') = p').
  { destruct p, p'; cbn in *; subst; reflexivity. }
  rewrite Hp. now apply eta_Case_brs.
Qed.

Lemma eta_Prim_array arr arr' :
  arr.(array_level) = arr'.(array_level) ->
  eta arr.(array_default) arr'.(array_default) ->
  eta arr.(array_type) arr'.(array_type) ->
  All2 eta arr.(array_value) arr'.(array_value) ->
  eta (tPrim (primArray; primArrayModel arr)) (tPrim (primArray; primArrayModel arr')).
Proof.
  intros Hl Hd Ht Hv.
  eapply rt_trans with
    (y := tPrim (primArray; primArrayModel (set_array_default arr arr'.(array_default)))).
  { assert (E0 : arr = set_array_default arr (array_default arr)) by (now destruct arr).
    rewrite {1}E0. now apply eta_Array_default. }
  eapply rt_trans with
    (y := tPrim (primArray; primArrayModel
            (set_array_type (set_array_default arr arr'.(array_default)) arr'.(array_type)))).
  { assert (E1 : set_array_default arr arr'.(array_default)
               = set_array_type (set_array_default arr arr'.(array_default)) (array_type arr))
      by (now destruct arr).
    rewrite {1}E1. now apply eta_Array_type. }
  eapply rt_trans with
    (y := tPrim (primArray; primArrayModel
            (set_array_value (set_array_type (set_array_default arr arr'.(array_default)) arr'.(array_type))
                             arr'.(array_value)))).
  { apply eta_Array_val. cbn. exact Hv. }
  assert (Heq : set_array_value
                  (set_array_type (set_array_default arr arr'.(array_default)) arr'.(array_type))
                  arr'.(array_value) = arr').
  { destruct arr, arr'; cbn in *; subst; reflexivity. }
  rewrite Heq. apply rt_refl.
Qed.

(** ** [subst_eta] and the public [eta_subst] (plan U2/U4, locked statements). *)

Lemma subst_eta s s' k b :
  All2 eta s s' -> eta (subst s k b) (subst s' k b).
Proof.
  induction b in s, s', k |- * using term_forall_list_ind; cbn; intro XX.
  all: try solve [apply rt_refl].
  - (* tRel *) destruct (Nat.leb k n) eqn:e; [|apply rt_refl].
    rewrite (All2_length XX).
    destruct (nth_error s (n - k)) eqn:X.
    + eapply All2_nth_error_Some in X as (b'' & X1 & X2); [|exact XX]. rewrite X1.
      now apply weakening_eta.
    + eapply All2_nth_error_None in X as X'; [|exact XX]. now rewrite X'.
  - (* tEvar *) apply eta_Evar. apply All2_map. eapply All_All2; [exact X|].
    intros x IHx. now apply IHx.
  - (* tProd *) apply eta_Prod; eauto.
  - (* tLambda *) apply eta_Lambda; eauto.
  - (* tLetIn *) apply eta_LetIn; eauto.
  - (* tApp *) apply eta_App; eauto.
  - (* tCase *) destruct X as (IHpars & _ & IHret).
    apply eta_Case; cbn.
    + apply All2_map. eapply All_All2; [exact IHpars|]. intros x IHx. now apply IHx.
    + reflexivity.
    + reflexivity.
    + now apply IHret.
    + now apply IHb.
    + apply All2_map. eapply All_All2; [exact X0|].
      intros br [_ IHbody]. split; cbn; [now apply IHbody|reflexivity].
  - (* tProj *) apply eta_Proj; eauto.
  - (* tFix *)
    set (D := #|m| + k). clearbody D.
    eapply rt_trans.
    { apply (eta_Fix_ty n _ (map (map_def (subst s' k) (subst s D)) m)).
      clear -X XX. induction X as [|d m0 p X IH]; cbn; constructor.
      - split; cbn; [now apply (fst p)|reflexivity].
      - exact IH. }
    apply (eta_Fix_body n _ (map (map_def (subst s' k) (subst s' D)) m)).
    clear -X XX. induction X as [|d m0 p X IH]; cbn; constructor.
    + split; cbn; [now apply (snd p)|reflexivity].
    + exact IH.
  - (* tCoFix *)
    set (D := #|m| + k). clearbody D.
    eapply rt_trans.
    { apply (eta_CoFix_ty n _ (map (map_def (subst s' k) (subst s D)) m)).
      clear -X XX. induction X as [|d m0 p X IH]; cbn; constructor.
      - split; cbn; [now apply (fst p)|reflexivity].
      - exact IH. }
    apply (eta_CoFix_body n _ (map (map_def (subst s' k) (subst s' D)) m)).
    clear -X XX. induction X as [|d m0 p X IH]; cbn; constructor.
    + split; cbn; [now apply (snd p)|reflexivity].
    + exact IH.
  - (* tPrim *) destruct p as [? []]; cbn; try apply rt_refl.
    destruct X as (IHty & IHdef & IHval).
    apply eta_Prim_array; cbn.
    + reflexivity.
    + now apply IHdef.
    + now apply IHty.
    + apply All2_map. eapply All_All2; [exact IHval|]. intros z0 IHz. now apply IHz.
Qed.

Lemma eta_subst s s' b b' :
  All2 eta s s' -> eta b b' -> eta (subst0 s b) (subst0 s' b').
Proof.
  intros Hs Hb. eapply rt_trans.
  - eapply eta_subst_term; eassumption.
  - eapply subst_eta; eassumption.
Qed.

(** ** red1_eta_ctx_strong (plan: transport one [red1] step across an
    η-related context; the second C3 dependency after [eta_subst]).

    Statement published and locked with Main, C3Prover3, C3Falsifier, EtaC3C:
    one [red1] step on the η-related context Δ, joined by [eta]. No [wf], no
    scoping premise — the only context-reading case (red_rel) is discharged by
    [weakening_eta]; red_delta reads Σ, not Γ. *)

#[global] Instance eta_Reflexive : CRelationClasses.Reflexive eta.
Proof. intro t. apply rt_refl. Qed.

Definition eta_ctx : context -> context -> Type := All2 (All_decls eta).

Lemma eta_ctx_refl Γ : eta_ctx Γ Γ.
Proof.
  apply All2_refl. intro d. destruct d as [na [b|] ty]; constructor; apply rt_refl.
Qed.

Lemma eta_ctx_app Ξ Γ Δ : eta_ctx Γ Δ -> eta_ctx (Γ ,,, Ξ) (Δ ,,, Ξ).
Proof.
  intro H. apply All2_app; [|exact H].
  apply All2_refl. intro d. destruct d as [na [b|] ty]; constructor; apply rt_refl.
Qed.

Lemma OnOne2_pos {A} {R : A -> A -> Type} pre post a b :
  R a b -> OnOne2 R (pre ++ a :: post) (pre ++ b :: post).
Proof. intro. induction pre; cbn; now constructor. Qed.

Lemma All2_eta_pos pre post a b :
  eta a b -> All2 eta (pre ++ a :: post) (pre ++ b :: post).
Proof.
  intro. apply All2_app; [apply All2_refl; reflexivity|].
  constructor; [assumption|apply All2_refl; reflexivity].
Qed.

Lemma red1_eta_ctx_strong Σ Γ Δ t u :
  red1 Σ Γ t u -> eta_ctx Γ Δ -> ∑ u', red1 Σ Δ t u' × eta u u'.
Proof.
  intros H. revert Δ.
  induction H using red1_ind_all; intros Δ HΔ.
  all: try (eexists; split; [solve [econstructor; eauto]|apply rt_refl]; fail).
  - (* red_rel *)
    destruct (nth_error Γ i) as [decl|] eqn:Hi; [|discriminate].
    assert (Hd' : ∑ decl', nth_error Δ i = Some decl' × All_decls eta decl decl').
    { eapply All2_nth_error_Some; [exact HΔ|exact Hi]. }
    destruct Hd' as (decl' & Hi' & Hd).
    depelim Hd.
    + cbn in H; discriminate.
    + cbn in H. invs H.
      exists (lift0 (S i) b'). split.
      * constructor. rewrite Hi'. reflexivity.
      * now apply weakening_eta.
  - (* abs_red_l *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tLambda na xx N). split; [now apply abs_red_l|now apply eta_Lambda_l].
  - (* abs_red_r *)
    edestruct (IHred1 (Δ ,, vass na N)) as (xx & Hr & He); [now apply (eta_ctx_app [_])|].
    exists (tLambda na N xx). split; [now apply abs_red_r|now apply eta_Lambda_r].
  - (* letin_red_def *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tLetIn na xx t b'). split; [now apply letin_red_def|now apply eta_LetIn_b].
  - (* letin_red_ty *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tLetIn na b xx b'). split; [now apply letin_red_ty|now apply eta_LetIn_t].
  - (* letin_red_body *)
    edestruct (IHred1 (Δ ,, vdef na b t)) as (xx & Hr & He); [now apply (eta_ctx_app [_])|].
    exists (tLetIn na b t xx). split; [now apply letin_red_body|now apply eta_LetIn_c].
  - (* case_red_param *)
    apply OnOne2_split in X as (a & b & pre & post & (ra & IHa) & Hp1 & Hp2).
    edestruct (IHa Δ HΔ) as (a' & Hr & He).
    exists (tCase ci (set_pparams p (pre ++ a' :: post)) c brs). split.
    + apply case_red_param. rewrite Hp1. now apply OnOne2_pos.
    + rewrite Hp2. now apply eta_Case_pars_pos.
  - (* case_red_return *)
    edestruct (IHred1 (Δ ,,, inst_case_predicate_context p)) as (xx & Hr & He);
      [now apply eta_ctx_app|].
    exists (tCase ci (set_preturn p xx) c brs). split.
    + now apply case_red_return.
    + assert (Hrw : set_preturn p xx = set_preturn (set_preturn p preturn') xx) by (now destruct p).
      rewrite Hrw. apply eta_Case_preturn. cbn. exact He.
  - (* case_red_discr *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tCase ind p xx brs). split; [now apply case_red_discr|now apply eta_Case_discr].
  - (* case_red_brs *)
    apply OnOne2_split in X
      as (br0 & br1 & pre & post & ((rb & IHb) & Hbc) & Hb1 & Hb2).
    edestruct (IHb (Δ ,,, inst_case_branch_context p br0)) as (xx & Hr & He);
      [now apply eta_ctx_app|].
    exists (tCase ci p c (pre ++ {| bcontext := bcontext br0; bbody := xx |} :: post)). split.
    + rewrite Hb1. apply case_red_brs. apply OnOne2_pos. split; cbn; [exact Hr|reflexivity].
    + rewrite Hb2.
      destruct br0 as [bc0 bb0], br1 as [bc1 bb1]; cbn in *; subst bc1.
      now apply eta_Case_brs_pos.
  - (* proj_red *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tProj p xx). split; [now apply proj_red|now apply eta_Proj].
  - (* app_red_l *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tApp xx M2). split; [now apply app_red_l|now apply eta_App_l].
  - (* app_red_r *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tApp M1 xx). split; [now apply app_red_r|now apply eta_App_r].
  - (* prod_red_l *)
    edestruct (IHred1 Δ HΔ) as (xx & Hr & He).
    exists (tProd na xx M2). split; [now apply prod_red_l|now apply eta_Prod_l].
  - (* prod_red_r *)
    edestruct (IHred1 (Δ ,, vass na M1)) as (xx & Hr & He); [now apply (eta_ctx_app [_])|].
    exists (tProd na M1 xx). split; [now apply prod_red_r|now apply eta_Prod_r].
  - (* evar *)
    apply OnOne2_split in X as (a & b & pre & post & (ra & IHa) & Hl1 & Hl2).
    edestruct (IHa Δ HΔ) as (a' & Hr & He).
    exists (tEvar ev (pre ++ a' :: post)). split.
    + rewrite Hl1. constructor. now apply OnOne2_pos.
    + rewrite Hl2. now apply eta_Evar_pos.
  - (* fix_red_ty *)
    apply OnOne2_split in X as (d0 & d1 & pre & post & ((rd & IHd) & Hg) & Hm1 & Hm2).
    edestruct (IHd Δ HΔ) as (tt' & Hr & He).
    exists (tFix (pre ++ mkdef term (dname d0) tt' (dbody d0) (rarg d0) :: post) idx). split.
    + rewrite Hm1. apply fix_red_ty. apply OnOne2_pos. split; cbn; [exact Hr|reflexivity].
    + rewrite Hm2. apply eta_Fix_ty.
      apply All2_app; [apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]|].
      constructor; [|apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]].
      split; cbn; [exact He|cbn in Hg; now symmetry].
  - (* fix_red_body *)
    apply OnOne2_split in X as (d0 & d1 & pre & post & ((rd & IHd) & Hg) & Hm1 & Hm2).
    edestruct (IHd (Δ ,,, fix_context mfix0)) as (tt' & Hr & He); [now apply eta_ctx_app|].
    exists (tFix (pre ++ mkdef term (dname d0) (dtype d0) tt' (rarg d0) :: post) idx). split.
    + rewrite Hm1. apply fix_red_body.
      rewrite Hm1 in Hr. apply OnOne2_pos. split; cbn; [exact Hr|reflexivity].
    + rewrite Hm2. apply eta_Fix_body.
      apply All2_app; [apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]|].
      constructor; [|apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]].
      split; cbn; [exact He|cbn in Hg; now symmetry].
  - (* cofix_red_ty *)
    apply OnOne2_split in X as (d0 & d1 & pre & post & ((rd & IHd) & Hg) & Hm1 & Hm2).
    edestruct (IHd Δ HΔ) as (tt' & Hr & He).
    exists (tCoFix (pre ++ mkdef term (dname d0) tt' (dbody d0) (rarg d0) :: post) idx). split.
    + rewrite Hm1. apply cofix_red_ty. apply OnOne2_pos. split; cbn; [exact Hr|reflexivity].
    + rewrite Hm2. apply eta_CoFix_ty.
      apply All2_app; [apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]|].
      constructor; [|apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]].
      split; cbn; [exact He|cbn in Hg; now symmetry].
  - (* cofix_red_body *)
    apply OnOne2_split in X as (d0 & d1 & pre & post & ((rd & IHd) & Hg) & Hm1 & Hm2).
    edestruct (IHd (Δ ,,, fix_context mfix0)) as (tt' & Hr & He); [now apply eta_ctx_app|].
    exists (tCoFix (pre ++ mkdef term (dname d0) (dtype d0) tt' (rarg d0) :: post) idx). split.
    + rewrite Hm1. apply cofix_red_body.
      rewrite Hm1 in Hr. apply OnOne2_pos. split; cbn; [exact Hr|reflexivity].
    + rewrite Hm2. apply eta_CoFix_body.
      apply All2_app; [apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]|].
      constructor; [|apply All2_refl; intro x; split; cbn; [apply rt_refl|reflexivity]].
      split; cbn; [exact He|cbn in Hg; now symmetry].
  - (* array_red_val *)
    apply OnOne2_split in X as (a & b & pre & post & (ra & IHa) & Hl1 & Hl2).
    edestruct (IHa Δ HΔ) as (a' & Hr & He).
    exists (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ a' :: post)))). split.
    + apply array_red_val. rewrite Hl1. now apply OnOne2_pos.
    + rewrite Hl2. now apply eta_Array_val_pos.
  - (* array_red_def *)
    edestruct (IHred1 Δ HΔ) as (dd & Hr & He).
    exists (tPrim (primArray; primArrayModel (set_array_default arr dd))). split.
    + now apply array_red_def.
    + now apply eta_Array_default.
  - (* array_red_type *)
    edestruct (IHred1 Δ HΔ) as (tt' & Hr & He).
    exists (tPrim (primArray; primArrayModel (set_array_type arr tt'))). split.
    + now apply array_red_type.
    + now apply eta_Array_type.
Qed.

(** ** Lift-inversion helpers for red1_strengthening (ported from
    origin/eta_postpo:PCUICBasicStrengthening.v; mkApps_nested -> mkApps_app on 9.2). *)

Lemma lift_Apps_Ind_inv n k M ind u args
      (H : lift n k M = mkApps (tInd ind u) args)
  : ∑ args', M = mkApps (tInd ind u) args' /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. now exists [].
  - rewrite mkApps_app in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite mkApps_app; cbn.
    rewrite map_app. now repeat split.
Qed.

Lemma lift_Apps_Construct_inv n k M ind c u args
      (H : lift n k M = mkApps (tConstruct ind c u) args)
  : ∑ args', M = mkApps (tConstruct ind c u) args' /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. now exists [].
  - rewrite mkApps_app in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite mkApps_app; cbn.
    rewrite map_app. now repeat split.
Qed.

Lemma lift_Apps_Fix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. now eexists _, [].
  - rewrite mkApps_app in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite mkApps_app; cbn.
    rewrite map_app. now repeat split.
Qed.

Lemma lift_Apps_CoFix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tCoFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tCoFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. now eexists _, [].
  - rewrite mkApps_app in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite mkApps_app; cbn.
    rewrite map_app. now repeat split.
Qed.

Lemma lift_unfold_fix n k mfix idx :
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_fix mfix idx).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  f_equal. unfold on_snd; cbn. f_equal.
  rewrite distr_lift_subst. rewrite fix_subst_length. f_equal.
  unfold fix_subst. rewrite !length_map.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

Lemma lift_unfold_cofix n k mfix idx :
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_cofix mfix idx).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  f_equal. unfold on_snd; cbn. f_equal.
  rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !length_map.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

(** [decompose_app] commutes with [lift]. Both this and [lift_is_constructor]
    are COMMENTED OUT in 9.2 (Conversion/PCUICWeakeningConv.v:175-208), so they
    are proved here rather than imported — keeps consumers' build graphs free of
    Conversion/. *)

Lemma decompose_app_rec_lift n k t l :
  let (f, a) := decompose_app_rec t l in
  decompose_app_rec (lift n k t) (map (lift n k) l) = (lift n k f, map (lift n k) a).
Proof.
  induction t in k, l |- *; simpl; auto.
  specialize (IHt1 k (t2 :: l)).
  destruct decompose_app_rec. now rewrite IHt1.
Qed.

Lemma decompose_app_lift n k t f a :
  decompose_app t = (f, a) -> decompose_app (lift n k t) = (lift n k f, map (lift n k) a).
Proof.
  generalize (decompose_app_rec_lift n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  cbn. intros Heq [= <- <-]. exact Heq.
Qed.

Lemma lift_is_constructor args narg n k :
  is_constructor narg args = is_constructor narg (map (lift n k) args).
Proof.
  unfold is_constructor. rewrite nth_error_map.
  destruct nth_error; cbnr.
  unfold isConstruct_app. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->; cbn.
  destruct t0; cbnr.
Qed.
