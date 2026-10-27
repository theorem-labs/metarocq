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
     PCUICEquality PCUICEtaDefs.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.

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
