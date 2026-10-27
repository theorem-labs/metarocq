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
