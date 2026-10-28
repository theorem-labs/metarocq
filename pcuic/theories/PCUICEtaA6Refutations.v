(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, A6: the two refuted restatement forms

  Like [C1b_false]/[C4_false] (PCUICEtaC1b.v): each theorem takes the refuted
  form as a hypothesis, instantiated at the empty environment, and derives
  [False].

  - [A6_D_conv_body_false]: the rev-4 D-row form (i51/i52: λ ≤[pb] λ gives the
    bodies at [Conv]) is false at [pb = Cumul]. Witness
    [λx:Prop. Prop x ≤[Cumul] λx:Prop. Type0 x]: both sides η-reduce, to [Prop]
    and [Type0], which compare at [Cumul]; but [Prop x] and [Type0 x] are
    βη-normal and differ at [Conv].
    RETIRED form; REPLACED BY the body at [pb] ([plan.md] A6 restatements, D rows).
  - [A6_F_raw_false]: the raw F-row form (i9: [tProd … ≤ T] gives [T] reaching a
    [tProd] by [red ∪ eta1]) is false. Witness
    [T := λz:Prop. (tProd nb (λy:z.y) Prop) z], related in E to
    [tProd nb (λ_:S.tRel 0) Prop] by one η step on [canon T], but βη-normal as it
    stands, because [z] occurs in an inner domain.
    RETIRED form; REPLACED BY the canonical form, [(R_c ∪ eta1)* (canon T)]
    reaching the [tProd] ([plan.md] A6 restatements, F rows), and for typed [T] by
    [T8_Prod_r_inv_statement].

  Both witnesses are ill-typed; the refuted lemmas are untyped, as base's are.
  Assumptions: primitive-type axioms only. C4-side (through A1). *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICEtaFInst
     PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaC1b PCUICWellScopedCumulativityEta.

Section Witnesses.

  #[local] Existing Instance default_checker_flags.

  Definition aw_Σ : global_env_ext := (empty_global_env, Monomorphic_ctx).
  Definition aw_A : term := tSort sProp.

  (** *** D-row witness *)

  Definition aw_b1 : term := tApp (tSort sProp) (tRel 0).
  Definition aw_b2 : term := tApp (tSort Sort.type0) (tRel 0).

  Lemma aw_body_normal Σ s v :
    union (R_c Σ ([] ,, vass c1b_na aw_A)) eta1 (tApp (tSort s) (tRel 0)) v -> False.
  Proof.
    intros [[v0 [h ->]]|h].
    - inv_red h.
      + eapply red_normal_Sort; eassumption.
      + eapply red_normal_Rel0; eassumption.
    - inv_eta h.
      + eapply eta_normal_Sort; eassumption.
      + eapply eta_normal_Rel; eassumption.
  Qed.

  Lemma aw_D_premise :
    ws_cumul_pbE FInstFollowKernel Cumul aw_Σ [] (tLambda c1b_na aw_A aw_b1) (tLambda c1b_na aw_A aw_b2).
  Proof.
    constructor; try reflexivity.
    exists (tSort sProp), (tSort Sort.type0). split; [|split].
    - apply rt_step; right. cbn. exact (eta_red canon_la (tSort sProp) canon_dom).
    - apply rt_step; right. cbn. exact (eta_red canon_la (tSort Sort.type0) canon_dom).
    - constructor. cbn. reflexivity.
  Qed.

  (** *** F-row witness *)

  Definition aw_T : term :=
    tLambda c1b_na aw_A (tApp (tProd c1b_na (tLambda c1b_na (tRel 0) (tRel 0)) (tSort sProp)) (tRel 0)).
  Definition aw_P : term := tProd c1b_na (tLambda canon_la canon_dom (tRel 0)) (tSort sProp).

  Lemma lift_1_0_not_domP X : lift 1 0 X = tProd c1b_na (tLambda c1b_na (tRel 0) (tRel 0)) (tSort sProp) -> False.
  Proof.
    intros E. destruct X; cbn in E; try discriminate E.
    injection E as _ e2 _.
    match type of e2 with lift 1 0 ?Y = _ => destruct Y end; cbn in e2; try discriminate e2.
    injection e2 as _ e3 _. exact (lift_1_0_not_Rel0 _ e3).
  Qed.

  Lemma aw_T_red_normal Σ Γ v : red1 Σ Γ aw_T v -> False.
  Proof.
    unfold aw_T, aw_A. intros H. inv_red H.
    - eapply red_normal_Sort; eassumption.
    - inv_red H.
      + inv_red H.
        * inv_red H.
          -- eapply red_normal_Rel0; eassumption.
          -- eapply red_normal_Rel0; eassumption.
        * eapply red_normal_Sort; eassumption.
      + eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma aw_T_eta_normal v : eta1 aw_T v -> False.
  Proof.
    unfold aw_T, aw_A. intros H. inv_eta H.
    - eapply lift_1_0_not_domP; eassumption.
    - eapply eta_normal_Sort; eassumption.
    - inv_eta H.
      + inv_eta H.
        * inv_eta H.
          -- eapply eta_normal_Rel; eassumption.
          -- eapply eta_normal_Rel; eassumption.
        * eapply eta_normal_Sort; eassumption.
      + eapply eta_normal_Rel; eassumption.
  Qed.

  Lemma aw_F_premise : ws_cumul_pbE FInstFollowKernel Conv aw_Σ [] aw_P aw_T.
  Proof.
    constructor; try reflexivity.
    exists aw_P, aw_P. split; [|split].
    - cbn. apply rt_refl.
    - apply rt_step; right. cbn. exact (eta_red canon_la aw_P canon_dom).
    - apply compare_term_eta_refl.
  Qed.

End Witnesses.

(** **RETIRED form 1** (rev-4 D rows, body at [Conv]). *)
Theorem A6_D_conv_body_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) (r : finst_construct_rule)
          pb Γ na1 na2 A1 A2 b1 b2,
     ws_cumul_pbE r pb Σ Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) ->
     ws_cumul_pbE r Conv Σ (Γ ,, vass na1 A1) b1 b2) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags aw_Σ (@wf_empty_global_env default_checker_flags) FInstFollowKernel
              Cumul [] c1b_na c1b_na aw_A aw_A aw_b1 aw_b2 aw_D_premise) as [_ _ _ (v & v' & hv & hv' & e)].
  cbn in hv, hv'.
  apply (rt_from_normal _ _ _ (aw_body_normal _ _)) in hv.
  apply (rt_from_normal _ _ _ (aw_body_normal _ _)) in hv'.
  subst v v'. depelim e. depelim e1. cbn in *. exact c.
Qed.

(** **RETIRED form 2** (raw F rows: [T] reaches a [tProd] by [red ∪ eta1]). *)
Theorem A6_F_raw_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) (r : finst_construct_rule)
          pb Γ na dom codom T,
     ws_cumul_pbE r pb Σ Γ (tProd na dom codom) T ->
     ∑ na' dom' codom', clos_refl_trans (fun x y => (red1 Σ Γ x y + eta1 x y)%type) T (tProd na' dom' codom'))
  -> False.
Proof.
  intros H.
  destruct (H default_checker_flags aw_Σ (@wf_empty_global_env default_checker_flags) FInstFollowKernel
              Conv [] _ _ _ aw_T aw_F_premise) as (na' & dom' & codom' & h).
  apply rt_from_normal in h.
  - unfold aw_T in h. discriminate h.
  - intros v [hr|he]; [exact (aw_T_red_normal _ _ _ hr)|exact (aw_T_eta_normal _ he)].
Qed.
