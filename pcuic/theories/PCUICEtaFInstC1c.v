(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 8 (STAGED AT FollowSpec), A3 piece:
      C1c for U1' — a [red1] step commutes with the F-inst comparison

    [red1_finst_l] : u ≈F[pb,napp] u' -> red1 Σ Γ u v ->
                     ∑ v', red1 Σ Γ u' v' × v ≈F[pb,napp] v'

  The strong one-step form, exactly as base's [red1_eq_term_upto_univ_l]
  ([PCUICConfluence.v:809]).

  **Route, and why it is small.** At [Conv], U1' IS base's relation over
  [eta_env] ([finst_Conv_base]). So:
  - **pure spines** — a term whose application spine is NOT headed by [tSort],
    [tInd], [tConstruct] or [tProd]. There the comparison does not depend on [pb]
    ([finst_pure_Conv]), so C1c is base's C1c at [Conv], transported, then lifted
    back to [(pb, napp)] by term-level monotonicity ([finst_term_Conv_pb]).
    Every [red1] case whose source has a pure spine goes this way, including
    every root redex (β, ζ, rel, ι, fix, cofix-case, cofix-proj, δ, proj).
  - **the four spine congruences** — [app_red_l] (induction hypothesis at
    [(pb, S napp)]), [app_red_r] and [prod_red_l] (a [Conv] position: base's C1c,
    transported), [prod_red_r] (induction hypothesis at [(pb, 0)], then the
    assumption-only context change of [context_pres_let_bodies_red1],
    [PCUICRedTypeIrrelevance.v:94]).

  [finst_term_Conv_pb] is also the term-level [(Conv, n) → (pb, m)] monotonicity
  that obligation 9's Case (A) uses for the η drop.

  **Hypotheses satisfiable (FRAC's rule):** yes — all are met by
  [compare_universe φ] and [compare_sort φ] for every [φ]: the preorders and
  subrelations by base's instances, the [SubstUnivPreserving] ones by base's
  instances used for [compare_term] (they are [red1_eq_term_upto_univ_l]'s own
  premises at [Conv]). The comparison premise: any F-inst-related pair, e.g. a
  term with itself.

  **C4-side**: it Requires base [PCUICConfluence] for [red1_eq_term_upto_univ_l].
  No C3-side file may Require it. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICReduction PCUICTyping PCUICUnivSubstitutionConv PCUICConfluence
     PCUICRedTypeIrrelevance PCUICEtaFInst PCUICEtaFInstTransport.

(** ** Pure spines *)

Fixpoint finst_pure (t : term) : bool :=
  match t with
  | tApp f _ => finst_pure f
  | tSort _ | tInd _ _ | tConstruct _ _ _ | tProd _ _ _ => false
  | _ => true
  end.

Lemma finst_pure_mkApps f args : finst_pure (mkApps f args) = finst_pure f.
Proof. induction args in f |- *; cbn; [reflexivity|]. now rewrite IHargs. Qed.

Section C1c.

  Context (r : finst_construct_rule) (Σ' : global_env)
          (cu : conv_pb -> Universe.t -> Universe.t -> Prop)
          (cs : conv_pb -> sort -> sort -> Prop).

  Local Notation RF pb n := (eq_term_upto_univ_eta_napp r Σ' cu cs pb n).

  (** **Term-level [(Conv, n) → (pb, m)] monotonicity.** Recursive positions other
      than [App]-left and [Prod]-codomain are at [(Conv, 0)] and stay there. *)
  Lemma finst_term_Conv_pb pb0 n t u :
    RF pb0 n t u -> pb0 = Conv ->
    forall pb m, RelationClasses.subrelation (cu Conv) (cu pb) ->
                 RelationClasses.subrelation (cs Conv) (cs pb) ->
    RF pb m t u.
  Proof.
    induction 1; intros hpb pb' m hsu hss; subst.
    all: first
      [ solve [constructor; eauto]
      | solve [constructor; now apply hss]
      | solve [constructor; eapply finst_Conv_pb; eauto]
      | solve [constructor; assumption] ].
  Qed.

  (** On a pure spine the comparison does not depend on [pb]. *)
  Lemma finst_pure_Conv pb n t u : RF pb n t u -> finst_pure t = true -> RF Conv n t u.
  Proof.
    induction 1; cbn; intros hp; try discriminate.
    all: first [ solve [constructor; eauto] | solve [constructor; assumption] ].
  Qed.

  Context (pre_u : RelationClasses.PreOrder (cu Conv))
          (pre_s : RelationClasses.PreOrder (cs Conv))
          (su_u : SubstUnivPreserving (cu Conv) (cu Conv))
          (su_s : SubstUnivPreserving (cu Conv) (cs Conv)).

  (** C1c at [Conv]: base's, transported. *)
  Lemma red1_finst_Conv (Σ : global_env) Γ napp u v u' :
    RF Conv napp u u' -> red1 Σ Γ u v -> ∑ v', red1 Σ Γ u' v' × RF Conv napp v v'.
  Proof.
    intros e h. apply finst_Conv_to_base in e.
    destruct (@red1_eq_term_upto_univ_l Σ (eta_env r Σ') cu cs Conv napp Γ u v u'
                pre_u pre_u pre_s pre_s (fun x y h => h) (fun x y h => h) su_u su_s su_s e h)
      as (v' & hr & ev).
    exists v'. split; [exact hr|]. now apply finst_Conv_of_base.
  Qed.

  Context (pb : conv_pb)
          (sub_u : RelationClasses.subrelation (cu Conv) (cu pb))
          (sub_s : RelationClasses.subrelation (cs Conv) (cs pb)).

  (** C1c for a pure spine, at any [(pb, napp)]. *)
  Lemma red1_finst_pure (Σ : global_env) Γ napp u v u' :
    finst_pure u = true -> RF pb napp u u' -> red1 Σ Γ u v ->
    ∑ v', red1 Σ Γ u' v' × RF pb napp v v'.
  Proof.
    intros hp e h.
    destruct (red1_finst_Conv Σ Γ napp u v u' (finst_pure_Conv _ _ _ _ e hp) h) as (v' & hr & ev).
    exists v'. split; [exact hr|]. exact (finst_term_Conv_pb _ _ _ _ ev eq_refl pb napp sub_u sub_s).
  Qed.

End C1c.

(** ** C1c for U1', at any [(pb, napp)] *)

Section C1cMain.

  Context (r : finst_construct_rule) (Σ' : global_env)
          (cu : conv_pb -> Universe.t -> Universe.t -> Prop)
          (cs : conv_pb -> sort -> sort -> Prop)
          (pre_u : RelationClasses.PreOrder (cu Conv))
          (pre_s : RelationClasses.PreOrder (cs Conv))
          (su_u : SubstUnivPreserving (cu Conv) (cu Conv))
          (su_s : SubstUnivPreserving (cu Conv) (cs Conv)).

  Local Notation RF pb n := (eq_term_upto_univ_eta_napp r Σ' cu cs pb n).

  Theorem red1_finst_l (Σ : global_env) Γ u v :
    red1 Σ Γ u v ->
    forall pb napp u',
      RelationClasses.subrelation (cu Conv) (cu pb) ->
      RelationClasses.subrelation (cs Conv) (cs pb) ->
      RF pb napp u u' -> ∑ v', red1 Σ Γ u' v' × RF pb napp v v'.
  Proof.
    intros h. pose proof h as h0. revert h0.
    induction h using red1_ind_all; intros h0 pb napp u' hsu hss e.
    (* Every case whose source has a pure spine: the generic route. The purity goal
       holds the evar [?u] until [e]/[h0] fix it, so it is discharged LAST. *)
    all: try solve [ eapply (red1_finst_pure r Σ' cu cs pre_u pre_s su_u su_s pb hsu hss Σ);
                     [ idtac | exact e | exact h0 ];
                     rewrite ?finst_pure_mkApps; reflexivity ].
    (* The four spine congruences remain, in red1_ind_all's order. Hypotheses are
       selected by TYPE: red1_ind_all's binder names are not stable. *)
    - (* app_red_l: induction hypothesis at (pb, S napp) *)
      depelim e.
      (* [depelim] may rename the non-uniform [napp]; match only on the shared ?A. *)
      match goal with
      | IH : red1 _ _ ?A ?B -> _, hA : red1 _ _ ?A ?B,
        hl : eq_term_upto_univ_eta_napp _ _ _ _ _ _ ?A _ |- _ =>
          edestruct (IH hA _ _ _ ltac:(eassumption) ltac:(eassumption) hl) as (v1 & hv1 & ev1)
      end.
      eexists. split; [apply app_red_l; exact hv1|constructor; [exact ev1|assumption]].
    - (* app_red_r: a Conv position *)
      depelim e.
      match goal with
      | hA : red1 _ _ ?A ?B, hr : eq_term_upto_univ_eta_napp _ _ _ _ Conv 0 ?A ?A' |- _ =>
          destruct (red1_finst_Conv r Σ' cu cs pre_u pre_s su_u su_s Σ _ 0 A B A' hr hA)
            as (v2 & hv2 & ev2)
      end.
      eexists. split; [apply app_red_r; exact hv2|constructor; [assumption|exact ev2]].
    - (* prod_red_l: the domain is a Conv position *)
      depelim e.
      match goal with
      | hA : red1 _ _ ?A ?B, ha : eq_term_upto_univ_eta_napp _ _ _ _ Conv 0 ?A ?A' |- _ =>
          destruct (red1_finst_Conv r Σ' cu cs pre_u pre_s su_u su_s Σ _ 0 A B A' ha hA)
            as (v1 & hv1 & ev1)
      end.
      eexists. split; [apply prod_red_l; exact hv1|constructor; [assumption|exact ev1|assumption]].
    - (* prod_red_r: induction hypothesis at (pb, 0), then the context change *)
      depelim e.
      match goal with
      | IH : red1 _ _ ?A ?B -> _, hA : red1 _ _ ?A ?B,
        hb : eq_term_upto_univ_eta_napp _ _ _ _ _ _ ?A _ |- _ =>
          edestruct (IH hA _ _ _ ltac:(eassumption) ltac:(eassumption) hb) as (v2 & hv2 & ev2)
      end.
      (* The red1 slot first: it fixes the reduct evar before [constructor] runs. *)
      eexists. split.
      + apply prod_red_r.
        eapply context_pres_let_bodies_red1; [|exact hv2].
        constructor; [apply All2_fold_refl; intros ? [na0 [b0|] ty0]; cbn; [reflexivity|exact tt]|exact tt].
      + constructor; [assumption|assumption|exact ev2].
  Qed.

End C1cMain.
