(* Distributed under the terms of the MIT license. *)

(** * Flipping U1', and C1c on the right-hand term

    [finst_flip]   : u ≈F[cu, pb] v -> v ≈F[cu', pb'] u   (cu ⊆ flip cu')
    [red1_finst_r] : u ≈F[pb,napp] u' -> red1 Σ Γ u' v' ->
                     ∑ v, red1 Σ Γ u v × v ≈F[pb,napp] v'

  A3's transitivity pushes the comparison along steps of both terms. U1' is not
  symmetric at [Cumul], so right-C1c is left-C1c ([red1_finst_l],
  [PCUICEtaFInstC1c]) for the relation with the universe comparison flipped,
  exactly as base derives [red1_eq_term_upto_univ_r] from [_l].

  Base's [cmp_global_instance_flip] and [eq_term_upto_univ_napp_flip]
  ([PCUICEquality]), ported to U1'. The one new point is the instance level: at
  [(pb, napp)] and [(pb', napp)] the F-inst mode is [pb]/[pb'] or [Conv]/[Conv]
  together (both read [head_arity <=? napp]), so base's per-variance flip lemmas
  apply in either case.

  **The hypotheses are satisfiable:** the flip premises by [cu' := flip cu]
  (identity), and the C1c premises by [compare_universe φ] and [compare_sort φ],
  as for [red1_finst_l]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICReduction PCUICUnivSubstitutionConv PCUICEtaFInst PCUICEtaFInstC1c.

(** ** Instance level *)

Lemma finst_inst_flip Σ cu cu' pb pb' gr napp u u' :
  RelationClasses.subrelation (cu Conv) (flip (cu' Conv)) ->
  RelationClasses.subrelation (cu pb) (flip (cu' pb')) ->
  cmp_global_instance_finst Σ cu pb gr napp u u' ->
  cmp_global_instance_finst Σ cu' pb' gr napp u' u.
Proof.
  intros conv_sym pb_sym.
  unfold cmp_global_instance_finst, cmp_global_instance_eta, finst_mode, cmp_opt_variance.
  (* The two modes read the same test, so they are [pb]/[pb'] or [Conv]/[Conv]. *)
  have hm : RelationClasses.subrelation
              (cu (if head_arity Σ gr <=? napp then pb else Conv))
              (flip (cu' (if head_arity Σ gr <=? napp then pb' else Conv)))
    by destruct (_ <=? _).
  destruct global_variance_eta_gen as [| |v] => //.
  2: intros [H|H]; [left|right]; move:H.
  1,2: apply cmp_universe_instance_flip; tas; reflexivity.
  now apply cmp_universe_instance_variance_flip.
Qed.

(** ** Term level *)

Lemma finst_flip Σ cu cu' cs cs' pb pb' napp u v :
  RelationClasses.subrelation (cu Conv) (flip (cu' Conv)) ->
  RelationClasses.subrelation (cu pb) (flip (cu' pb')) ->
  RelationClasses.subrelation (cs Conv) (flip (cs' Conv)) ->
  RelationClasses.subrelation (cs pb) (flip (cs' pb')) ->
  eq_term_upto_univ_eta_napp Σ cu cs pb napp u v ->
  eq_term_upto_univ_eta_napp Σ cu' cs' pb' napp v u.
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb.
  induction u in napp, pb, pb', univ_sub_pb, sort_sub_pb, v |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using cmp_universe_instance_flip; try (symmetry; assumption); fail).
  - inversion 1; subst; constructor.
    eapply All2_sym, All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor. now eapply sort_sub_pb.
  - inversion 1; subst; constructor.
    eapply finst_inst_flip. 3:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply finst_inst_flip. 3:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto.
    solve_all.
    * apply All2_sym; solve_all.
    * eapply cmp_universe_instance_flip; eauto.
    * symmetry. solve_all.
    * apply All2_sym. solve_all. symmetry. solve_all.
  - inversion 1; subst; constructor.
    eapply All2_sym, All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto. now symmetry.
  - inversion 1; subst; constructor.
    eapply All2_sym, All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto. now symmetry.
  - inversion 1; subst; constructor. depelim X1; tas; try now constructor.
    destruct X as (hty & hdef & harr).
    constructor; eauto.
    1: now eapply univ_sub_conv.
    apply All2_sym; solve_all.
Qed.

(** ** Flipped relations keep the C1c premises *)

Lemma substu_flip (cu : Universe.t -> Universe.t -> Prop) {A} `{UnivSubst A} (eqA : A -> A -> Prop) :
  SubstUnivPreserving cu eqA -> SubstUnivPreserving (flip cu) (flip eqA).
Proof.
  intros h u u1 u2 e. unfold flip. apply h.
  unfold cmp_universe_instance in *. now apply Forall2_flip.
Qed.

Section RightC1c.
  Context (Σ' : global_env)
          (cu : conv_pb -> Universe.t -> Universe.t -> Prop)
          (cs : conv_pb -> sort -> sort -> Prop)
          (pre_u : RelationClasses.PreOrder (cu Conv))
          (pre_s : RelationClasses.PreOrder (cs Conv))
          (su_u : SubstUnivPreserving (cu Conv) (cu Conv))
          (su_s : SubstUnivPreserving (cu Conv) (cs Conv)).

  Let fcu := fun pb => flip (cu pb).
  Let fcs := fun pb => flip (cs pb).

  (** **C1c on the right-hand term.** *)
  Theorem red1_finst_r (Σ : global_env) Γ pb napp u u' v' :
    RelationClasses.subrelation (cu Conv) (cu pb) ->
    RelationClasses.subrelation (cs Conv) (cs pb) ->
    eq_term_upto_univ_eta_napp Σ' cu cs pb napp u u' ->
    red1 Σ Γ u' v' ->
    ∑ v, red1 Σ Γ u v × eq_term_upto_univ_eta_napp Σ' cu cs pb napp v v'.
  Proof.
    intros hsu hss e h.
    (* flip, take left-C1c for the flipped relation, flip back *)
    have ef : eq_term_upto_univ_eta_napp Σ' fcu fcs pb napp u' u
      := finst_flip Σ' cu fcu cs fcs pb pb napp u u'
           (fun x y h => h) (fun x y h => h) (fun x y h => h) (fun x y h => h) e.
    destruct (red1_finst_l Σ' fcu fcs
                (RelationClasses.flip_PreOrder _) (RelationClasses.flip_PreOrder _)
                (substu_flip _ _ su_u) (substu_flip _ _ su_s)
                Σ Γ u' v' h pb napp u
                (fun x y h => hsu y x h) (fun x y h => hss y x h) ef) as (v & hv & ev).
    exists v. split; [exact hv|].
    exact (finst_flip Σ' fcu cu fcs cs pb pb napp v' v
             (fun x y h => h) (fun x y h => h) (fun x y h => h) (fun x y h => h) ev).
  Qed.

End RightC1c.
