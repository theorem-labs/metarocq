(* Distributed under the terms of the MIT license. *)

(** * U1' is reflexive, symmetric and transitive at the term level

  A3 ([PCUICEtaI5Trans]) composes comparisons across a confluence join, so it
  needs transitivity of the whole relation, not only of the instance comparison
  ([cmp_global_instance_eta_trans], [PCUICEtaFInst]).

  Base's [eq_term_upto_univ_refl]/[_sym]/[_trans] ([PCUICEquality]), ported to
  [eq_term_upto_univ_eta_napp] with constructor renames only. Base finds the
  instance-level facts by typeclass search; here the U1' instance lemmas are
  registered as [#[local]] instances, so the same automation finds them. Their
  premise lists are base's (at both [Conv] and [pb]), so the term-level premise
  lists below are exactly base's.

  **The hypotheses are satisfiable** by [compare_universe φ] and [compare_sort φ]
  at every [pb] for every [φ]: base's own instances
  ([compare_term_refl]/[_sym]/[_trans] discharge the same lists).

  Parametric in the constructor rule [r]. No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import Program.Equality.
From MetaRocq.Utils Require Import LibHypsNaming.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICEtaFInst.

(** The corrected instance-level lemmas, as instances (premises at [Conv] and
    [pb], exactly base's). *)
#[local] Instance finst_inst_refl r Σ cu pb gr napp :
  RelationClasses.Reflexive (cu Conv) -> RelationClasses.Reflexive (cu pb) ->
  RelationClasses.Reflexive (cmp_global_instance_finst r Σ cu pb gr napp)
  := cmp_global_instance_eta_refl r Σ cu pb gr napp.

#[local] Instance finst_inst_sym r Σ cu pb gr napp :
  RelationClasses.Symmetric (cu Conv) -> RelationClasses.Symmetric (cu pb) ->
  RelationClasses.Symmetric (cmp_global_instance_finst r Σ cu pb gr napp)
  := cmp_global_instance_eta_sym r Σ cu pb gr napp.

#[local] Instance finst_inst_trans r Σ cu pb gr napp :
  RelationClasses.subrelation (cu Conv) (cu pb) ->
  RelationClasses.Transitive (cu Conv) -> RelationClasses.Transitive (cu pb) ->
  RelationClasses.Transitive (cmp_global_instance_finst r Σ cu pb gr napp)
  := cmp_global_instance_eta_trans r Σ cu pb gr napp.

Section FInstEquiv.
  Context (r : finst_construct_rule).

  Polymorphic Lemma eq_term_upto_univ_eta_refl Σ cmp_universe cmp_sort pb napp :
    RelationClasses.Reflexive (cmp_universe Conv) ->
    RelationClasses.Reflexive (cmp_universe pb) ->
    RelationClasses.Reflexive (cmp_sort Conv) ->
    RelationClasses.Reflexive (cmp_sort pb) ->
    Reflexive (eq_term_upto_univ_eta_napp r Σ cmp_universe cmp_sort pb napp).
  Proof.
    intros refl_univ refl_univ' refl_sort refl_sort' t.
    induction t in napp, pb, refl_univ', refl_sort' |- * using term_forall_list_ind.
    all: simpl.
    all: try constructor. all: eauto.
    all: try reflexivity.
    all: try solve [eapply All_All2 ; eauto].
    - unfold eq_predicate. solve_all.
      2,3: reflexivity.
      eapply All_All2; eauto.
    - unfold eq_branches, eq_branch.
      eapply All_All2; eauto.
      intros br [_ ?]; split; eauto. reflexivity.
    - eapply All_All2; eauto; simpl; intuition eauto.
    - eapply All_All2; eauto; simpl; intuition eauto.
    - destruct p as [? []]; constructor; cbn in X; intuition eauto.
      eapply All_All2; eauto.
  Qed.

  Polymorphic Lemma eq_term_upto_univ_eta_sym Σ cmp_universe cmp_sort pb napp :
    RelationClasses.Symmetric (cmp_universe Conv) ->
    RelationClasses.Symmetric (cmp_universe pb) ->
    RelationClasses.Symmetric (cmp_sort Conv) ->
    RelationClasses.Symmetric (cmp_sort pb) ->
    Symmetric (eq_term_upto_univ_eta_napp r Σ cmp_universe cmp_sort pb napp).
  Proof.
    intros sym_univ sym_univ' sym_sort sym_sort' u v e.
    pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
    induction u in napp, pb, sym_univ', sym_sort', v, e |- * using term_forall_list_ind.
    all: dependent destruction e.
    all: try solve [
      econstructor ; eauto ;
      try eapply Forall2_symP ; eauto ; easy
    ].
    - econstructor.
      apply All2_sym. solve_all.
    - solve_all. destruct e as (r' & ? & eq & ?).
      econstructor; rewrite ?e; unfold eq_predicate, eq_branches, eq_branch in *; repeat split; eauto.
      2,3: now symmetry.
      all: eapply All2_sym; solve_all.
      apply All2_symP; solve_all. tc.
    - econstructor. unfold eq_mfixpoint in *.
      apply All2_sym. solve_all.
    - econstructor. unfold eq_mfixpoint in *.
      apply All2_sym. solve_all.
    - econstructor.
      depelim o; cbn in X; constructor; intuition eauto.
      eapply All2_All_mix_left in a0 as h; eauto. cbn in h.
      eapply All2_sym; solve_all.
  Qed.

  Polymorphic Lemma eq_term_upto_univ_eta_trans Σ cmp_universe cmp_sort pb napp :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    RelationClasses.Transitive (cmp_universe Conv) ->
    RelationClasses.Transitive (cmp_universe pb) ->
    RelationClasses.Transitive (cmp_sort Conv) ->
    RelationClasses.Transitive (cmp_sort pb) ->
    Transitive (eq_term_upto_univ_eta_napp r Σ cmp_universe cmp_sort pb napp).
  Proof.
    intros sub_univ trans_univ trans_univ' trans_sort trans_sort' u v w e1 e2.
    pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
    assert (RelationClasses.subrelation (cmp_universe Conv) (cmp_universe Conv)) by reflexivity.
    induction u in napp, pb, sub_univ, trans_univ', trans_sort', v, w, e1, e2 |- * using term_forall_list_ind.
    all: dependent destruction e1.
    all: try solve [ eauto ].
    all: try solve [
      dependent destruction e2 ; econstructor ; eauto ;
      try now etransitivity
    ].
    - dependent destruction e2.
      econstructor.
      eapply All2_All_mix_left in X as h; eauto.
      eapply All2_trans'; tea.
      intros u v w [[IH]]. now eapply IH.
    - dependent destruction e2.
      unfold eq_predicate, eq_branches, eq_branch in *.
      !!solve_all.
      econstructor; unfold eq_predicate, eq_branches, eq_branch in *; solve_all; eauto.
      2: now etransitivity.
      all: eapply All2_trans'; tea; intros ??? [[IH]]; repeat split; eauto.
      * etransitivity; eassumption.
      * destruct p0, p1; etransitivity; eassumption.
      * destruct IH, p0, p1; eauto.
    - dependent destruction e2.
      econstructor. unfold eq_mfixpoint in *.
      eapply All2_All_mix_left in X as h; eauto.
      eapply All2_trans'; tea.
      intros u v w [[[IHt IHb] (?&?&?&?)] (?&?&?&?)]. repeat split; eauto. now etransitivity.
    - dependent destruction e2.
      econstructor. unfold eq_mfixpoint in *.
      eapply All2_All_mix_left in X as h; eauto.
      eapply All2_trans'; tea.
      intros u v w [[[IHt IHb] (?&?&?&?)] (?&?&?&?)]. repeat split; eauto. now etransitivity.
    - dependent destruction e2; constructor.
      depelim o; tas. depelim o0. constructor; destruct X as (hty & hdef & harr); eauto.
      eapply All2_All_mix_left in harr as h; eauto.
      eapply All2_trans'; tea.
      intros ??? [[IH]]; repeat split; eauto.
  Qed.

End FInstEquiv.

(** **Hypotheses satisfiable:** the real comparison meets all three. *)
Lemma compare_term_eta_trans {cf : checker_flags} r Σ φ pb napp :
  Transitive (eq_term_upto_univ_eta_napp r Σ (compare_universe φ) (compare_sort φ) pb napp).
Proof. apply eq_term_upto_univ_eta_trans; tc. Qed.

Lemma compare_term_eta_refl {cf : checker_flags} r Σ φ pb napp :
  Reflexive (eq_term_upto_univ_eta_napp r Σ (compare_universe φ) (compare_sort φ) pb napp).
Proof. apply eq_term_upto_univ_eta_refl; tc. Qed.

Lemma compare_term_eta_sym {cf : checker_flags} r Σ φ napp :
  Symmetric (eq_term_upto_univ_eta_napp r Σ (compare_universe φ) (compare_sort φ) Conv napp).
Proof. apply eq_term_upto_univ_eta_sym; tc. Qed.
