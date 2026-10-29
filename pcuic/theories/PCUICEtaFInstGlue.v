(* Distributed under the terms of the MIT license. *)

(** * From U1''s instance comparison to the base one

  Glue from U1''s F-inst instance comparison to the base instance comparison that
  the specification's [cumulE_Ind]/[cumulE_Construct] read. It comes in two
  halves, matching U1''s mode ([finst_mode], [PCUICEtaFInst]):
  - **fully applied** ([head_arity <= napp]): F-inst at [pb] is base at [pb] and
    the same [napp], i.e. [cumul_*_univ Σ pb _ napp], read by [cumulE_*] directly;
  - **under-applied** ([napp < head_arity]): F-inst at [Conv] with the full-arity
    variance is base at [Conv] and the full arity, i.e. [cumul_*_univ Σ Conv _ n],
    read by [cumulSpecE_*_underapplied] ([PCUICCumulativitySpecEtaClosure]).

  F-inst's variance is base's at the head's full arity ([global_variance_eta_gen]),
  so both halves are base's lemmas at that arity. A non-cumulative constructor
  gets [AllEqual] there, as base gives it.

  The reverse direction, base ⇒ F-inst, holds at every [(pb, napp)]: for the instance
  comparison ([cumul_ind_finst], [cumul_construct_finst]) and for the whole term comparison
  ([eq_term_upto_univ_napp_finst]). *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICEquality PCUICEtaFInst.
From Equations.Prop Require Import DepElim.

Local Open Scope type_scope.

Lemma finst_mode_full Σ gr pb napp : head_arity Σ gr <= napp -> finst_mode Σ gr pb napp = pb.
Proof. intros h. unfold finst_mode. now rewrite (proj2 (Nat.leb_le _ _) h). Qed.

Lemma finst_mode_under Σ gr pb napp : napp < head_arity Σ gr -> finst_mode Σ gr pb napp = Conv.
Proof.
  intros h. unfold finst_mode.
  destruct (Nat.leb_spec (head_arity Σ gr) napp); [lia|reflexivity].
Qed.

(** ** Inductive heads *)

Lemma finst_ind_glue_full (Σ : global_env) cu pb i napp u u' :
  head_arity Σ (IndRef i) <= napp ->
  cmp_global_instance_eta Σ cu pb (IndRef i) napp u u' ->
  cmp_global_instance Σ cu pb (IndRef i) napp u u'.
Proof.
  intros hle h. unfold cmp_global_instance_eta, global_variance_eta_gen in h.
  rewrite finst_mode_full // Nat.max_l // in h.
Qed.

Lemma finst_ind_glue_under (Σ : global_env) cu pb i napp u u' :
  napp < head_arity Σ (IndRef i) ->
  cmp_global_instance_eta Σ cu pb (IndRef i) napp u u' ->
  cmp_global_instance Σ cu Conv (IndRef i) (head_arity Σ (IndRef i)) u u'.
Proof.
  intros hlt h. unfold cmp_global_instance_eta, global_variance_eta_gen in h.
  rewrite finst_mode_under // Nat.max_r in h; [lia|exact h].
Qed.

(** ** Constructor heads — SITE K1 *)

Lemma finst_construct_glue_full (Σ : global_env) cu pb i k napp u u' :
  head_arity Σ (ConstructRef i k) <= napp ->
  cmp_global_instance_eta Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_global_instance Σ cu pb (ConstructRef i k) napp u u'.
Proof.
  intros hle h. unfold cmp_global_instance_eta, global_variance_eta_gen in h.
  rewrite finst_mode_full // Nat.max_l // in h.
Qed.

Lemma finst_construct_glue_under (Σ : global_env) cu pb i k napp u u' :
  napp < head_arity Σ (ConstructRef i k) ->
  cmp_global_instance_eta Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_global_instance Σ cu Conv (ConstructRef i k) (head_arity Σ (ConstructRef i k)) u u'.
Proof.
  intros hlt h. unfold cmp_global_instance_eta, global_variance_eta_gen in h.
  rewrite finst_mode_under // Nat.max_r in h; [lia|exact h].
Qed.

(** ** The reverse glue: base instance comparison ⇒ F-inst — SITE K3

  What the spec's [cumulE_Ind]/[cumulE_Construct] read ([cumul_*_univ Σ pb _ n],
  i.e. base [cmp_global_instance] at [pb] and [napp := n]) implies F-inst at the
  same [(pb, n)]. Fully applied: F-inst IS base (mode [pb], variance at
  [max n arity = n]). Under-applied: base's variance is [AllEqual], i.e. instance
  equality, which implies F-inst's [Conv]-mode comparison at any variance.

  The constructor half is the A2 constructor case. Before repair (a) it was
  FALSE for a non-cumulative constructor (base gave [AllIrrelevant] to a fully
  applied one, F-inst [AllEqual]). After (a) base gives [AllEqual] there too. *)

Lemma cmp_global_instance_ind_under (Σ : global_env) cu pb i napp u u' :
  napp < head_arity Σ (IndRef i) ->
  cmp_global_instance Σ cu pb (IndRef i) napp u u' ->
  cmp_universe_instance (cu Conv) u u'.
Proof.
  unfold cmp_global_instance, global_variance_gen, head_arity_gen.
  destruct (lookup_inductive_gen (lookup_env Σ) i) as [[mdecl idecl]|]; [|intros; lia].
  intros hlt. destruct (Nat.leb_spec (context_assumptions (ind_params mdecl ,,, ind_indices idecl)) napp);
    [lia|]. intros h; exact h.
Qed.

Lemma cmp_global_instance_construct_under (Σ : global_env) cu pb i k napp u u' :
  napp < head_arity Σ (ConstructRef i k) ->
  cmp_global_instance Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_universe_instance (cu Conv) u u'.
Proof.
  unfold cmp_global_instance, global_variance_gen, head_arity_gen.
  destruct (lookup_constructor_gen (lookup_env Σ) i k) as [[[mdecl idecl] cdecl]|]; [|intros; lia].
  intros hlt. destruct (Nat.leb_spec (cstr_arity cdecl + ind_npars mdecl) napp); [lia|].
  intros h; exact h.
Qed.

Lemma cumul_ind_finst (Σ : global_env) cu pb i napp u u' :
  cmp_global_instance Σ cu pb (IndRef i) napp u u' ->
  cmp_global_instance_eta Σ cu pb (IndRef i) napp u u'.
Proof.
  intros h. unfold cmp_global_instance_eta, global_variance_eta_gen.
  destruct (Nat.le_gt_cases (head_arity Σ (IndRef i)) napp) as [hle|hlt].
  - rewrite (finst_mode_full Σ (IndRef i) pb napp hle) (Nat.max_l _ _ hle). exact h.
  - rewrite (finst_mode_under Σ (IndRef i) pb napp hlt).
    apply cmp_instance_opt_variance.
    exact (cmp_global_instance_ind_under Σ cu pb i napp u u' hlt h).
Qed.

(** **SITE K3.** *)
Lemma cumul_construct_finst (Σ : global_env) cu pb i k napp u u' :
  cmp_global_instance Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_global_instance_eta Σ cu pb (ConstructRef i k) napp u u'.
Proof.
  intros h. unfold cmp_global_instance_eta, global_variance_eta_gen.
  destruct (Nat.le_gt_cases (head_arity Σ (ConstructRef i k)) napp) as [hle|hlt].
  - rewrite (finst_mode_full Σ (ConstructRef i k) pb napp hle) (Nat.max_l _ _ hle). exact h.
  - rewrite (finst_mode_under Σ (ConstructRef i k) pb napp hlt).
    apply cmp_instance_opt_variance.
    exact (cmp_global_instance_construct_under Σ cu pb i k napp u u' hlt h).
Qed.

(** ** The term-level reverse glue: base comparison ⇒ U1'

  Base [eq_term_upto_univ_napp] at [(pb, napp)] implies U1' ([eq_term_upto_univ_eta_napp]) at the
  same [(pb, napp)], for any universe and sort comparisons. The two relations differ only at
  [eq_Ind]/[eq_Construct], where [cumul_ind_finst]/[cumul_construct_finst] carry base's instance
  comparison over; every other constructor is base's. The proof is base's
  [eq_term_upto_univ_impl] with those two cases replaced. *)
Lemma eq_term_upto_univ_napp_finst (Σ : global_env) cu cs pb napp t u :
  eq_term_upto_univ_napp Σ cu cs pb napp t u ->
  eq_term_upto_univ_eta_napp Σ cu cs pb napp t u.
Proof.
  induction t in pb, napp, u |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor; eauto; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor. now apply cumul_ind_finst.
  - inversion 1; subst; constructor. now apply cumul_construct_finst.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - intros h; depelim h. depelim o; constructor; cbn in X; constructor; intuition eauto.
    solve_all.
Qed.

(** ** Arity bridges: [head_arity] is the count S4's lemmas state *)

Lemma head_arity_ind (Σ : global_env) i mdecl idecl :
  declared_inductive_gen (lookup_env Σ) i mdecl idecl ->
  head_arity Σ (IndRef i) = context_assumptions (ind_params mdecl ,,, ind_indices idecl).
Proof. intros h. unfold head_arity_gen. now rewrite (declared_inductive_lookup_gen h). Qed.

Lemma head_arity_construct (Σ : global_env) i k mdecl idecl cdecl :
  declared_constructor_gen (lookup_env Σ) (i, k) mdecl idecl cdecl ->
  head_arity Σ (ConstructRef i k) = (cstr_arity cdecl + ind_npars mdecl)%nat.
Proof.
  intros h. unfold head_arity_gen.
  now rewrite (declared_constructor_lookup_gen (id := (i, k)) h).
Qed.
