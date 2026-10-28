(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 8 (STAGED AT FollowSpec): the S4 glue

  Glue from U1''s F-inst instance comparison to the BASE instance comparison
  that the spec's [cumulE_Ind]/[cumulE_Construct] read. It comes in two halves,
  matching U1''s mode ([finst_mode], corrected from 5b9cd4ff):
  - **fully applied** ([head_arity <= napp]): F-inst at [pb] IS base at [pb] and
    the same [napp], i.e. [cumul_*_univ Σ pb _ napp], read by [cumulE_*] directly;
  - **under-applied** ([napp < head_arity]): F-inst at [Conv] with the full-arity
    variance IS base at [Conv] and the full arity, i.e. [cumul_*_univ Σ Conv _ n],
    read by S4's [cumulSpecE_*_underapplied]
    ([PCUICCumulativitySpecEtaClosure.v:527], [:609]; frac/eta @ be5ce9b5).

  **Constructor-rule sites** (site K1 in the list sent to the lane lead):
  [finst_construct_glue_full] and [finst_construct_glue_under]. Both are
  parametric in [r] and proved for both values: under [FInstFollowKernel] a
  non-cumulative constructor compares with [AllEqual], which implies every
  variance. After repair (a) their statements are unchanged.
  The [IndRef] halves never read the constructor rule. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICEtaFInst.

Local Open Scope type_scope.

Lemma finst_mode_full Σ gr pb napp : head_arity Σ gr <= napp -> finst_mode Σ gr pb napp = pb.
Proof. intros h. unfold finst_mode. now rewrite (proj2 (Nat.leb_le _ _) h). Qed.

Lemma finst_mode_under Σ gr pb napp : napp < head_arity Σ gr -> finst_mode Σ gr pb napp = Conv.
Proof.
  intros h. unfold finst_mode.
  destruct (Nat.leb_spec (head_arity Σ gr) napp); [lia|reflexivity].
Qed.

(** ** Inductive heads: the rule never reads [IndRef] *)

Lemma global_variance_eta_ind r lookup i napp :
  global_variance_eta_gen r lookup (IndRef i) napp
  = global_variance_gen lookup (IndRef i) (max napp (head_arity_gen lookup (IndRef i))).
Proof. unfold global_variance_eta_gen. now destruct r. Qed.

Lemma finst_ind_glue_full r (Σ : global_env) cu pb i napp u u' :
  head_arity Σ (IndRef i) <= napp ->
  cmp_global_instance_eta r Σ cu pb (IndRef i) napp u u' ->
  cmp_global_instance Σ cu pb (IndRef i) napp u u'.
Proof.
  intros hle h. unfold cmp_global_instance_eta in h.
  rewrite finst_mode_full // global_variance_eta_ind Nat.max_l // in h.
Qed.

Lemma finst_ind_glue_under r (Σ : global_env) cu pb i napp u u' :
  napp < head_arity Σ (IndRef i) ->
  cmp_global_instance_eta r Σ cu pb (IndRef i) napp u u' ->
  cmp_global_instance Σ cu Conv (IndRef i) (head_arity Σ (IndRef i)) u u'.
Proof.
  intros hlt h. unfold cmp_global_instance_eta in h.
  rewrite finst_mode_under // global_variance_eta_ind Nat.max_r in h; [lia|exact h].
Qed.

(** ** Constructor heads — SITE K1, parametric in [r], both values *)

Lemma global_variance_eta_construct_cases r lookup i k napp v :
  global_variance_eta_gen r lookup (ConstructRef i k) napp = v ->
  (v = global_variance_gen lookup (ConstructRef i k)
         (max napp (head_arity_gen lookup (ConstructRef i k)))) + (v = AllEqual).
Proof.
  unfold global_variance_eta_gen. intros <-.
  destruct (match r with FInstFollowSpec => false | _ => _ end); [now right|now left].
Qed.

Lemma finst_construct_glue_full r (Σ : global_env) cu pb i k napp u u' :
  head_arity Σ (ConstructRef i k) <= napp ->
  cmp_global_instance_eta r Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_global_instance Σ cu pb (ConstructRef i k) napp u u'.
Proof.
  intros hle h. unfold cmp_global_instance_eta in h. rewrite finst_mode_full // in h.
  destruct (global_variance_eta_construct_cases r (lookup_env Σ) i k napp _ eq_refl) as [e|e];
    rewrite e in h.
  - rewrite Nat.max_l // in h.
  - exact (cmp_instance_opt_variance cu pb _ u u' h).
Qed.

Lemma finst_construct_glue_under r (Σ : global_env) cu pb i k napp u u' :
  napp < head_arity Σ (ConstructRef i k) ->
  cmp_global_instance_eta r Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_global_instance Σ cu Conv (ConstructRef i k) (head_arity Σ (ConstructRef i k)) u u'.
Proof.
  intros hlt h. unfold cmp_global_instance_eta in h. rewrite finst_mode_under // in h.
  destruct (global_variance_eta_construct_cases r (lookup_env Σ) i k napp _ eq_refl) as [e|e];
    rewrite e in h.
  - rewrite Nat.max_r in h; [lia|exact h].
  - exact (cmp_instance_opt_variance cu Conv _ u u' h).
Qed.

(** ** The reverse glue: base instance comparison ⇒ F-inst — SITE K3

  What the spec's [cumulE_Ind]/[cumulE_Construct] read ([cumul_*_univ Σ pb _ n],
  i.e. base [cmp_global_instance] at [pb] and [napp := n]) implies F-inst at the
  same [(pb, n)]. Fully applied: F-inst IS base (mode [pb], variance at
  [max n arity = n]). Under-applied: base's variance is [AllEqual], i.e. instance
  equality, which implies F-inst's [Conv]-mode comparison at any variance.

  The constructor half is the A2 constructor case. Before repair (a) it was
  FALSE at [FInstFollowKernel] (base gave [AllIrrelevant] to a fully applied
  non-cumulative constructor, F-inst [AllEqual]). After (a) it holds at BOTH
  rules, through [global_variance_eta_base]; A2 uses it at [FInstFollowKernel]. *)

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

Lemma cumul_ind_finst r (Σ : global_env) cu pb i napp u u' :
  cmp_global_instance Σ cu pb (IndRef i) napp u u' ->
  cmp_global_instance_eta r Σ cu pb (IndRef i) napp u u'.
Proof.
  intros h. unfold cmp_global_instance_eta. rewrite global_variance_eta_base.
  destruct (Nat.le_gt_cases (head_arity Σ (IndRef i)) napp) as [hle|hlt].
  - rewrite (finst_mode_full Σ (IndRef i) pb napp hle) (Nat.max_l _ _ hle). exact h.
  - rewrite (finst_mode_under Σ (IndRef i) pb napp hlt).
    apply cmp_instance_opt_variance.
    exact (cmp_global_instance_ind_under Σ cu pb i napp u u' hlt h).
Qed.

(** **SITE K3.** *)
Lemma cumul_construct_finst r (Σ : global_env) cu pb i k napp u u' :
  cmp_global_instance Σ cu pb (ConstructRef i k) napp u u' ->
  cmp_global_instance_eta r Σ cu pb (ConstructRef i k) napp u u'.
Proof.
  intros h. unfold cmp_global_instance_eta. rewrite global_variance_eta_base.
  destruct (Nat.le_gt_cases (head_arity Σ (ConstructRef i k)) napp) as [hle|hlt].
  - rewrite (finst_mode_full Σ (ConstructRef i k) pb napp hle) (Nat.max_l _ _ hle). exact h.
  - rewrite (finst_mode_under Σ (ConstructRef i k) pb napp hlt).
    apply cmp_instance_opt_variance.
    exact (cmp_global_instance_construct_under Σ cu pb i k napp u u' hlt h).
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
