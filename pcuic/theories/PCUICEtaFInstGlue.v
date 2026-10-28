(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 8 (STAGED AT FollowSpec): the S4 glue

  Glue between U1''s F-inst instance comparison and the BASE instance comparison
  that the spec's [cumulE_Ind]/[cumulE_Construct] read, at the head's full arity.
  With it, A4's under-applied case is S4's [cumulSpecE_*_underapplied]
  ([PCUICCumulativitySpecEtaClosure], frac/eta @ be5ce9b5).

  **Why it is almost definitional.** U1''s variance lookup IS base
  [global_variance_gen] at [max napp arity] ([global_variance_eta_gen]), except
  that under [FInstFollowKernel] a non-cumulative constructor compares with
  [AllEqual]. [AllEqual] implies every other variance
  ([cmp_instance_opt_variance], [PCUICEquality.v:102-109]), so the glue holds at
  BOTH rules.

  **Constructor-rule sites in this file** (plan.md §6.2 lists all of them):
  - [finst_construct_glue] = site K1. Stated parametric in [r] and proved for
    both values. After repair (a) lands in base [global_variance_gen], its
    statement is unchanged; its proof needs one more [destruct] on [ind_variance].
  [finst_ind_glue] and the arity bridges never read the constructor rule.

  Dependencies: [PCUICEtaFInst] and base syntax/equality. No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICEtaFInst.

Local Open Scope type_scope.

(** ** Inductive heads: uniform, the rule never reads [IndRef] *)

Lemma finst_ind_glue r (Σ : global_env) cu i napp u u' :
  cmp_global_instance_eta r Σ cu (IndRef i) napp u u' ->
  cmp_global_instance Σ cu Conv (IndRef i) (max napp (head_arity Σ (IndRef i))) u u'.
Proof. destruct r; intros h; exact h. Qed.

(** ** Constructor heads — SITE K1, parametric in [r], proved for both values *)

Lemma finst_construct_glue r (Σ : global_env) cu i k napp u u' :
  cmp_global_instance_eta r Σ cu (ConstructRef i k) napp u u' ->
  cmp_global_instance Σ cu Conv (ConstructRef i k)
    (max napp (head_arity Σ (ConstructRef i k))) u u'.
Proof.
  destruct r; intros h; [exact h|].
  unfold cmp_global_instance_eta, global_variance_eta_gen in h.
  destruct (noncumulative_constructor_gen (lookup_env Σ) (ConstructRef i k)); [|exact h].
  (* FollowKernel, non-cumulative: [AllEqual], which implies every variance *)
  exact (cmp_instance_opt_variance cu Conv _ u u' h).
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
