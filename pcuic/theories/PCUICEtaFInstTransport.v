(* Distributed under the terms of the MIT license. *)

(** * At [Conv], U1' is base's relation over a transformed environment

    [finst_Conv_base] : eq_term_upto_univ_eta_napp Σ cu cs Conv napp t u
                        <~> eq_term_upto_univ_napp (eta_env Σ) cu cs Conv napp t u

  **Why this exists.** A3 needs C1c (a [red1] step commutes with the comparison)
  for U1'. Base proves C1c for its own relation ([red1_eq_term_upto_univ_l],
  [PCUICConfluence]), some 630 lines on top of many relation lemmas. At [Conv],
  U1''s mode is always [Conv], so the only difference from base is the variance
  lookup: U1' reads the full-arity variance. [eta_env] is an environment in which
  base's lookup already returns exactly that, so at [Conv] the two relations
  coincide and base's whole [Conv]-level library transports. Only the [pb]-spine
  ([App]-left chains and [Prod] codomains at [Cumul]) is not covered, and is
  handled separately ([PCUICEtaFInstC1c]).

  **[eta_env Σ]** is [Σ] with every inductive's parameters and indices emptied
  ([ind_params], [ind_npars], [ind_indices]) and every constructor's [cstr_arity]
  set to 0, so base's [arity <=? napp] test always passes; and the constructors
  of non-cumulative blocks removed, so their lookup fails and base returns
  [AllEqual], which is the kernel rule F-inst follows there. It is a comparison
  device only: nothing types or reduces in it.

  **The iff has no hypotheses.** No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICEtaFInst.

(** ** The transformed environment *)

Definition eta_cstr (c : constructor_body) : constructor_body :=
  {| cstr_name := cstr_name c; cstr_args := cstr_args c; cstr_indices := cstr_indices c;
     cstr_type := cstr_type c; cstr_arity := 0 |}.

Definition eta_idecl (drop : bool) (i : one_inductive_body) : one_inductive_body :=
  {| ind_name := ind_name i; ind_indices := []; ind_sort := ind_sort i; ind_type := ind_type i;
     ind_kelim := ind_kelim i;
     ind_ctors := if drop then [] else map eta_cstr (ind_ctors i);
     ind_projs := ind_projs i; ind_relevance := ind_relevance i |}.

(** Drop the constructors of a non-cumulative block: there F-inst follows the
    kernel's rule and compares by instance equality. *)
Definition eta_drop (m : mutual_inductive_body) : bool :=
  match ind_variance m with None => true | Some _ => false end.

Definition eta_mdecl (m : mutual_inductive_body) : mutual_inductive_body :=
  {| ind_finite := ind_finite m; ind_npars := 0; ind_params := [];
     ind_bodies := map (eta_idecl (eta_drop m)) (ind_bodies m);
     ind_universes := ind_universes m; ind_variance := ind_variance m |}.

Definition eta_gdecl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl c => ConstantDecl c
  | InductiveDecl m => InductiveDecl (eta_mdecl m)
  end.

Definition eta_env (Σ : global_env) : global_env :=
  {| universes := universes Σ;
     declarations := map (fun d => (d.1, eta_gdecl d.2)) (declarations Σ);
     retroknowledge := retroknowledge Σ |}.

Lemma lookup_eta_env Σ kn :
  lookup_env (eta_env Σ) kn = option_map eta_gdecl (lookup_env Σ kn).
Proof.
  unfold lookup_env, eta_env; cbn. induction (declarations Σ) as [|[kn' d] tl IH]; cbn; [reflexivity|].
  destruct (kn == kn'); [reflexivity|exact IH].
Qed.

(** ** Base's lookup in [eta_env] returns U1''s variance *)

Lemma variance_eta_env Σ gr napp :
  global_variance_gen (lookup_env (eta_env Σ)) gr napp
  = global_variance_eta_gen (lookup_env Σ) gr napp.
Proof.
  unfold global_variance_eta_gen, global_variance_gen, head_arity_gen,
    lookup_constructor_gen, lookup_inductive_gen, lookup_minductive_gen.
  (* Keep [lookup_env] folded ([cbn -[lookup_env]]) until [lookup_eta_env] is used. *)
  destruct gr as [id|kn|ind|ind k]; cbn -[lookup_env]; try reflexivity.
  - (* IndRef *)
    rewrite lookup_eta_env.
    destruct (lookup_env Σ (inductive_mind ind)) as [[c|m]|]; cbn; try reflexivity.
    rewrite nth_error_map.
    destruct (nth_error (ind_bodies m) (inductive_ind ind)) as [idecl|]; cbn;
      [|reflexivity].
    (* [0 <=? napp] already computes to [true]; only the [max] test remains. *)
    rewrite (proj2 (Nat.leb_le _ (max napp _)) (Nat.le_max_r _ _)).
    reflexivity.
  - (* ConstructRef *)
    rewrite lookup_eta_env.
    destruct (lookup_env Σ (inductive_mind ind)) as [[c|m]|]; cbn; try reflexivity.
    rewrite nth_error_map.
    destruct (nth_error (ind_bodies m) (inductive_ind ind)) as [idecl|]; cbn;
      [|reflexivity].
    unfold eta_drop.
    (* Non-cumulative blocks lose their constructors, so base's lookup fails and
       returns [AllEqual]; cumulative ones keep them with arity zeroed. *)
    destruct (ind_variance m) as [var|] eqn:hv; cbn.
    + rewrite nth_error_map.
      destruct (nth_error (ind_ctors idecl) k) as [cdecl|]; cbn; [|reflexivity].
      rewrite (proj2 (Nat.leb_le _ (max napp _)) (Nat.le_max_r _ _)) hv.
      reflexivity.
    + rewrite nth_error_nil.
      destruct (nth_error (ind_ctors idecl) k) as [cdecl|]; cbn; rewrite ?hv;
        first [reflexivity | now destruct (_ <=? _)].
Qed.

(** At [Conv], the F-inst instance comparison IS base's in [eta_env]. *)
Lemma finst_Conv_inst_iff Σ cu gr napp u u' :
  cmp_global_instance_finst Σ cu Conv gr napp u u'
  <-> cmp_global_instance (eta_env Σ) cu Conv gr napp u u'.
Proof.
  unfold cmp_global_instance_finst, cmp_global_instance_eta, cmp_global_instance_gen.
  have -> : finst_mode Σ gr Conv napp = Conv by unfold finst_mode; now destruct (_ <=? _).
  now rewrite variance_eta_env.
Qed.

(** ** The transport *)

Section Transport.
  Context (Σ : global_env)
          (cu : conv_pb -> Universe.t -> Universe.t -> Prop)
          (cs : conv_pb -> sort -> sort -> Prop).

  Lemma finst_Conv_to_base napp t u :
    eq_term_upto_univ_eta_napp Σ cu cs Conv napp t u ->
    eq_term_upto_univ_napp (eta_env Σ) cu cs Conv napp t u.
  Proof.
    induction t in napp, u |- * using term_forall_list_ind;
      try (inversion 1; subst; constructor; eauto; fail).
    - inversion 1; subst; constructor.
      eapply All2_impl'; tea. eapply All_impl; eauto.
    - inversion 1; subst; constructor. now apply finst_Conv_inst_iff.
    - inversion 1; subst; constructor. now apply finst_Conv_inst_iff.
    - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    - inversion 1; subst; constructor.
      eapply All2_impl'; tea. eapply All_impl; eauto.
      cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
    - inversion 1; subst; constructor.
      eapply All2_impl'; tea. eapply All_impl; eauto.
      cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
    - intros h; depelim h. depelim o; constructor; cbn in X; constructor; intuition eauto.
      solve_all.
  Qed.

  Lemma finst_Conv_of_base napp t u :
    eq_term_upto_univ_napp (eta_env Σ) cu cs Conv napp t u ->
    eq_term_upto_univ_eta_napp Σ cu cs Conv napp t u.
  Proof.
    induction t in napp, u |- * using term_forall_list_ind;
      try (inversion 1; subst; constructor; eauto; fail).
    - inversion 1; subst; constructor.
      eapply All2_impl'; tea. eapply All_impl; eauto.
    - inversion 1; subst; constructor. now apply finst_Conv_inst_iff.
    - inversion 1; subst; constructor. now apply finst_Conv_inst_iff.
    - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    - inversion 1; subst; constructor.
      eapply All2_impl'; tea. eapply All_impl; eauto.
      cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
    - inversion 1; subst; constructor.
      eapply All2_impl'; tea. eapply All_impl; eauto.
      cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
    - intros h; depelim h. depelim o; constructor; cbn in X; constructor; intuition eauto.
      solve_all.
  Qed.

  Theorem finst_Conv_base napp t u :
    eq_term_upto_univ_eta_napp Σ cu cs Conv napp t u
    <~> eq_term_upto_univ_napp (eta_env Σ) cu cs Conv napp t u.
  Proof. split; [apply finst_Conv_to_base|apply finst_Conv_of_base]. Qed.

End Transport.
