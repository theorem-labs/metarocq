(* Distributed under the terms of the MIT license. *)

(** * A3: the join relation [JoinE] is transitive

    [I5_join_trans] : is_closed_context Γ -> is_open_term Γ u ->
                      JoinE Σ Γ pb t u -> JoinE Σ Γ pb u w -> JoinE Σ Γ pb t w

  ** Route

  From [canon t ⇝* v ≈[pb] v' *⇜ canon u] and [canon u ⇝* x ≈[pb] x' *⇜ canon w]:
  - join [v'] and [x] at [y] by [canon_beta_eta_confluence] ([PCUICEtaCanonC4]):
    [canon u] is canonical ([canon_idem]) and scoped;
  - pull [v ≈ v'] along [v' ⇝* y] by the right-hand C1c: [v ⇝* z ≈ y];
  - push [x ≈ x'] along [x ⇝* y] by the left-hand C1c: [x' ⇝* z'] and [y ≈ z'];
  - [z ≈ y ≈ z'] by [compare_term_eta_trans].

  One step of [R_c ∪ eta1] commutes with U1' on either side:
  - an [R_c] step is [red1] then [canon]: [red1_finst_l]/[red1_finst_r], then
    [finst_canon] (below: [canon] preserves U1');
  - an [eta1] step: [eta1_finst_l], and its flip for the right-hand side.
  The η-C1c needs the reducing term scoped; every term on both chains is a reduct
  of the scoped [canon u], so only [u] needs a scoping premise.

  **The hypotheses are satisfiable.** [finst_canon]: [Reflexive (cs Conv)] by
  [compare_sort φ]. [I5_join_trans]: [ClosedBodies Σ], which every well-formed environment satisfies
  ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); [is_closed_context Γ] and
  [is_open_term Γ u] by any scoped context and term; the two joins by
  [t = u = w] (each [JoinE] is inhabited by [canon t] with itself,
  [compare_term_eta_refl]). *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICReduction PCUICOnFreeVars PCUICTyping PCUICUnivSubstitutionConv
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonC4
     PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaFInstC1c PCUICEtaFInstFlip
     PCUICEtaFInstEtaC1c PCUICEtaI5 PCUICClosedBodies.

(** ** [canon] preserves U1' *)

Section Canon.

  Context (Σ' : global_env)
          (cu : conv_pb -> Universe.t -> Universe.t -> Prop)
          (cs : conv_pb -> sort -> sort -> Prop)
          (hcs : RelationClasses.Reflexive (cs Conv)).

  Local Notation RF pb n := (eq_term_upto_univ_eta_napp Σ' cu cs pb n).

  (** [canon] replaces every λ domain by [canon_dom] on BOTH sides (compared by
      reflexivity of [cs Conv]), erases binder names (relevance kept, so
      [eq_binder_annot] survives), and leaves case-context types and bodies alone
      (the [eq_context_upto_names] side collapses to equal contexts). *)
  Lemma finst_canon pb napp t u : RF pb napp t u -> RF pb napp (canon t) (canon u).
  Proof.
    intros e. induction t in pb, napp, u, e |- * using term_forall_list_ind; depelim e; cbn.
    - (* Rel *) constructor.
    - (* Var *) constructor.
    - (* Evar *) constructor. apply All2_map.
      eapply All2_impl; [eapply All2_All_mix_left; eassumption|]. cbn.
      intros x y [IH h]. exact (IH _ _ _ h).
    - (* Sort *) constructor; assumption.
    - (* Prod *) constructor; [match goal with h : eq_binder_annot _ _ |- _ => exact h end|eauto|eauto].
    - (* Lambda *) constructor; [apply eq_binder_annot_refl'|constructor; apply hcs|eauto].
    - (* LetIn *)
      constructor; [match goal with h : eq_binder_annot _ _ |- _ => exact h end|eauto|eauto|eauto].
    - (* App *) constructor; eauto.
    - (* Const *) constructor; assumption.
    - (* Ind *) constructor; assumption.
    - (* Construct *) constructor; assumption.
    - (* Case *)
      match goal with
      | hP : tCasePredProp _ _ _, hB : tCaseBrsProp _ _,
        ep : eq_predicate _ _ _ _, eb : eq_branches _ _ _ |- _ =>
          destruct hP as (Hpar & _ & Hret); destruct ep as (hpar & hu & hctx & hret);
          rename hB into Hbrs; rename eb into hbrs
      end.
      unfold tCaseBrsProp in Hbrs. unfold eq_branches, eq_branch in hbrs.
      constructor.
      + unfold eq_predicate; cbn. split; [|split; [exact hu|split]].
        * apply All2_map. eapply All2_impl; [exact (All2_All_mix_left Hpar hpar)|].
          cbn. intros x y [IH h]. exact (IH _ _ _ h).
        * rewrite (canon_ctx_eq _ _ hctx). apply eq_context_upto_names_refl'.
        * exact (Hret _ _ _ hret).
      + eauto.
      + unfold eq_branches, eq_branch. apply All2_map.
        eapply All2_impl; [exact (All2_All_mix_left Hbrs hbrs)|].
        cbn. intros x y [[_ IH] [hc hb]]. unfold canon_branch; cbn.
        split; [rewrite (canon_ctx_eq _ _ hc); apply eq_context_upto_names_refl'|exact (IH _ _ _ hb)].
    - (* Proj *) constructor; eauto.
    - (* Fix *) constructor. unfold eq_mfixpoint in *. unfold tFixProp in *. apply All2_map.
      eapply All2_impl; [eapply All2_All_mix_left; eassumption|].
      cbn. intros x y [[IHt IHb] (ht & hb & hr & hn)].
      unfold canon_def; cbn. exact (IHt _ _ _ ht, (IHb _ _ _ hb, (hr, hn))).
    - (* CoFix *) constructor. unfold eq_mfixpoint in *. unfold tFixProp in *. apply All2_map.
      eapply All2_impl; [eapply All2_All_mix_left; eassumption|].
      cbn. intros x y [[IHt IHb] (ht & hb & hr & hn)].
      unfold canon_def; cbn. exact (IHt _ _ _ ht, (IHb _ _ _ hb, (hr, hn))).
    - (* Prim *) constructor.
      match goal with o : onPrims _ _ _ _ |- _ => depelim o end; cbn;
        [constructor|constructor|constructor|].
      match goal with X : tPrimProp _ _ |- _ => cbn in X; destruct X as (HPt & HPd & HPv) end.
      constructor; cbn.
      + match goal with h : cu Conv _ _ |- _ => exact h end.
      + eauto.
      + eauto.
      + apply All2_map. eapply All2_impl; [eapply All2_All_mix_left; eassumption|].
        cbn. intros x y [IH h]. exact (IH _ _ _ h).
  Qed.

End Canon.

(** ** A3 *)

Section A3.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ).

  Local Notation cu := (compare_universe Σ).
  Local Notation cs := (compare_sort Σ).
  Local Notation RF pb := (eq_term_upto_univ_eta_napp Σ.1 cu cs pb 0).
  Local Notation RE Γ := (union (R_c Σ Γ) eta1).

  (** The premises of the C1c lemmas, met by the real comparison. *)
  Lemma a3_pre_u : RelationClasses.PreOrder (cu Conv). Proof. tc. Qed.
  Lemma a3_pre_s : RelationClasses.PreOrder (cs Conv). Proof. tc. Qed.
  Lemma a3_su_u : SubstUnivPreserving (cu Conv) (cu Conv).
  Proof. exact (compare_universe_substu _ Conv). Qed.
  Lemma a3_su_s : SubstUnivPreserving (cu Conv) (cs Conv).
  Proof. exact (compare_sort_substu _ Conv). Qed.
  Lemma a3_sub_u pb : RelationClasses.subrelation (cu Conv) (cu pb).
  Proof. exact (compare_universe_subrel _ pb). Qed.
  Lemma a3_sub_s pb : RelationClasses.subrelation (cs Conv) (cs pb).
  Proof. exact (compare_sort_subrel _ pb). Qed.
  Lemma a3_refl_s : RelationClasses.Reflexive (cs Conv). Proof. tc. Qed.

  (** Scoping along the join. *)
  Lemma step_open Γ a b :
    is_closed_context Γ -> is_open_term Γ a -> RE Γ a b -> is_open_term Γ b.
  Proof.
    intros hΓ ha [[b0 [hr ->]]|he].
    - exact (canon_is_open_term Γ b0 (red1_is_open_term wfΣ hΓ hr ha)).
    - exact (eta1_on_free_vars a b he _ ha).
  Qed.

  Lemma star_open Γ a b :
    is_closed_context Γ -> is_open_term Γ a -> clos_refl_trans (RE Γ) a b -> is_open_term Γ b.
  Proof.
    intros hΓ ha h. revert ha.
    induction h as [x y s|x|x y z _ IH1 _ IH2]; intros hx.
    - exact (step_open Γ x y hΓ hx s).
    - exact hx.
    - exact (IH2 (IH1 hx)).
  Qed.

  (** One join step, left-hand term. *)
  Lemma step_finst_l Γ pb a b a' :
    is_open_term Γ a -> RE Γ a b -> RF pb a a' -> ∑ b', RE Γ a' b' × RF pb b b'.
  Proof.
    intros ha [[b0 [hr ->]]|he] e.
    - destruct (red1_finst_l Σ.1 cu cs a3_pre_u a3_pre_s a3_su_u a3_su_s Σ Γ a b0 hr
                  pb 0 a' (a3_sub_u pb) (a3_sub_s pb) e) as (b0' & hr' & e').
      exists (canon b0'). split; [left; exists b0'; split; [exact hr'|reflexivity]|].
      exact (finst_canon Σ.1 cu cs a3_refl_s pb 0 b0 b0' e').
    - destruct (eta1_finst_l Σ.1 cu cs a b he _ pb 0 a' (a3_sub_u pb) (a3_sub_s pb) ha e)
        as (b' & he' & e').
      exists b'. split; [right; exact he'|exact e'].
  Qed.

  (** One join step, right-hand term: [red1_finst_r], and the η-C1c for the
      flipped comparison, flipped back. *)
  Lemma step_finst_r Γ pb a a' b' :
    is_open_term Γ a' -> RF pb a a' -> RE Γ a' b' -> ∑ b, RE Γ a b × RF pb b b'.
  Proof.
    intros ha' e [[b0' [hr ->]]|he].
    - destruct (red1_finst_r Σ.1 cu cs a3_pre_u a3_pre_s a3_su_u a3_su_s Σ Γ pb 0 a a' b0'
                  (a3_sub_u pb) (a3_sub_s pb) e hr) as (b0 & hr0 & e0).
      exists (canon b0). split; [left; exists b0; split; [exact hr0|reflexivity]|].
      exact (finst_canon Σ.1 cu cs a3_refl_s pb 0 b0 b0' e0).
    - have ef := finst_flip Σ.1 cu (fun pb => flip (cu pb)) cs (fun pb => flip (cs pb))
                   pb pb 0 a a' (fun x y h => h) (fun x y h => h) (fun x y h => h)
                   (fun x y h => h) e.
      destruct (eta1_finst_l Σ.1 (fun pb => flip (cu pb)) (fun pb => flip (cs pb)) a' b' he
                  _ pb 0 a (fun x y h => a3_sub_u pb y x h) (fun x y h => a3_sub_s pb y x h)
                  ha' ef) as (b & hb & eb).
      exists b. split; [right; exact hb|].
      exact (finst_flip Σ.1 (fun pb => flip (cu pb)) cu (fun pb => flip (cs pb)) cs
               pb pb 0 b' b (fun x y h => h) (fun x y h => h) (fun x y h => h)
               (fun x y h => h) eb).
  Qed.

  (** Many join steps, left-hand term. *)
  Lemma star_finst_l Γ pb a b a' :
    is_closed_context Γ -> is_open_term Γ a ->
    clos_refl_trans (RE Γ) a b -> RF pb a a' ->
    ∑ b', clos_refl_trans (RE Γ) a' b' × RF pb b b'.
  Proof.
    intros hΓ ha h. apply clos_rt_rt1n_iff in h.
    revert a' ha. induction h as [a|a a1 b hs _ IH]; intros a' ha e.
    - exists a'. split; [apply rt_refl|exact e].
    - destruct (step_finst_l Γ pb a a1 a' ha hs e) as (a1' & hs' & e1).
      destruct (IH a1' (step_open Γ a a1 hΓ ha hs) e1) as (b' & hb' & eb).
      exists b'. split; [eapply rt_trans; [apply rt_step; exact hs'|exact hb']|exact eb].
  Qed.

  (** Many join steps, right-hand term. *)
  Lemma star_finst_r Γ pb a a' b' :
    is_closed_context Γ -> is_open_term Γ a' ->
    RF pb a a' -> clos_refl_trans (RE Γ) a' b' ->
    ∑ b, clos_refl_trans (RE Γ) a b × RF pb b b'.
  Proof.
    intros hΓ ha' e h. apply clos_rt_rt1n_iff in h.
    revert a e ha'. induction h as [a'|a' a1' b' hs _ IH]; intros a e ha'.
    - exists a. split; [apply rt_refl|exact e].
    - destruct (step_finst_r Γ pb a a' a1' ha' e hs) as (a1 & hs1 & e1).
      destruct (IH a1 e1 (step_open Γ a' a1' hΓ ha' hs)) as (b & hb & eb).
      exists b. split; [eapply rt_trans; [apply rt_step; exact hs1|exact hb]|exact eb].
  Qed.

  (** **A3.** *)
  Theorem I5_join_trans Γ pb t u w :
    is_closed_context Γ -> is_open_term Γ u ->
    JoinE Σ Γ pb t u -> JoinE Σ Γ pb u w -> JoinE Σ Γ pb t w.
  Proof.
    intros hΓ hu (v & v' & hv & hv' & e1) (x & x' & hx & hx' & e2).
    have hcu : is_open_term Γ (canon u) := canon_is_open_term Γ u hu.
    destruct (canon_beta_eta_confluence Σ wfΣ Γ (canon u) v' x hΓ hcu (canon_idem u) hv' hx)
      as (y & hy1 & hy2).
    destruct (star_finst_r Γ pb v v' y hΓ (star_open Γ _ _ hΓ hcu hv') e1 hy1) as (z & hz & ez).
    destruct (star_finst_l Γ pb x y x' hΓ (star_open Γ _ _ hΓ hcu hx) hy2 e2) as (z' & hz' & ez').
    exists z, z'. repeat split.
    - eapply rt_trans; [exact hv|exact hz].
    - eapply rt_trans; [exact hx'|exact hz'].
    - exact (compare_term_eta_trans Σ.1 _ pb 0 _ _ _ ez ez').
  Qed.

End A3.
