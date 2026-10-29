(* Distributed under the terms of the MIT license. *)

(** * A6, part 1: inversions for [ws_cumul_pbE] (untyped)

  The η versions of base's inversion lemmas for sorts, products, reduction, let-in
  and λ, over [ws_cumul_pbE]:
  - the forms "one side is a head" ([*_l_inv], [*_r_inv]): the other side's
    canonical form reaches the head by [(R_c ∪ eta1)*], with the component
    comparisons as [ws_cumul_pbE]. The form with the raw term in place of its
    canonical form is false ([A6_F_raw_false], [PCUICEtaA6Refutations]);
  - λ against λ ([ws_cumul_pbE_Lambda_inv] and its forms): the bodies at [pb],
    with no annotation or domain conjunct. The form with the bodies at [Conv] is
    false ([A6_D_conv_body_false]).

  ** Method
  [JoinE] is a pair of [(R_c ∪ eta1)*] chains from the canonical forms that end
  U1'-related. A chain from a rigid head keeps the head ([chain_Sort],
  [chain_Prod]) and gives a [BE] chain per component; U1'-related terms share the
  head ([finst_*_l], [finst_*_r]); the components are then joined by [BE_JoinE].

  **The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); every [ws_cumul_pbE] premise by
  reflexivity; the reductions by [rt_refl]. Instances: [PCUICEtaA6Instances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICConversion
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonEta PCUICEtaFInst
     PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst PCUICClosedBodies.
From MetaRocq.PCUIC Require PCUICEtaC3BR.

Lemma eq_binder_annot_canon_na na : eq_binder_annot na (canon_na na).
Proof. reflexivity. Qed.

Lemma eq_binder_annot_trans {A B C} (a : binder_annot A) (b : binder_annot B) (c : binder_annot C) :
  eq_binder_annot a b -> eq_binder_annot b c -> eq_binder_annot a c.
Proof. unfold eq_binder_annot. congruence. Qed.

Lemma eq_binder_annot_sym {A B} (a : binder_annot A) (b : binder_annot B) :
  eq_binder_annot a b -> eq_binder_annot b a.
Proof. unfold eq_binder_annot. congruence. Qed.

Section A6.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation chain Γ := (clos_refl_trans (RE Γ)).
  Local Notation BE Γ := (clos_refl_trans (be_step Σ Γ)).
  Local Notation RF pb n := (eq_term_upto_univ_eta_napp Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).
  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  Lemma WS_trans {pb Γ t u v} : WS pb Γ t u -> WS pb Γ u v -> WS pb Γ t v.
  Proof. exact (fun h1 h2 => ws_cumul_pbE_trans (Σ := Σ) (wfΣ := wfΣ) _ _ _ h1 h2). Qed.

  (** ** Chains from rigid heads *)

  Lemma chain_Sort Γ s v : chain Γ (tSort s) v -> v = tSort s.
  Proof.
    apply rt_from_normal. intros w [[w0 [h _]]|h].
    - exact (red_normal_Sort _ _ _ _ h).
    - exact (eta_normal_Sort _ _ h).
  Qed.

  Lemma BE_red1 Γ x y : red1 Σ Γ x y -> BE Γ x y.
  Proof. intros h. apply rt_step; left; left; exact h. Qed.
  Lemma BE_eta1 Γ x y : eta1 x y -> BE Γ x y.
  Proof. intros h. apply rt_step; left; right; exact h. Qed.
  Lemma BE_canon_eq Γ x y : canon x = canon y -> BE Γ x y.
  Proof. intros h. apply rt_step; right; exact h. Qed.
  Lemma BE_to_canon Γ x : BE Γ x (canon x).
  Proof. apply BE_canon_eq. symmetry. apply canon_idem. Qed.

  Lemma red1_Prod_inv Γ na A B y : red1 Σ Γ (tProd na A B) y ->
    (∑ A', red1 Σ Γ A A' × (y = tProd na A' B)) + (∑ B', red1 Σ (Γ ,, vass na A) B B' × (y = tProd na A B')).
  Proof.
    intros h. inv_red h.
    all: first [ left; eexists; split; [eassumption|reflexivity]
               | right; eexists; split; [eassumption|reflexivity] ].
  Qed.

  Lemma eta1_Prod_inv na A B y : eta1 (tProd na A B) y ->
    (∑ A', eta1 A A' × (y = tProd na A' B)) + (∑ B', eta1 B B' × (y = tProd na A B')).
  Proof.
    intros h. inv_eta h.
    all: first [ left; eexists; split; [eassumption|reflexivity]
               | right; eexists; split; [eassumption|reflexivity] ].
  Qed.

  Lemma chain_Prod Γ na A B v :
    chain Γ (tProd na A B) v ->
    ∑ na' A' B', [× v = tProd na' A' B', eq_binder_annot na na', BE Γ A A' & BE (Γ ,, vass na A) B B'].
  Proof.
    intros h. apply clos_rt_rt1n_iff in h.
    remember (tProd na A B) as x eqn:Ex.
    induction h as [x|x y v s _ IH] in na, A, B, Ex |- *; subst x.
    - exists na, A, B. split; [reflexivity|reflexivity|apply rt_refl|apply rt_refl].
    - destruct s as [[y0 [hr ->]]|he].
      + destruct (red1_Prod_inv _ _ _ _ _ hr) as [(A0 & hA0 & ->)|(B0 & hB0 & ->)].
        * destruct (IH (canon_na na) (canon A0) (canon B) eq_refl) as (na' & A' & B' & [-> hna hA hB]).
          exists na', A', B'. split.
          -- reflexivity.
          -- exact (eq_binder_annot_trans _ _ _ (eq_binder_annot_canon_na na) hna).
          -- eapply rt_trans; [apply BE_red1; exact hA0|]. eapply rt_trans; [apply BE_to_canon|exact hA].
          -- eapply rt_trans; [apply BE_to_canon|]. exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB).
        * destruct (IH (canon_na na) (canon A) (canon B0) eq_refl) as (na' & A' & B' & [-> hna hA hB]).
          exists na', A', B'. split.
          -- reflexivity.
          -- exact (eq_binder_annot_trans _ _ _ (eq_binder_annot_canon_na na) hna).
          -- eapply rt_trans; [apply BE_to_canon|exact hA].
          -- eapply rt_trans; [apply BE_red1; exact hB0|]. eapply rt_trans; [apply BE_to_canon|].
             exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB).
      + destruct (eta1_Prod_inv _ _ _ _ he) as [(A0 & hA0 & ->)|(B0 & hB0 & ->)].
        * destruct (IH na A0 B eq_refl) as (na' & A' & B' & [-> hna hA hB]).
          exists na', A', B'. split; [reflexivity|exact hna| |].
          -- eapply rt_trans; [apply BE_eta1; exact hA0|exact hA].
          -- exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB).
        * destruct (IH na A B0 eq_refl) as (na' & A' & B' & [-> hna hA hB]).
          exists na', A', B'. split; [reflexivity|exact hna|exact hA|].
          eapply rt_trans; [apply BE_eta1; exact hB0|exact hB].
  Qed.

  (** ** U1' keeps the head *)

  Lemma finst_Sort_l pb n s v : RF pb n (tSort s) v -> ∑ s', (v = tSort s') × compare_sort Σ pb s s'.
  Proof. intros e. depelim e. eexists; split; [reflexivity|assumption]. Qed.

  Lemma finst_Sort_r pb n s v : RF pb n v (tSort s) -> ∑ s', (v = tSort s') × compare_sort Σ pb s' s.
  Proof. intros e. depelim e. eexists; split; [reflexivity|assumption]. Qed.

  Lemma finst_Prod_l pb n na A B v : RF pb n (tProd na A B) v ->
    ∑ na' A' B', [× v = tProd na' A' B', eq_binder_annot na na', RF Conv 0 A A' & RF pb 0 B B'].
  Proof. intros e. depelim e. do 3 eexists; split; [reflexivity|assumption|assumption|assumption]. Qed.

  Lemma finst_Prod_r pb n na A B v : RF pb n v (tProd na A B) ->
    ∑ na' A' B', [× v = tProd na' A' B', eq_binder_annot na' na, RF Conv 0 A' A & RF pb 0 B' B].
  Proof. intros e. depelim e. do 3 eexists; split; [reflexivity|assumption|assumption|assumption]. Qed.

  Lemma finst_Sort_Prod pb n s na A B : RF pb n (tSort s) (tProd na A B) -> False.
  Proof. intros e. depelim e. Qed.

  Lemma finst_Prod_Sort pb n s na A B : RF pb n (tProd na A B) (tSort s) -> False.
  Proof. intros e. depelim e. Qed.

  (** Components of canonical terms are canonical. *)
  Lemma canon_Prod_comp na A B : canon (tProd na A B) = tProd na A B -> canon A = A × canon B = B.
  Proof. cbn [canon]. intros e. injection e as _ e1 e2. now split. Qed.

  Lemma chain_canonical Γ x y : canon x = x -> chain Γ x y -> canon y = y.
  Proof.
    intros cx h. induction h as [x y [[y0 [_ ->]]|he]|x|x y z _ IH1 _ IH2] in cx |- *.
    - apply canon_idem.
    - exact (eta1_canonical _ _ cx he).
    - exact cx.
    - exact (IH2 (IH1 cx)).
  Qed.

  (** ** Scoping helpers *)

  Lemma open_Prod_inv Γ na A B : is_open_term Γ (tProd na A B) ->
    is_open_term Γ A × is_open_term (Γ ,, vass na A) B.
  Proof. cbn [on_free_vars]. move/andP => [h1 h2]. split; [exact h1|exact (open_snoc Γ _ B h2)]. Qed.

  Lemma chain_open Γ t v : is_closed_context Γ -> is_open_term Γ t -> chain Γ (canon t) v -> is_open_term Γ v.
  Proof. intros hΓ ht h. exact (star_open Σ wfΣ Γ _ _ hΓ (canon_is_open_term Γ t ht) h). Qed.

  (** ** Sorts (i1-i5) *)

  Lemma ws_cumul_pbE_Sort_inv {Γ s s'} pb : WS pb Γ (tSort s) (tSort s') -> compare_sort Σ pb s s'.
  Proof.
    intros [_ _ _ (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
    apply chain_Sort in hv, hv'. subst v v'. depelim e. assumption.
  Qed.

  Lemma ws_cumul_pbE_Sort_Prod_inv {Γ s na dom codom} pb : WS pb Γ (tSort s) (tProd na dom codom) -> False.
  Proof.
    intros [_ _ _ (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
    apply chain_Sort in hv. subst v.
    destruct (chain_Prod _ _ _ _ _ hv') as (na' & A' & B' & [-> _ _ _]).
    exact (finst_Sort_Prod _ _ _ _ _ _ e).
  Qed.

  Lemma ws_cumul_pbE_Prod_Sort_inv {Γ s na dom codom} pb : WS pb Γ (tProd na dom codom) (tSort s) -> False.
  Proof.
    intros [_ _ _ (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
    apply chain_Sort in hv'. subst v'.
    destruct (chain_Prod _ _ _ _ _ hv) as (na' & A' & B' & [-> _ _ _]).
    exact (finst_Prod_Sort _ _ _ _ _ _ e).
  Qed.

  (** i4 in the pinned canonical form. *)
  Lemma ws_cumul_pbE_Sort_l_inv {Γ s T} pb : WS pb Γ (tSort s) T ->
    ∑ s', chain Γ (canon T) (tSort s') × compare_sort Σ pb s s'.
  Proof.
    intros [_ _ _ (v & v' & hv & hv' & e)]. cbn [canon] in hv.
    apply chain_Sort in hv. subst v.
    destruct (finst_Sort_l _ _ _ _ e) as (s' & -> & hs). exists s'. split; assumption.
  Qed.

  Lemma ws_cumul_pbE_Sort_r_inv {Γ s T} pb : WS pb Γ T (tSort s) ->
    ∑ s', chain Γ (canon T) (tSort s') × compare_sort Σ pb s' s.
  Proof.
    intros [_ _ _ (v & v' & hv & hv' & e)]. cbn [canon] in hv'.
    apply chain_Sort in hv'. subst v'.
    destruct (finst_Sort_r _ _ _ _ e) as (s' & -> & hs). exists s'. split; assumption.
  Qed.

  (** ** Products (i9-i11, i40, i41, i47) *)

  Lemma ws_cumul_pbE_Prod_l_inv {pb Γ na dom codom T} : WS pb Γ (tProd na dom codom) T ->
    ∑ na' dom' codom', [× chain Γ (canon T) (tProd na' dom' codom'), eq_binder_annot na na',
      WS Conv Γ dom dom' & WS pb (Γ ,, vass na dom) codom codom'].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)]. cbn [canon] in hv.
    destruct (open_Prod_inv Γ na dom codom hl) as [hdom hcodom].
    destruct (chain_Prod _ _ _ _ _ hv) as (na1 & A1 & B1 & [-> hna1 hA1 hB1]).
    destruct (finst_Prod_l _ _ _ _ _ _ e) as (na2 & A2 & B2 & [-> hna2 eA eB]).
    have ho : is_open_term Γ (tProd na2 A2 B2) := chain_open Γ T _ hΓ hr hv'.
    destruct (open_Prod_inv Γ na2 A2 B2 ho) as [hA2 hB2].
    exists na2, A2, B2. split.
    - exact hv'.
    - exact (eq_binder_annot_trans _ _ _ (eq_binder_annot_canon_na na) (eq_binder_annot_trans _ _ _ hna1 hna2)).
    - constructor; [exact hΓ|exact hdom|exact hA2|].
      apply (BE_JoinE Σ Γ Conv dom A2 A1 A2).
      + eapply rt_trans; [apply BE_to_canon|exact hA1].
      + apply rt_refl.
      + exact (RF_canon Σ _ _ _ _ eA).
    - constructor; [exact (closed_snoc_vass Γ na dom hΓ hdom)|exact hcodom| |].
      + apply open_snoc. exact (open_snoc_inv Γ _ _ hB2).
      + apply (BE_JoinE Σ (Γ ,, vass na dom) pb codom B2 B1 B2).
        * eapply rt_trans; [apply BE_to_canon|].
          exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ dom) hB1).
        * apply rt_refl.
        * exact (RF_canon Σ _ _ _ _ eB).
  Qed.

  Lemma ws_cumul_pbE_Prod_r_inv {pb Γ na dom codom T} : WS pb Γ T (tProd na dom codom) ->
    ∑ na' dom' codom', [× chain Γ (canon T) (tProd na' dom' codom'), eq_binder_annot na na',
      WS Conv Γ dom' dom & WS pb (Γ ,, vass na dom) codom' codom].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)]. cbn [canon] in hv'.
    destruct (open_Prod_inv Γ na dom codom hr) as [hdom hcodom].
    destruct (chain_Prod _ _ _ _ _ hv') as (na1 & A1 & B1 & [-> hna1 hA1 hB1]).
    destruct (finst_Prod_r _ _ _ _ _ _ e) as (na2 & A2 & B2 & [-> hna2 eA eB]).
    have ho : is_open_term Γ (tProd na2 A2 B2) := chain_open Γ T _ hΓ hl hv.
    destruct (open_Prod_inv Γ na2 A2 B2 ho) as [hA2 hB2].
    exists na2, A2, B2. split.
    - exact hv.
    - apply eq_binder_annot_sym.
      exact (eq_binder_annot_trans _ _ _ hna2 (eq_binder_annot_sym _ _
               (eq_binder_annot_trans _ _ _ (eq_binder_annot_canon_na na) hna1))).
    - constructor; [exact hΓ|exact hA2|exact hdom|].
      apply (BE_JoinE Σ Γ Conv A2 dom A2 A1).
      + apply rt_refl.
      + eapply rt_trans; [apply BE_to_canon|exact hA1].
      + exact (RF_canon Σ _ _ _ _ eA).
    - constructor; [exact (closed_snoc_vass Γ na dom hΓ hdom)| |exact hcodom|].
      + apply open_snoc. exact (open_snoc_inv Γ _ _ hB2).
      + apply (BE_JoinE Σ (Γ ,, vass na dom) pb B2 codom B2 B1).
        * apply rt_refl.
        * eapply rt_trans; [apply BE_to_canon|].
          exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ dom) hB1).
        * exact (RF_canon Σ _ _ _ _ eB).
  Qed.

  Lemma ws_cumul_pbE_Prod_Prod_inv {pb Γ na na' dom dom' codom codom'} :
    WS pb Γ (tProd na dom codom) (tProd na' dom' codom') ->
    [× eq_binder_annot na na', WS Conv Γ dom dom' & WS pb (Γ ,, vass na' dom') codom codom'].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
    destruct (open_Prod_inv Γ na dom codom hl) as [hdom hcodom].
    destruct (open_Prod_inv Γ na' dom' codom' hr) as [hdom' hcodom'].
    destruct (chain_Prod _ _ _ _ _ hv) as (na1 & A1 & B1 & [-> hna1 hA1 hB1]).
    destruct (chain_Prod _ _ _ _ _ hv') as (na2 & A2 & B2 & [-> hna2 hA2 hB2]).
    destruct (finst_Prod_l _ _ _ _ _ _ e) as (na3 & A3 & B3 & [E hna3 e2 e3]).
    injection E as <- <- <-.
    split.
    - apply (eq_binder_annot_trans _ _ _ (eq_binder_annot_canon_na na)).
      apply (eq_binder_annot_trans _ _ _ hna1).
      apply (eq_binder_annot_trans _ _ _ hna3).
      apply eq_binder_annot_sym.
      exact (eq_binder_annot_trans _ _ _ (eq_binder_annot_canon_na na') hna2).
    - constructor; [exact hΓ|exact hdom|exact hdom'|].
      apply (BE_JoinE Σ Γ Conv dom dom' A1 A2).
      + eapply rt_trans; [apply BE_to_canon|exact hA1].
      + eapply rt_trans; [apply BE_to_canon|exact hA2].
      + exact (RF_canon Σ _ _ _ _ e2).
    - constructor; [exact (closed_snoc_vass Γ na' dom' hΓ hdom')| |exact hcodom'|].
      + apply open_snoc. exact (open_snoc_inv Γ _ _ hcodom).
      + apply (BE_JoinE Σ (Γ ,, vass na' dom') pb codom codom' B1 B2).
        * eapply rt_trans; [apply BE_to_canon|].
          exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na' _ dom') hB1).
        * eapply rt_trans; [apply BE_to_canon|].
          exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na' _ dom') hB2).
        * exact (RF_canon Σ _ _ _ _ e3).
  Qed.

  Lemma cumul_Prod_invE {Γ na na' A B A' B'} :
    WS Cumul Γ (tProd na A B) (tProd na' A' B') ->
    [× eq_binder_annot na na', WS Conv Γ A A' & WS Cumul (Γ ,, vass na' A') B B'].
  Proof. apply ws_cumul_pbE_Prod_Prod_inv. Qed.

  Lemma conv_Prod_invE {Γ na na' A B A' B'} :
    WS Conv Γ (tProd na A B) (tProd na' A' B') ->
    [× eq_binder_annot na na', WS Conv Γ A A' & WS Conv (Γ ,, vass na' A') B B'].
  Proof. apply ws_cumul_pbE_Prod_Prod_inv. Qed.

  (** i47: base's squashed form. *)
  Lemma Prod_conv_cum_invE {Γ pb na1 na2 A1 A2 B1 B2} :
    ∥ WS pb Γ (tProd na1 A1 B1) (tProd na2 A2 B2) ∥ ->
    eq_binder_annot na1 na2 /\ ∥ WS Conv Γ A1 A2 ∥ /\ ∥ WS pb (Γ ,, vass na2 A2) B1 B2 ∥.
  Proof.
    intros [h]. destruct (ws_cumul_pbE_Prod_Prod_inv h) as [h1 h2 h3].
    split; [exact h1|split; constructor; assumption].
  Qed.

  (** ** Reduction on either side (i22, i23, i48, i53) *)

  Lemma closed_red_of {Γ t u} : is_closed_context Γ -> is_open_term Γ t -> red Σ Γ t u -> Σ ;;; Γ ⊢ t ⇝ u.
  Proof. intros h1 h2 h3. split; assumption. Qed.

  Lemma ws_cumul_pbE_red_r_inv {Γ T} U {U'} {pb} : WS pb Γ T U -> red Σ Γ U U' -> WS pb Γ T U'.
  Proof.
    intros h hr. apply (WS_trans h).
    exact (red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (closed_red_of (wsE_ctx h) (wsE_right h) hr)).
  Qed.

  Lemma ws_cumul_pbE_red_l_inv {Γ} T {T' U} {pb} : WS pb Γ T U -> red Σ Γ T T' -> WS pb Γ T' U.
  Proof.
    intros h hr. refine (WS_trans _ h).
    exact (red_ws_cumul_pbE_inv (Σ := Σ) (wfΣ := wfΣ) (closed_red_of (wsE_ctx h) (wsE_left h) hr)).
  Qed.

  Lemma conv_cum_red_invE pb Γ t1 t2 t1' t2' :
    Σ ;;; Γ ⊢ t1 ⇝ t1' -> Σ ;;; Γ ⊢ t2 ⇝ t2' -> WS pb Γ t1 t2 -> WS pb Γ t1' t2'.
  Proof.
    intros h1 h2 h. eapply ws_cumul_pbE_red_r_inv; [|exact (clrel_rel h2)].
    eapply ws_cumul_pbE_red_l_inv; [exact h|exact (clrel_rel h1)].
  Qed.

  Lemma ws_cumul_pbE_terms_red_inv {Γ ts ts' tsr tsr'} :
    All2 (closed_red Σ Γ) ts tsr -> All2 (closed_red Σ Γ) ts' tsr' ->
    ws_cumul_pbE_terms Σ Γ ts ts' -> ws_cumul_pbE_terms Σ Γ tsr tsr'.
  Proof.
    intros h1. induction h1 as [|x x' l lr hx _ IH] in ts', tsr' |- *; intros h2 h;
      unfold ws_cumul_pbE_terms in *.
    - depelim h. depelim h2. constructor.
    - depelim h. depelim h2. constructor; [|eapply IH; eassumption].
      eapply conv_cum_red_invE; [exact hx|eassumption|eassumption].
  Qed.

  (** ** Let-in (i8, i24, i25) *)

  Lemma ws_cumul_pbE_LetIn_l_inv {Γ C na d ty b} {pb} :
    WS pb Γ (tLetIn na d ty b) C -> WS pb Γ (subst10 d b) C.
  Proof.
    intros h. eapply ws_cumul_pbE_red_l_inv; [exact h|].
    apply rt_step. apply red_zeta.
  Qed.

  Lemma ws_cumul_pbE_LetIn_r_inv {Γ C na d ty b} {pb} :
    WS pb Γ C (tLetIn na d ty b) -> WS pb Γ C (subst10 d b).
  Proof.
    intros h. eapply ws_cumul_pbE_red_r_inv; [exact h|].
    apply rt_step. apply red_zeta.
  Qed.

  (** i8 in the canonical F form: the canonical form of [T] itself. *)
  Lemma ws_cumul_pbE_LetIn_r_inv_canon {Γ na d ty b T} :
    WS Cumul Γ T (tLetIn na d ty b) ->
    ∑ b', chain Γ (canon T) b' × WS Cumul Γ b' (b {0 := d}).
  Proof.
    intros h. exists (canon T). split; [apply rt_refl|].
    have hT : WS Cumul Γ (canon T) T.
    { constructor; [exact (wsE_ctx h)|exact (canon_is_open_term Γ T (wsE_left h))|exact (wsE_left h)|].
      apply JoinE_canon_eq. apply canon_idem. }
    exact (WS_trans hT (ws_cumul_pbE_LetIn_r_inv h)).
  Qed.

  (** ** λ, the D rows at [pb] (i51, i52) *)


  Lemma ws_cumul_pbE_Lambda_inv pb Γ na1 na2 A1 A2 b1 b2 :
    WS pb Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) -> WS pb (Γ ,, vass na1 A1) b1 b2.
  Proof.
    intros h.
    have hΓ := wsE_ctx h.
    move: (wsE_left h). cbn [on_free_vars]. move/andP => [hA1 hb1].
    move: (wsE_right h). cbn [on_free_vars]. move/andP => [hA2 hb2].
    have hΓ1 : is_closed_context (Γ ,, vass na1 A1) := closed_snoc_vass Γ na1 A1 hΓ hA1.
    (* weaken both λs by the binder, apply both to the bound variable, β back *)
    have hw := weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb) (Γ := Γ) (Γ' := [])
                 (Γ'' := [vass na1 A1]) h hΓ1.
    have happ : WS pb (Γ ,, vass na1 A1)
                  (tApp (lift0 1 (tLambda na1 A1 b1)) (tRel 0)) (tApp (lift0 1 (tLambda na2 A2 b2)) (tRel 0)).
    { apply ws_cumul_pbE_App; [exact hw|]. apply ws_cumul_pbE_refl; [exact hΓ1|reflexivity]. }
    have hbeta : forall na A b, is_open_term (Γ ,, vass na1 A1) (tApp (lift0 1 (tLambda na A b)) (tRel 0)) ->
        Σ ;;; Γ ,, vass na1 A1 ⊢ tApp (lift0 1 (tLambda na A b)) (tRel 0) ⇝ b.
    { intros na A b ho. split; [exact hΓ1|exact ho|]. apply rt_step. cbn [lift].
      have H := red_beta Σ (Γ ,, vass na1 A1) na (lift 1 0 A) (lift 1 1 b) (tRel 0).
      rewrite PCUICEtaC3BR.C3R.subst_rel0_lift_id0 in H. exact H. }
    have h1 := red_ws_cumul_pbE_inv (Σ := Σ) (wfΣ := wfΣ) (pb := pb) (hbeta na1 A1 b1 (wsE_left happ)).
    have h2 := red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb) (hbeta na2 A2 b2 (wsE_right happ)).
    exact (WS_trans h1 (WS_trans happ h2)).
  Qed.

  Lemma Lambda_conv_cum_invE pb Γ na1 na2 A1 A2 b1 b2 :
    ∥ WS pb Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) ∥ -> ∥ WS pb (Γ ,, vass na1 A1) b1 b2 ∥.
  Proof. intros [h]. constructor. exact (ws_cumul_pbE_Lambda_inv pb Γ na1 na2 A1 A2 b1 b2 h). Qed.

End A6.
