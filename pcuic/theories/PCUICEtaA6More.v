(* Distributed under the terms of the MIT license. *)

(** * A6, part 3: further inversions that the typing metatheory uses

  Over [ws_cumul_pbE], untyped:
  - [conv_sort_invE] (used by base [PCUICCumulProp]);
  - [ws_cumul_pbE_LetIn_inv] (base [PCUICInductiveInversion]);
  - [ws_cumul_pbE_Prod_Prod_inv_l] (base [PCUICInductiveInversion]): the product
    inversion with the codomain in the left binder's context;
  - [invert_cumul_it_mkProd_or_LetIn_Sort_IndE] (base [PCUICFirstorder]), at every
    [pb];
  - [invert_cumul_prim_type_indE], [_prodE] (base [PCUICFirstorder],
    [PCUICSafeLemmata], erasure), at every [pb].

  **The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]);
  [declared_constant] with [primitive_invariants] and [prim_op_of Σ cst = None] by
  an environment declaring the primitive type; every [ws_cumul_pbE] premise by
  reflexivity. Instances: [PCUICEtaA6Instances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICConversion
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonEta PCUICEtaFInst
     PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind
     PCUICInductives PCUICClosedBodies.

Lemma prim_type_spine p cst : ∑ u args, prim_type p cst = mkApps (tConst cst u) args.
Proof.
  destruct p as [? []]; cbn.
  1-3: exists [], []; reflexivity.
  eexists _, [_]. simp prim_type. reflexivity.
Qed.

Lemma primitive_invariants_body tag cdecl : primitive_invariants tag cdecl -> cst_body cdecl = None.
Proof. destruct tag; cbn; intros [_ h _]; exact h. Qed.

Lemma eta1_LetIn_inv na b A t y : eta1 (tLetIn na b A t) y ->
  (∑ b', eta1 b b' × (y = tLetIn na b' A t)) + (∑ A', eta1 A A' × (y = tLetIn na b A' t))
  + (∑ t', eta1 t t' × (y = tLetIn na b A t')).
Proof.
  intros h. inv_eta h.
  all: first [ left; left; eexists; split; [eassumption|reflexivity]
             | left; right; eexists; split; [eassumption|reflexivity]
             | right; eexists; split; [eassumption|reflexivity] ].
Qed.

Lemma canon_it_mkProd_or_LetIn_Ind ctx ind u args :
  ∑ ctx', canon (it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args))
          = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) (map canon args)).
Proof.
  induction ctx as [|d ctx IH] using rev_ind.
  - exists []. cbn. now rewrite canon_mkApps.
  - destruct IH as [ctx' e]. rewrite it_mkProd_or_LetIn_app. destruct d as [na [b|] A]; cbn; rewrite e.
    + exists (ctx' ++ [vdef (canon_na na) (canon b) (canon A)]). now rewrite it_mkProd_or_LetIn_app.
    + exists (ctx' ++ [vass (canon_na na) (canon A)]). now rewrite it_mkProd_or_LetIn_app.
Qed.

Lemma eta1_it_mkProd_or_LetIn_Ind ctx ind u args y :
  eta1 (it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args)) y ->
  ∑ ctx' args', y = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) args').
Proof.
  revert y. induction ctx as [|d ctx IH] using rev_ind; intros y h.
  - cbn in h. destruct (eta1_mkApps_rigid_inv _ _ _ (eta_normal_Ind ind u) h) as (l' & -> & _).
    now exists [], l'.
  - rewrite it_mkProd_or_LetIn_app in h. destruct d as [na [b|] A]; cbn in h.
    + destruct (eta1_LetIn_inv _ _ _ _ _ h) as [[(b' & _ & ->)|(A' & _ & ->)]|(t' & ht & ->)].
      * exists (ctx ++ [vdef na b' A]), args. now rewrite it_mkProd_or_LetIn_app.
      * exists (ctx ++ [vdef na b A']), args. now rewrite it_mkProd_or_LetIn_app.
      * destruct (IH _ ht) as (ctx' & args' & ->). exists (ctx' ++ [vdef na b A]), args'.
        now rewrite it_mkProd_or_LetIn_app.
    + destruct (eta1_Prod_inv _ _ _ _ h) as [(A' & _ & ->)|(t' & ht & ->)].
      * exists (ctx ++ [vass na A']), args. now rewrite it_mkProd_or_LetIn_app.
      * destruct (IH _ ht) as (ctx' & args' & ->). exists (ctx' ++ [vass na A]), args'.
        now rewrite it_mkProd_or_LetIn_app.
Qed.

Section A6More.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation chain Γ := (clos_refl_trans (RE Γ)).
  Local Notation BE Γ := (clos_refl_trans (be_step Σ Γ)).
  Local Notation RF pb n := (eq_term_upto_univ_eta_napp Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).
  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  (** x15. *)
  Lemma conv_sort_invE Γ s s' : WS Conv Γ (tSort s) (tSort s') -> eq_sort (global_ext_constraints Σ) s s'.
  Proof. intros h. exact (ws_cumul_pbE_Sort_inv Conv h). Qed.

  (** x17. *)
  Lemma ws_cumul_pbE_LetIn_inv {le Γ na na' b b' ty ty' t t'} :
    WS le Γ (tLetIn na b ty t) (tLetIn na' b' ty' t') -> WS le Γ (t {0 := b}) (t' {0 := b'}).
  Proof.
    intros h. have h1 := ws_cumul_pbE_LetIn_l_inv (wfΣ := wfΣ) h.
    exact (ws_cumul_pbE_LetIn_r_inv (wfΣ := wfΣ) h1).
  Qed.

  (** x18: i11 with the codomain in the left binder's context. *)
  Lemma ws_cumul_pbE_Prod_Prod_inv_l {pb Γ na na' A B A' B'} :
    WS pb Γ (tProd na A B) (tProd na' A' B') ->
    [× eq_binder_annot na na', WS Conv Γ A A' & WS pb (Γ ,, vass na A) B B'].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
    destruct (open_Prod_inv Γ na A B hl) as [hA hB].
    destruct (open_Prod_inv Γ na' A' B' hr) as [hA' hB'].
    destruct (chain_Prod _ _ _ _ _ hv) as (na1 & A1 & B1 & [-> hna1 hA1 hB1]).
    destruct (chain_Prod _ _ _ _ _ hv') as (na2 & A2 & B2 & [-> hna2 hA2 hB2]).
    destruct (finst_Prod_l _ _ _ _ _ _ e) as (na3 & A3 & B3 & [E hna3 e2 e3]).
    injection E as <- <- <-.
    split.
    - apply (eq_binder_annot_trans _ _ _ (PCUICEtaA6.eq_binder_annot_canon_na na)).
      apply (eq_binder_annot_trans _ _ _ hna1).
      apply (eq_binder_annot_trans _ _ _ hna3).
      apply eq_binder_annot_sym.
      exact (eq_binder_annot_trans _ _ _ (PCUICEtaA6.eq_binder_annot_canon_na na') hna2).
    - constructor; [exact hΓ|exact hA|exact hA'|].
      apply (BE_JoinE Σ Γ Conv A A' A1 A2).
      + eapply rt_trans; [apply BE_to_canon|exact hA1].
      + eapply rt_trans; [apply BE_to_canon|exact hA2].
      + exact (RF_canon Σ _ _ _ _ e2).
    - constructor; [exact (closed_snoc_vass Γ na A hΓ hA)|exact hB| |].
      + apply open_snoc. exact (open_snoc_inv Γ _ _ hB').
      + apply (BE_JoinE Σ (Γ ,, vass na A) pb B B' B1 B2).
        * eapply rt_trans; [apply BE_to_canon|].
          exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB1).
        * eapply rt_trans; [apply BE_to_canon|].
          exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB2).
        * exact (RF_canon Σ _ _ _ _ e3).
  Qed.

  (** x16, at every [pb]. *)
  Lemma invert_cumul_it_mkProd_or_LetIn_Sort_IndE {pb Γ Δ s i u args} :
    WS pb Γ (it_mkProd_or_LetIn Δ (tSort s)) (mkApps (tInd i u) args) -> False.
  Proof.
    induction Δ as [|d Δ IH] using ctx_length_rev_ind; cbn.
    - exact (invert_cumul_sort_indE (wfΣ := wfΣ)).
    - rewrite it_mkProd_or_LetIn_app. destruct d as [na [b|] A]; cbn.
      + intros h. have h' := ws_cumul_pbE_LetIn_l_inv (wfΣ := wfΣ) h.
        try unfold subst1 in h'. rewrite subst_it_mkProd_or_LetIn /= in h'.
        eapply (IH (subst_context [b] 0 Δ)); [now len|exact h'].
      + exact (invert_cumul_prod_indE (wfΣ := wfΣ)).
  Qed.

  (** i37, i38, at every [pb]. *)
  Lemma invert_cumul_prim_type_indE {pb Γ cst cdecl p ind u' args'} :
    declared_constant Σ cst cdecl -> primitive_invariants (prim_val_tag p) cdecl ->
    prim_op_of Σ cst = None ->
    WS pb Γ (prim_type p cst) (mkApps (tInd ind u') args') -> False.
  Proof.
    intros hd hp hnop. destruct (prim_type_spine p cst) as (u & args & ->).
    exact (invert_cumul_axiom_indE (wfΣ := wfΣ) hd (primitive_invariants_body _ _ hp) hnop).
  Qed.

  Lemma invert_cumul_prim_type_prodE {pb Γ cst cdecl p na dom codom} :
    declared_constant Σ cst cdecl -> primitive_invariants (prim_val_tag p) cdecl ->
    prim_op_of Σ cst = None ->
    WS pb Γ (prim_type p cst) (tProd na dom codom) -> False.
  Proof.
    intros hd hp hnop. destruct (prim_type_spine p cst) as (u & args & ->).
    exact (invert_cumul_axiom_prodE (wfΣ := wfΣ) hd (primitive_invariants_body _ _ hp) hnop).
  Qed.

  (** x14, untyped: base's [wf_local] premise served only to scope the context,
      which the [ws_cumul_pbE] premise already does; [red_rel_all] replaces
      base's typed [red_expand_let]. *)
  Lemma ws_cumul_pbE_LetIn_l_inv_alt {Γ C na d ty b} :
    WS Conv Γ (tLetIn na d ty b) C -> WS Conv (Γ ,, vdef na d ty) b (lift0 1 C).
  Proof.
    intros h.
    have hΓ := wsE_ctx h.
    move: (wsE_left h). cbn [on_free_vars]. move/and3P => [hd hty hb].
    have hΓ1 : is_closed_context (Γ ,, vdef na d ty) := closed_snoc_vdef Γ na d ty hΓ hd hty.
    have hr : red Σ (Γ ,, vdef na d ty) b (lift 1 0 (b {0 := d}))
      := red_rel_all (Σ := Σ) (Γ := Γ ,, vdef na d ty) (i := 0) (body := d) (t := b) eq_refl.
    have h1 := red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := Conv)
                 (closed_red_of hΓ1 (open_snoc Γ _ b hb) hr).
    have h2 := ws_cumul_pbE_LetIn_l_inv (wfΣ := wfΣ) h.
    have h3 := weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := Conv) (Γ := Γ) (Γ' := [])
                 (Γ'' := [vdef na d ty]) h2 hΓ1.
    exact (WS_trans (wfΣ := wfΣ) h1 h3).
  Qed.

  (** The untyped lemma behind the uses in base [PCUICInductiveInversion]. The
      scoping premises are what base's [red_it_mkProd_or_LetIn_mkApps_Ind_cb]
      (closed reduction) needs. *)
  Lemma chain_it_mkProd_or_LetIn_mkApps_Ind Γ ctx ind u args T :
    is_closed_context Γ -> is_open_term Γ (it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args)) ->
    chain Γ (canon (it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args))) T ->
    ∑ ctx' args', T = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) args').
  Proof.
    intros hΓ ho h.
    destruct (canon_it_mkProd_or_LetIn_Ind ctx ind u args) as (ctx0 & e0). rewrite e0 in h.
    have ho0 : is_open_term Γ (it_mkProd_or_LetIn ctx0 (mkApps (tInd ind u) (map canon args))).
    { rewrite -e0. exact (canon_is_open_term Γ _ ho). }
    clear e0 ho. revert ho0 h. generalize (map canon args) as args0. revert ctx0.
    intros ctx0 args0 ho0 h. apply clos_rt_rt1n_iff in h.
    remember (it_mkProd_or_LetIn ctx0 (mkApps (tInd ind u) args0)) as x eqn:Ex.
    induction h as [x|x y z s _ IH] in ctx0, args0, ho0, Ex |- *; subst x.
    - now exists ctx0, args0.
    - destruct s as [[y0 [hr ->]]|he].
      + have hcr := closed_red_of hΓ ho0 (red1_red _ _ _ _ hr).
        destruct (red_it_mkProd_or_LetIn_mkApps_Ind_cb (wfΣ := wfΣ) hcr) as (ctx1 & args1 & ->).
        destruct (canon_it_mkProd_or_LetIn_Ind ctx1 ind u args1) as (ctx2 & e2).
        apply (IH ctx2 (map canon args1) e2).
        exact (canon_is_open_term Γ _ (closed_red_open_right_cb (wfΣ := wfΣ) hcr)).
      + destruct (eta1_it_mkProd_or_LetIn_Ind _ _ _ _ _ he) as (ctx1 & args1 & ->).
        exact (IH ctx1 args1 eq_refl (eta1_on_free_vars _ _ he _ ho0)).
  Qed.

End A6More.
