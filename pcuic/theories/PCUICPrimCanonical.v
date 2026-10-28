(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics
  PCUICGeneration PCUICArities PCUICSR PCUICInversion PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICInductiveInversion PCUICNormal
  PCUICSafeLemmata PCUICReduction PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICContexts PCUICLiftSubst PCUICUnivSubst PCUICClosed PCUICClosedTyp
  PCUICClassification PCUICPrimitiveRed
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICElimination
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICSigmaCalculus PCUICContextConversion
  PCUICCumulativity PCUICConfluence PCUICInduction.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** * Canonical forms at a primitive type (BET-319 row I)

  A well-typed weak-head normal form of the int or string type that is not a
  literal is neutral.  The machine needs this to classify a stuck case or
  projection whose discriminant is a rigid primitive application
  ([whnf_non_ctor_non_cofix_ind_typed], safechecker/theories/PCUICSafeReduce.v).

  Every head that is not neutral is refuted by typing: below a bodiless constant
  that is not an operation only applications of that constant are found
  ([ws_cumul_pb_Axiom_r_inv]), so a sort, a product, an inductive, a constructor
  or a cofixpoint type cannot be there; a literal of the type is excluded by the
  hypothesis; a literal of another type has another type constant, distinct by
  §4.2(a) [types_distinct]; and a rigid application recurses on its blocking
  argument. *)

(** Two tags that name the same type constant are the same tag. *)
Lemma primitive_constant_inj {Σ : global_env} t t' k :
  Retroknowledge.wf_retro Σ.(retroknowledge) ->
  primitive_constant Σ t = Some k -> primitive_constant Σ t' = Some k -> t = t'.
Proof.
  move=> [_ _ [d1 [d2 [d3 [d4 [d5 d6]]]]] _] h h'.
  destruct t, t'; cbn in h, h' => //; exfalso;
    solve [ eapply d1; eauto | eapply d2; eauto | eapply d3; eauto
          | eapply d4; eauto | eapply d5; eauto | eapply d6; eauto ].
Qed.

Section BelowAxiom.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.
  Context {kn : kername} {d : constant_body}
    (hd : declared_constant Σ kn d) (hb : cst_body d = None) (hnop : prim_op_of Σ kn = None).

  Lemma below_axiom {Γ T u} :
    Σ ;;; Γ ⊢ T ≤ tConst kn u -> ∑ u' args', Σ ;;; Γ ⊢ T ⇝ mkApps (tConst kn u') args'.
  Proof using hd hb hnop wfΣ.
    move=> h.
    destruct (ws_cumul_pb_Axiom_r_inv (args := []) hd hb hnop h) as (u' & args' & [r _ _]).
    now exists u', args'.
  Qed.

  Lemma sort_not_below_axiom {Γ s u} : Σ ;;; Γ ⊢ tSort s ≤ tConst kn u -> False.
  Proof using hd hb hnop wfΣ.
    move=> /below_axiom [u' [args' r]].
    eapply invert_red_sort in r.
    apply (f_equal decompose_app) in r. rewrite decompose_app_mkApps // in r.
  Qed.

  Lemma prod_not_below_axiom {Γ na A B u} : Σ ;;; Γ ⊢ tProd na A B ≤ tConst kn u -> False.
  Proof using hd hb hnop wfΣ.
    move=> /below_axiom [u' [args' r]].
    eapply invert_red_prod in r as (dom' & codom' & [e _ _]).
    apply (f_equal decompose_app) in e. rewrite decompose_app_mkApps // in e.
  Qed.

  Lemma ind_not_below_axiom {Γ ind ui l u} : Σ ;;; Γ ⊢ mkApps (tInd ind ui) l ≤ tConst kn u -> False.
  Proof using hd hb hnop wfΣ.
    move=> /below_axiom [u' [args' r]].
    eapply invert_red_mkApps_tInd in r as (args'' & [e _ _]).
    apply (f_equal decompose_app) in e. rewrite !decompose_app_mkApps // in e.
  Qed.

  Lemma Is_conv_to_Arity_axiom {Γ u} : Is_conv_to_Arity Σ Γ (tConst kn u) -> False.
  Proof using hd hb hnop wfΣ.
    move=> [ar [[r] isA]].
    pose proof (invert_red_axiom hd hb hnop r) as e. rewrite e in isA. inversion isA.
  Qed.

  Lemma typing_spine_arity_axiom {Γ T l u} :
    wf_local Σ Γ -> PCUICArities.typing_spine Σ Γ T l (tConst kn u) ->
    Is_conv_to_Arity Σ Γ T -> False.
  Proof using hd hb hnop wfΣ.
    move=> wf sp isc.
    eapply (isArity_typing_spine wf sp) in isc.
    now eapply Is_conv_to_Arity_axiom.
  Qed.

End BelowAxiom.

(** Every operation takes int or string arguments ([PrimitiveOps.info]). *)
Lemma prim_op_args_int_or_string {op i tag} :
  nth_error (po_args (info op)) i = Some tag -> tag = primInt \/ tag = primString.
Proof.
  move=> h. apply nth_error_In in h.
  destruct op; cbn in h; firstorder (subst; auto).
Qed.

(** Canonical forms.  The premises on [kn] are §4.2(b)'s [prim_op_tag_declared]
    (restatement approved by the lane lead): without a bodiless [kn] the statement
    is false, since a constructor could be typed at [tConst kn u] through the body
    of [kn]. *)
Lemma whnf_prim_type_canonical {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} flags {Γ a tag kn d u} :
  primitive_constant Σ tag = Some kn -> declared_constant Σ kn d -> primitive_invariants tag d ->
  tag = primInt \/ tag = primString ->
  whnf flags Σ Γ a -> Σ ;;; Γ |- a : tConst kn u -> lit_of_term a = None ->
  whne flags Σ Γ a.
Proof.
  move=> hkn hd hinv htag hw.
  revert tag kn d u hkn hd hinv htag.
  induction hw; intros tag kn dk uk hkn hd hinv htag typ hnl.
  all: assert (hb : cst_body dk = None)
         by (destruct htag as [-> | ->]; destruct hinv as [_ hb' _]; exact hb').
  all: pose proof wfΣ as (_ & wfr & _).
  all: assert (hnop : prim_op_of Σ kn = None)
         by exact (prim_op_of_primitive_constant Σ tag kn wfr hkn).
  - (* neutral *) assumption.
  - (* sort *) exfalso.
    apply inversion_Sort in typ as (? & ? & hle); auto.
    exact (sort_not_below_axiom hd hb hnop hle).
  - (* product *) exfalso.
    apply inversion_Prod in typ as (? & ? & ? & ? & hle); auto.
    exact (sort_not_below_axiom hd hb hnop hle).
  - (* lambda *) exfalso.
    apply inversion_Lambda in typ as (? & ? & ? & hle); auto.
    exact (prod_not_below_axiom hd hb hnop hle).
  - (* constructor *) exfalso.
    eapply inversion_mkApps in typ as [A [hC hs]]; auto.
    apply inversion_Construct in hC as [mdecl [idecl [cdecl [hΓ [isdecl [const htc]]]]]]; auto.
    assert (vty := declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const).
    eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
    pose proof isdecl as declc.
    destruct (on_declared_constructor declc) as [[onmind onind] [? [_ onc]]].
    destruct declc as [decli declc].
    destruct onc as [argslength cdecl_eq [cs' t] cargs cinds]; simpl.
    unfold type_of_constructor in hs, vty. simpl in hs, vty.
    rewrite cdecl_eq in hs vty.
    rewrite !subst_instance_it_mkProd_or_LetIn in hs vty.
    rewrite !subst_it_mkProd_or_LetIn subst_instance_length Nat.add_0_r in hs vty.
    rewrite subst_instance_mkApps subst_mkApps subst_instance_length in hs vty.
    assert (Hind : inductive_ind i < #|ind_bodies mdecl|).
    { destruct decli. now eapply nth_error_Some_length in H0. }
    rewrite (subst_inds_concl_head i) in hs vty => //.
    rewrite -it_mkProd_or_LetIn_app in hs vty.
    eapply typing_spine_smash in hs.
    rewrite expand_lets_mkApps in hs.
    set (Δ := smash_context [] _) in hs.
    have assΔ : assumption_context Δ by apply smash_context_assumption_context; constructor.
    destruct (Nat.lt_total #|v| (context_assumptions Δ)) as [lt|[eq|gt]].
    + destruct (nth_error (List.rev Δ) #|v|) as [dl|] eqn:hn.
      2:{ apply nth_error_None in hn. rewrite ?List.length_rev ?rev_length in hn.
          rewrite (assumption_context_assumptions assΔ) in lt. lia. }
      eapply (typing_spine_nth_error_None_prod _ _ _ _ _ _ #|v| dl) in hs
        as (na & dom & codom & cum); eauto.
      * exact (prod_not_below_axiom hd hb hnop cum).
      * eapply wf_local_smash_end; eauto.
        destruct vty as (_ & s & Hs & _).
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * now apply nth_error_None.
    + destruct (typing_spine_all_inv wfΣ _ _ _ _ _ hs eq) as [cum _].
      rewrite expand_lets_mkApps subst_mkApps /= in cum.
      exact (ind_not_below_axiom hd hb hnop cum).
    + exact (typing_spine_more_inv wfΣ _ _ _ _ _ _ _ hs gt).
    + exact wfΣ.
  - (* inductive *) exfalso.
    eapply inversion_mkApps in typ as (? & ? & ?); auto.
    eapply inversion_Ind in t as (? & ? & wfΓ & decl & cu & ?); auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    eapply (typing_spine_ind_type_inv decl) in t0; tea.
    rewrite it_mkProd_or_LetIn_app !subst_instance_it_mkProd_or_LetIn in t0.
    eapply (typing_spine_arity_axiom hd hb hnop) in t0; eauto.
    eapply typing_spine_isType_dom in t0 as (_ & s & Hs & _).
    eexists; split; [sq|]. now eapply wt_closed_red_refl.
    now do 2 eapply isArity_it_mkProd_or_LetIn.
    now eapply isTypeRel_isType, (declared_inductive_valid_type decl).
  - (* unsaturated fixpoint *) exfalso.
    eapply inversion_mkApps in typ as (? & ? & ?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto. apply isTypeRel_isType in a.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    destruct o as [[? [e' hnth]] | e']; rewrite e in e'; noconf e'.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite hnth in t0. destruct t0 as [na [dom [codom cum]]].
    exact (prod_not_below_axiom hd hb hnop cum).
  - (* cofixpoint *) exfalso.
    eapply inversion_mkApps in typ as [A [Hcof sp]]; auto.
    eapply inversion_CoFix in Hcof as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto.
    simpl in a.
    apply isTypeRel_isType in a.
    eapply typing_spine_strengthen in sp; eauto.
    eapply wf_cofixpoint_spine in sp as (Γ' & concl & _ & ?); eauto.
    move: s => [ind' [u' [indargs' [[ceq ccum] ck]]]].
    subst concl. move: ck.
    elim: Nat.ltb_spec => Hargs.
    + rewrite subst_it_mkProd_or_LetIn; len.
      set (ctx := subst_context _ _ _).
      assert (assumption_context ctx).
      eapply assumption_context_fold, assumption_context_firstn, smash_context_assumption_context; constructor.
      assert (#|ctx| > 0).
      { rewrite /ctx; len; rewrite firstn_length_le. len; lia. lia. }
      destruct ctx as [|ctx [na [b|] ty]] using rev_case. simpl in H0; lia.
      exfalso; move/assumption_context_app: H => [ass assd]; depelim assd.
      move/assumption_context_app: H => [ass assd]; depelim assd.
      rewrite it_mkProd_or_LetIn_app /mkProd_or_LetIn /= => cum.
      exact (prod_not_below_axiom hd hb hnop cum).
    + move=> [hargs ccum'].
      rewrite expand_lets_mkApps subst_mkApps /= in ccum'.
      exact (ind_not_below_axiom hd hb hnop ccum').
  - (* a literal: of this type it is excluded, of another type its constant differs *)
    exfalso.
    eapply inversion_Prim in typ as (prim_ty & cdecl & [? hpc hdecl' hinv' ? w]); tea.
    destruct p as [? []]; cbn in hnl; try discriminate hnl;
      destruct hinv' as [? hb' ?]; simp prim_type in w;
      destruct (below_axiom hd hb hnop w) as (u' & args' & r).
    + (* float *)
      pose proof (invert_red_axiom hdecl' hb' (prim_op_of_primitive_constant _ _ _ wfr hpc) r)
        as e.
      apply (f_equal decompose_app) in e. rewrite decompose_app_mkApps // in e. noconf e.
      pose proof (primitive_constant_inj _ _ _ wfr hpc hkn) as et. cbn in et.
      destruct htag as [-> | ->]; discriminate et.
    + (* array *)
      destruct (invert_red_axiom_app (args := [_]) hdecl' hb' (prim_op_of_primitive_constant _ _ _ wfr hpc) r)
        as [args'' [e _]].
      apply (f_equal decompose_app) in e. rewrite !decompose_app_mkApps // in e. noconf e.
      pose proof (primitive_constant_inj _ _ _ wfr hpc hkn) as et. cbn in et.
      destruct htag as [-> | ->]; discriminate et.
  - (* unsaturated operation: a product type *) exfalso.
    destruct (prim_app_typing_inv e1 typ (Nat.lt_le_incl _ _ l)) as [_ hprod].
    destruct (hprod l) as (na & A & B & hle).
    exact (prod_not_below_axiom hd hb hnop hle).
  - (* rigid operation: stuck on its blocking argument, by induction *)
    eapply whne_primapp_stuck; eauto.
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    destruct (prim_app_typing_inv e1 typ hle) as [hargs _].
    destruct (nth_error (po_args (info op)) #|ls|) as [tag'|] eqn:htag'.
    2:{ apply nth_error_None in htag'. rewrite /arity in e2. lia. }
    have hnth : nth_error (map term_of_lit ls ++ a :: rest) #|ls| = Some a.
    { rewrite nth_error_app2; len => //. rewrite Nat.sub_diag //. }
    destruct (hargs _ _ _ hnth htag') as (kn' & hkn' & hta).
    pose proof (validity typ) as isT.
    eapply PCUICSpine.inversion_mkApps_direct in typ as (A0 & s0 & hc & _ & _); tea.
    eapply inversion_Const in hc as (decl0 & wfΓ0 & hdecl0 & cu0 & hle0); tea.
    destruct (prim_op_head_type wfΓ0 hdecl0 cu0 e1 hle0) as (res & Tp & [_ _ _ _ hdeclared]).
    eapply All_nth_error in hdeclared; tea.
    destruct hdeclared as (kn'' & d'' & [hkn'' hd'' hinv'']).
    rewrite hkn' in hkn''. noconf hkn''.
    eapply (IHhw tag' kn' d'' [] hkn' hd'' hinv'' (prim_op_args_int_or_string htag') hta).
    assumption.
Qed.
