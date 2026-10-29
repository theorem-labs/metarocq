(* Distributed under the terms of the MIT license. *)
(* BET-64 ETAK (EtaConv), plan row K3: the η conversion checker, an E copy of
   PCUICSafeConversion.v (cut from trunk 0729d50e, prim-ops rows I/J in; scaffold
   e24d0aec). Normative design: lanes/eta/plan.md §2 I7, revisions 12-15.

   G7 (plan I7 rev 14), done in commit 9425b658: ConversionResult has no [~P] payload,
   every [Error e h] match lost [h], the 86 obligations that only proved the payload are
   deleted (289 -> 203 [Next Obligation]s), base's [herr] argument of
   [unfold_prims_args] is dropped, [isconv_complete]/[isconv_term_complete] are deleted.

   ===================== CONTRACTS ASSUMED (lanes/eta/etak/CONTRACTS.md) =====================
   A mismatch with an owner's entry must show here at once; this block is updated whenever an
   owner's entry changes the form.
   - ENV (EtaWfEnv, entry 06:55Z, fork/wip/etak-wfenv-2026-10-29 @ b86b8cc5): PCUICWfEnvEta is
     base PCUICWfEnv with the same names; [abstract_env_ext_wf X : abstract_env_ext_rel X Σ ->
     ∥ wf_extE Σ ∥], [abstract_env_ext_sq_wf : ∥ wfE Σ ∥], [abstract_env_ext_closed_bodies :
     ∥ ClosedBodies Σ ∥]; imported LAST. Section premise
     [normalization_in : forall Σ, wf_extE Σ -> Σ ∼_ext X -> NormalizationInE Σ].
   - REDUCE (EtaReduce, entry 06:58Z): the bridge PCUICSafeReduceEtaBridge over
     PCUICSafeReduceEta (base PCUICPosition.stack, welltypedE): [reduce_args_E flags X_type X Γ t
     args h] with [h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ (PCUICPosition.zip
     (t, PCUICPosition.appstack args []))]; facts [reduce_args_E_sound/_whnf/_isred/_Req],
     [reduce_stack_app_only], [app_only_zip], [stack_position_appstack_bridge],
     [stack_context_appstack_bridge], [zipp_appstack_bridge], [reduce_stack_vass],
     [reduce_args_E_vass]; the named E-facts hypothesis is the class instance
     [reduce_factsE : ReduceTypedFacts welltypedE wf_extE]. Other E uses of the machine
     ([reduce_term]) are [@PCUICSafeReduceEta.reduce_term (wt := welltypedE) (wfP := wf_extE)].
     The conversion calls reduction ONLY through these (plan rev 14 "B3 conditions").
   - POSITION (EtaPosK4, entry 06:48Z, @ 60266608): plan I7 rev 12-15 Coq text verbatim
     ([wf_stack], [eta_run], [drop_eta_run], [eta_virtuals], [eta_rename], [decompose_stack_eta],
     [zipp_eta], [stack_entry_context_eta se below], [stack_context_eta], [virtual_focus],
     [focus_context], [is_nil], [virt_ok], [eta_ren], [reducible_head_shape]).
     [conv_stack_ctx_eta] reads [ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta π1)
     (Γ ,,, stack_context_eta π2)] (the tree's [ws_cumul_ctx_pbE] has no FInst argument).
   - K4 (EtaPosK4): [pack] with the [wf_stack] fields, [R], [R_Acc], the descent lemmas of
     rev 14/15, over welltypedE and NormalizationInE. UNTIL K4 is announced over welltypedE,
     this file keeps its own copy of [pack]/[R_aux]/[R]/[R_Acc] in exactly that form.
   ============================================================================================= *)
From Stdlib Require Import ProofIrrelevance ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICConversion PCUICEquality PCUICConversion
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICPrincipality PCUICContextConversion PCUICContextConversionTyp PCUICSN PCUICUtils PCUICWfUniverses
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICClosed PCUICClosedTyp PCUICConvCumInversion
     PCUICCumulativitySpecEta PCUICTypingEta PCUICSNEta PCUICClosedBodies
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICContextConversionEta
     PCUICEtaK6EtaStep.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfReductionEta PCUICSafeReduceEta
     PCUICSafeReduceEtaBridge.
(* LAST among the stack providers, so the η stack shadows the base one. *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.
(* The E errors (EtaStackRefusal) shadow base PCUICErrors. *)
From MetaRocq.SafeChecker Require Import PCUICErrorsEta.
(* The E view algebra and the typed-facts class ConvTypedFacts (EtaConv's helper file), and
   K1's MustExpand (EtaK1). *)
From MetaRocq.SafeChecker Require Import PCUICSafeConversionEtaFacts PCUICMustExpandEta.
(* LAST (ENV contract). *)
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Instance red_brs_refl Σ p Γ: CRelationClasses.Reflexive (@red_brs Σ p Γ).
Proof.
  intros brs.
  eapply All2_same; unfold on_Trel; split; reflexivity.
Qed.

(** * Conversion for PCUIC without fuel

  Following PCUICSafeReduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Section Conversion.

  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  (* ENV contract: the normalization premise over welltypedE. *)
  Context {normalization_in : forall Σ, wf_extE Σ -> Σ ∼_ext X -> NormalizationInE Σ}.

  (* REDUCE contract: the named E-facts hypothesis of the reduction machine (EtaReduce's class;
     its fields are T1/T6 facts; its base instance [reduce_typed_facts_base] is restated at the
     end of this file). *)
  Context {reduce_factsE : ReduceTypedFacts welltypedE wf_extE}.

  (* The named typed facts of the conversion itself (plan rows T6 and T-row, fields
     [ctf_context], [ctf_case_brs_length], [ctf_wf_universes]); base instance
     [conv_typed_facts_base] in PCUICSafeConversionEtaFacts, restated at the end of this file. *)
  Context {conv_factsE : ConvTypedFacts welltypedE wf_extE}.

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_extE Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ ClosedBodies Σ ∥ := abstract_env_ext_closed_bodies _ _ _ wfΣ.

  Set Equations Transparent.
  Set Equations With UIP.

  Inductive state :=
  | Reduction
  | Term
  | Args
  | Fallback.

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : stateR Term Reduction
  | stateR_Args_Term : stateR Args Term
  | stateR_Fallback_Term : stateR Fallback Term
  | stateR_Args_Fallback : stateR Args Fallback.

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
  Proof using Type.
    assert (Acc stateR Args) as hArgs.
    { constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (Acc stateR Fallback) as hFall.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hArgs.
    }
    assert (Acc stateR Term) as hTerm.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      - apply hArgs.
      - apply hFall.
    }
    assert (Acc stateR Reduction) as hRed.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hTerm.
    }
    intro s. destruct s ; eauto.
  Qed.

  Notation wtp Γ t π :=
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (zipc t π)) (only parsing).

  Set Primitive Projections.

  (* K4's pack (plan rev 12-15): base's pack plus the [wf_stack] witness of each side's
     stack, which makes [stack_pos_wf] total over the virtual-argument states. *)
  Record pack (Γ : context) := mkpack {
    st   : state ;
    tm1  : term ;
    stk1 : stack ;
    tm2  : term ;
    stk2 : stack ;
    swf1 : wf_stack stk1 ;
    swf2 : wf_stack stk2 ;
    wth  : wtp Γ tm2 stk2
  }.

  Arguments st {_} _.
  Arguments tm1 {_} _.
  Arguments stk1 {_} _.
  Arguments tm2 {_} _.
  Arguments stk2 {_} _.
  Arguments swf1 {_} _.
  Arguments swf2 {_} _.
  Arguments wth {_} _.

  Definition wterm Γ := { t : term | forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` u) (` v).

  Lemma normalization_uptoE Σ (wfΣ : abstract_env_ext_rel X Σ) Γ u :
    welltypedE Σ Γ u -> Acc (cored' Σ Γ) u.
  Proof using normalization_in.
    intros h. destruct (heΣ _ wfΣ) as [hwf].
    eapply Acc_cored_cored'.
    - exact (@normalization_inE _ _ Σ (normalization_in Σ hwf wfΣ) Γ u h).
    - constructor. reflexivity.
  Qed.

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
  Proof using normalization_in.
    intros Γ [u hu].
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (hu _ wfΣ) as h.
    apply (normalization_uptoE _ wfΣ) in h.
    dependent induction h.
    constructor. intros [y hy] r.
    unfold wcored in r. cbn in r.
    eapply H0. eapply r; eauto.
  Qed.

  Definition eqt u v := ∥ u = v :> term ∥.

  Lemma eqt_eqterm {Σ} {wfΣ : abstract_env_ext_rel X Σ} {u v} :
    u = v -> eq_term Σ Σ u v.
  Proof using Type.
    intros <-.
    reflexivity.
  Qed.

  Local Instance eqt_refl : RelationClasses.Reflexive eqt.
  Proof using Type. red. intros x; constructor. reflexivity. Qed.

  Lemma eq_term_valid_pos :
    forall {u v p},
      validpos u p ->
      eqt u v ->
      validpos v p.
  Proof using X.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    intros u v p vp e.
    destruct e as [e'].
    eapply eq_term_valid_pos. all: eauto. now eapply eqt_eqterm.
    Unshelve. all:eauto.
  Qed.

  Definition weqt {Γ} (u v : wterm Γ) :=
    eqt (` u) (` v).

  Equations R_aux (Γ : context) :
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) ->
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) -> Prop :=
    R_aux Γ :=
      t ⊨ eqt \ fun t t' => forall Σ, abstract_env_ext_rel X Σ -> cored' Σ Γ t t' by _ ⨷
      @posR t ⊗
      w ⊨ weqt \ wcored Γ by _ ⨷
      @posR (` w) ⊗
      stateR.
  Next Obligation.
    split. 2: intuition eauto.
    exists (` p).
    destruct p as [p hp].
    eapply eq_term_valid_pos. all: eauto.
  Defined.
  Next Obligation.
    split. 2: assumption.
    exists (` p).
    destruct x as [u hu], x' as [v hv].
    destruct p as [p hp].
    simpl in *.
    eapply eq_term_valid_pos. all: eauto.
  Defined.

  Derive Signature for Subterm.lexprod.

  Lemma R_aux_Acc :
    forall Γ t p w q s,
      (forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ t) ->
      Acc (R_aux Γ) (t ; (p, (w ; (q, s)))).
  Proof using normalization_in.
    intros Γ t p w q s ht.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    rewrite R_aux_equation_1.
    unshelve eapply dlexmod_Acc.
    - intros x y [e]; eauto.  constructor. now symmetry.
    - intros x y z [e1] [e2]; eauto. constructor. now etransitivity; tea.
    - intro u. eapply Subterm.wf_lexprod.
      + intro. eapply posR_Acc.
      + intros [w' q'].
        unshelve eapply dlexmod_Acc.
        * intros x y [e]; eauto. constructor. now symmetry.
        * intros x y z [e1] [e2]; eauto. constructor.
          now etransitivity; tea.
        * intros [t' h']. eapply Subterm.wf_lexprod.
          -- intro. eapply posR_Acc.
          -- intro. eapply stateR_Acc.
        * eintros x x' y [e] [y' [x'' [r [[e1] [e2]]]]]; eauto.
          eexists _,_. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
          intuition eauto using sq.
          constructor. etransitivity; tea.
        * intros x.
          exists (@eqt_refl _).
          unfold weqt, eqt.
          intros [[q'' h] ?].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * cbn. intros x x' [[q'' h] ?] e.
          destruct e as [e'].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros x y z e1 e2 [[q'' h] ?].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros [t1 ht1] [t2 ht2] e [[q1 hq1] s1] [[q2 hq2] s2] h.
          destruct e as [e'].
          simpl in *.
          dependent destruction h.
          -- left. unfold posR in *. simpl in *. assumption.
          -- match goal with
             | |- context [ exist q1 ?hq1 ] =>
               assert (ee : hq1 = hq2) by eapply uip
             end.
            rewrite ee. right. clear ee. assumption.
        * eapply wcored_wf.
    - eintros x x' y [e] [y' [x'' [r [[e1] [e2]]]]]; eauto.
      intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      eexists _,_. intuition eauto using sq.
      constructor. etransitivity; eauto.
    - intros x. exists (@eqt_refl _). intros [[q' h] [? [? ?]]].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x x' [[q' h] [? [? ?]]] e.
      destruct e as [e']; eauto.
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x y z e1 e2 [[q' h] [? [? ?]]].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x x' e
             [[p1 hp1] [[u hu] [[q1 hq1] s1]]]
             [[p2 hp2] [[v hv] [[q2 hq2] s2]]] hl.
      destruct e as [e']; eauto.
      simpl in *.
      dependent destruction hl.
      + left. unfold posR in *.
        simpl in *.
        assumption.
      + match goal with
        | |- context [ exist p1 ?hp1 ] =>
          assert (ee : hp1 = hp2) by eapply uip
        end.
        rewrite ee. right. clear ee.
        dependent destruction H.
        * left. assumption.
        * unshelve econstructor 2. 1: assumption.
          dependent destruction H.
          -- left. unfold posR in *.
             simpl in *. assumption.
          -- right. assumption.
    - eapply Acc_equiv; try eapply (normalization_uptoE _ wfΣ); eauto.
      split; eauto; intros.
      erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Qed.

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos_wf (tm1 u) (stk1 u) (swf1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos_wf (tm2 u) (stk2 u) (swf2 u)) (only parsing).

  Notation obpack u:=
    (pzt u ; (pps1 u, (pwt u; (pps2 u, st u)))) (only parsing).

  Definition R Γ (u v : pack Γ) :=
    R_aux Γ (obpack u) (obpack v).

  Lemma R_Acc :
    forall Γ u,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (zipc (tm1 u) (stk1 u))) ->
      Acc (R Γ) u.
  Proof using normalization_in.
    intros Γ u h.
    eapply Acc_fun with (f := fun x => obpack x).
    apply R_aux_Acc. assumption.
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma R_aux_irrelevance Γ x y z :
    ((x.π1; x.π2.1), (existT (fun x => pos x × state) (` x.π2.2.π1) x.π2.2.π2)) =
    ((y.π1; y.π2.1), (existT (fun x => pos x × state) (` y.π2.2.π1) y.π2.2.π2)) ->
    R_aux Γ z x -> R_aux Γ z y.
  Proof using Type.
    destruct x as [t [pt [w [pw s]]]], y as [t' [pt' [w' [pw' s']]]].
    destruct z as [tz [ptz [wz [pwz sz]]]].
    cbn. intros [=]. subst. noconf H1. destruct w as [w wt], w' as [w' wt'].
    cbn in *. subst w'. noconf H3.
    unfold R_aux.
    intros hr. depelim hr.
    - now constructor.
    - cbn in H.
      eapply right_dlexmod with e. cbn.
      depelim H.
      * constructor. exact H.
      * constructor 2.
        depelim H.
        + now constructor.
        + eapply right_dlexmod with e0. cbn in H.
          depelim H.
          { constructor 1. cbn. exact H. }
          { constructor 2. exact H. }
  Qed.

  Lemma R_irrelevance Γ x y z :
    (x.(st), x.(tm1), x.(stk1), x.(tm2), x.(stk2)) =
    (y.(st), y.(tm1), y.(stk1), y.(tm2), y.(stk2)) ->
    R Γ z x -> R Γ z y.
  Proof using Type.
    destruct x as [s t π t' π' f1 f2 h], y as [s0 u ρ u' ρ' g1 g2 h']; cbn.
    intros [=]; subst.
    rewrite (uip f1 g1) (uip f2 g2).
    unfold R. eapply R_aux_irrelevance; cbn.
    reflexivity.
  Qed.

  Lemma R_cored :
    forall Γ p1 p2,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored Σ Γ (pzt p1) (pzt p2)) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ p1 p2 h.
    left. intros. eapply cored_cored'. eapply h; eauto.
  Qed.

  Lemma R_aux_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      eqt t1 t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof using Type.
    intros Γ t1 t2 p1 p2 [? [? ?]] s2 e h.
    unshelve eright.
    - eauto.
    - left. unfold posR. simpl. assumption.
  Qed.

  Lemma R_positionR :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      positionR (` (pps1 p1)) (` (pps1 p2)) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' f1 g1 h1] [s2 t2 π2 ρ2 t2' f2 g2 h2] e h. simpl in *.
    eapply R_aux_positionR ; simpl.
    - assumption.
    - assumption.
  Qed.

  Lemma R_aux_cored2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` w1) (` w2)) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof using Type.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 h.
    cbn in e2. cbn in h. subst.
    unshelve eright.
    - auto.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      left. assumption.
  Qed.

  Lemma R_cored2 :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
          cored Σ Γ (` (pwt p1)) (` (pwt p2))) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' f1 g1 h1] [s2 t2 π2 ρ2 t2' f2 g2 h2] e1 e2 h. simpl in *.
    eapply R_aux_cored2. all: simpl. all: auto.
    destruct s1, s2.
    all: intros; eapply cored_cored'.
    all: eauto.
  Qed.

  Lemma R_aux_positionR2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (eqt (` w1) (` w2)) ->
      positionR (` q1) (` q2) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof using Type.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 e3 h.
    cbn in e2. cbn in e3. subst.
    unshelve eright.
    - auto.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      unshelve eright.
      + auto.
      + left. unfold posR. simpl. assumption.
  Qed.

  Lemma R_positionR2 :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (eqt (` (pwt p1)) (` (pwt p2))) ->
      positionR (` (pps2 p1)) (` (pps2 p2)) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' f1 g1 h1] [s2 t2 π2 ρ2 t2' f2 g2 h2] e1 e2 e3 h.
    simpl in *.
    eapply R_aux_positionR2. all: simpl. all: auto.
  Qed.

  Lemma R_aux_stateR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2 ,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (eqt (` w1) (` w2)) ->
      ` q1 = ` q2 ->
      stateR s1 s2 ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof using Type.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] [q1 hq1] [q2 hq2] s1 s2
           e1 e2 e3 e4 h.
    cbn in e2. cbn in e3. cbn in e4. subst.
    unshelve eright.
    - auto.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      unshelve eright.
      + auto.
      + unfold R_aux_obligations_obligation_2. simpl.
        match goal with
        | |- context [ exist q2 ?hq1 ] =>
          assert (e' : hq1 = hq2) by eapply uip
        end.
        rewrite e'.
        right. assumption.
  Qed.

  Lemma R_stateR :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (eqt (` (pwt p1)) (` (pwt p2))) ->
      ` (pps2 p1) = ` (pps2 p2) ->
      stateR (st p1) (st p2) ->
      R Γ p1 p2.
  Proof using Type.
    intros Γ [s1 t1 π1 ρ1 t1' f1 g1 h1] [s2 t2 π2 ρ2 t2' f2 g2 h2] e1 e2 e3 e4 h.
    simpl in *.
    eapply R_aux_stateR. all: simpl. all: auto.
  Qed.

  Definition abstract_env_compare_global_instance := compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X).

  Notation eqb_ctx := (eqb_ctx_upto (abstract_env_compare_universe X) (abstract_env_compare_sort X) abstract_env_compare_global_instance Conv).
  Notation cmpb_term_napp := (eqb_term_upto_univ_napp (abstract_env_compare_universe X) (abstract_env_compare_sort X) abstract_env_compare_global_instance).
  Notation cmpb_term pb := (eqb_term_upto_univ (abstract_env_compare_universe X) (abstract_env_compare_sort X) abstract_env_compare_global_instance pb).
  Notation eqb_term := (cmpb_term Conv).
  Notation leqb_term := (cmpb_term Cumul).

  Lemma iff_reflect (P : Prop) (b : bool) :
    P <-> b -> reflect P b.
  Proof using Type.
    intro H. apply ssrbool.introP.
    - intuition.
    - destruct b; intuition.
  Qed.

  Definition wf_universe_iff  Σ u :
    wf_universeb Σ u <-> wf_universe Σ u.
  Proof using Type.
    symmetry; apply reflect_iff. eapply wf_universe_reflect.
  Qed.

  Definition wf_sort_iff Σ s :
    wf_sortb Σ s <-> wf_sort Σ s.
  Proof using Type.
    symmetry; apply reflect_iff. eapply wf_sort_reflect.
  Qed.

  Definition wf_instance_iff Σ u :
    wf_instanceb Σ u <-> wf_instance Σ u.
  Proof using Type.
    symmetry; apply reflect_iff. eapply wf_instanceP.
  Qed.

  (* rev 14 NB1: the conversion state compares the η contexts. (K4 will define it; this
     local copy has exactly the form of EtaPosK4's entry, 06:48Z.) *)
  Definition conv_stack_ctx_eta (Γ : context) (π1 π2 : stack) : Prop :=
    forall Σ, abstract_env_ext_rel X Σ ->
      ∥ ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta π1) (Γ ,,, stack_context_eta π2) ∥.

  Notation conv_stack_ctx Γ π1 π2 := (conv_stack_ctx_eta Γ π1 π2) (only parsing).

  (* The E counterpart of base [conv_cum]. *)
  Definition conv_cumE leq Σ Γ t u := ∥ ws_cumul_pbE leq Σ Γ t u ∥.

  (* Base [conv_cum_trans] took [wf Σ]; the E environment gives [ClosedBodies Σ]
     ([abstract_env_ext_closed_bodies]), which is all A3's transitivity needs. *)
  Lemma conv_cumE_trans {leq Σ Γ} : ClosedBodies Σ -> RelationClasses.Transitive (conv_cumE leq Σ Γ).
  Proof using Type.
    intros cb x y z [h1] [h2]. constructor. etransitivity; eassumption.
  Qed.

  (* I7 S13: [conv_term] reads the η views, in the η context of side 1. *)
  Notation conv_term leq Γ t π t' π' :=
    (forall Σ, abstract_env_ext_rel X Σ ->
       conv_cumE leq Σ (Γ ,,, stack_context_eta π) (zipp_eta t π) (zipp_eta t' π'))
      (only parsing).

  (* G7 (plan.md I7 rev 14): the E ConversionResult drops base's [~P] payload
     (base: [Error (e : ConversionError) (h : ~P)]). Under decision (C) a refusal
     claims nothing, so [no] needs no proof. *)
  Inductive ConversionResult (P : Prop) :=
  | Success (h : P)
  | Error (e : ConversionError).

  Arguments Success {_} _.
  Arguments Error {_} _.

  (* I7: [isred_full]/whnf reads the η view (one of the eleven η-view sites). *)
  Definition isred_full Γ t π :=
    isApp t = false /\
    forall Σ, abstract_env_ext_rel X Σ ->
      ∥ whnf RedFlags.nodelta Σ (Γ ,,, stack_context_eta π) (zipp_eta t π) ∥.

  Lemma eta_pair {A B} (p q : A * B) :
    p = q ->
    (p.1, p.2) = (q.1, q.2).
  Proof using Type. now destruct p, q. Qed.

  Ltac is_var t :=
    match goal with
    | v : _ |- _ =>
      match t with
      | v => idtac
      end
    end.

  Lemma zipp_stack_cat_decompose_stack t π π' :
    zipp t (π ++ (decompose_stack π').2) = zipp t π.
  Proof using Type.
    rewrite zipp_stack_cat; auto.
    destruct decompose_stack eqn:decomp.
    now apply decompose_stack_noStackApp in decomp.
  Qed.

  Lemma zipc_decompose_stack_empty t π :
    (decompose_stack π).2 = [] ->
    zipc t π = zipp t π.
  Proof using Type.
    destruct decompose_stack eqn:decomp.
    apply decompose_stack_eq in decomp as ->.
    cbn; intros ->.
    rewrite zipc_appstack zipp_as_mkApps decompose_stack_appstack.
    cbn.
    now rewrite app_nil_r.
  Qed.

  Ltac reduce_stack_facts Σ wfΣ :=
    repeat
      match goal with
      | [H: (?a, ?b) = reduce_stack ?f _ ?X ?Γ ?t ?π ?h |- _] =>
        let rid := fresh "r" in
        let decompid := fresh "d" in
        let whid := fresh "w" in
        let isr := fresh "isr" in
        pose proof (reduce_stack_sound f _ X Σ wfΣ Γ t π h) as [rid];
        pose proof (reduce_stack_decompose f _ X Γ t π h) as decompid;
        pose proof (reduce_stack_whnf f _ X Γ t π h Σ wfΣ) as whid;
        pose proof (reduce_stack_isred f _ X Γ t π h) as isr;
        rewrite <- H in rid, decompid, whid, isr; cbn in rid, decompid, whid, isr;
        clear H
      end.

  Lemma zipc_unfold_decompose_stack t π :
    zipc t π = zipc (mkApps t (decompose_stack π).1) (decompose_stack π).2.
  Proof using Type.
    rewrite <- zipc_appstack.
    destruct (decompose_stack π) eqn:decomp.
    now apply decompose_stack_eq in decomp as ->.
  Qed.

  Ltac simpl_stacks :=
    (repeat
       match goal with
       | [H: (?a, ?b) = decompose_stack ?π |- _] =>
         is_var a;
         is_var b;
         apply eta_pair in H; cbn in H; noconf H
       end);
    (repeat
       match goal with
       | [H: context[decompose_stack (appstack ?l ?ρ)] |- _] =>
         (rewrite (decompose_stack_appstack l ρ) in H; cbn in H) || fail 2
       | [H: context[stack_context (?π ++ ?π')] |- _] =>
         (rewrite (stack_context_stack_cat π' π) in H; cbn in H) || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[zipc ?t ?π] |- _] =>
         (rewrite (zipc_decompose_stack_empty t π H) in H'; cbn in H') || fail 2
       | [H: context[stack_context (decompose_stack ?π).2] |- _] =>
         (rewrite (stack_context_decompose π) in H; cbn in H) || fail 2
       | [H: context[zipp ?t (?π ++ (decompose_stack ?π').2)] |- _] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π') in H; cbn in H) || fail 2
       | [H: context[zipc ?t (appstack ?args ?π)] |- _] =>
         (rewrite (@zipc_appstack t args π) in H; cbn in H) || fail 2
       | [H: context[zipc ?t (?π ++ ?π')] |- _] =>
         (rewrite (zipc_stack_cat t π π') in H; cbn in H) || fail 2
       | [H: context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2] |- _] =>
         unfold zip in H
       | [H: context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2] |- _] =>
         (rewrite <- (zipc_unfold_decompose_stack t π) in H; cbn in H) || fail 2
       | [H: isStackApp ?π = false, H': context[zipp ?t ?π] |- _] =>
         (rewrite (zipp_noStackApp t π H) in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2, H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π') in H'; cbn in H')
         || fail 2

       | [|- context[decompose_stack (appstack ?l ?ρ)]] =>
         (rewrite (decompose_stack_appstack l ρ); cbn) || fail 2
       | [|- context[stack_context (?π ++ ?π')]] =>
         (rewrite (stack_context_stack_cat π' π); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H; cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[zipc ?t ?π]] =>
         (rewrite (zipc_decompose_stack_empty t π H); cbn) || fail 2
       | [|- context[stack_context (decompose_stack ?π).2]] =>
         (rewrite (stack_context_decompose π); cbn) || fail 2
       | [|- context[zipp ?t (?π ++ (decompose_stack ?π').2)]] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π'); cbn) || fail 2
       | [|- context[zipc ?t (appstack ?args ?π)]] =>
         (rewrite (@zipc_appstack t args π); cbn) || fail 2
       | [|- context[zipc ?t (?π ++ ?π')]] =>
         (rewrite (zipc_stack_cat t π π'); cbn) || fail 2
       | [|- context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2]] =>
         unfold zip
       | [|- context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2]] =>
         (rewrite <- (zipc_unfold_decompose_stack t π); cbn) || fail 2
       | [H: isStackApp ?π = false |- context[zipp ?t ?π]] =>
         (rewrite (zipp_noStackApp t π H); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2 |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π'); cbn) || fail 2
       end);
    repeat
      match goal with
      | [H: context[zipp ?t ?π] |- _] => rewrite (zipp_as_mkApps t π) in H
      | [|- context[zipp ?t ?π]] => rewrite (zipp_as_mkApps t π)
      end.

  Ltac simpl_reduce_stack Σ wfΣ := reduce_stack_facts Σ wfΣ ; simpl_stacks.

  (* Tailored view for isconv_prog and precondition for fallback case *)
  Equations prog_discr (t1 t2 : term) : Prop :=
    prog_discr (tApp _ _) (tApp _ _) := False ;
    prog_discr (tConst _ _) (tConst _ _) := False ;
    prog_discr (tLambda _ _ _) (tLambda _ _ _) := False ;
    prog_discr (tProd _ _ _) (tProd _ _ _) := False ;
    prog_discr (tCase _ _ _ _) (tCase _ _ _ _) := False ;
    prog_discr (tProj _ _) (tProj _ _) := False ;
    prog_discr (tFix _ _) (tFix _ _) := False ;
    prog_discr (tCoFix _ _) (tCoFix _ _) := False ;
    prog_discr (tPrim _) (tPrim _) := False ;
    prog_discr _ _ := True.

  (* rev 15 C7: base's Ret plus the four new arguments [hv_i] (T0's [virt_ok]) and [hwf_i]
     (the η contexts are well formed), unconditional and in the same position for every
     [s] (the arity must be the same for all [s], else the extracted code is wrong).
     The Args result reads the η argument lists, in side 1's η context. *)
  Definition Ret s Γ t π t' π' :=
    forall (leq : conv_pb),
      conv_stack_ctx Γ π π' ->
      virt_ok t π = true -> virt_ok t' π' = true ->
      (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥) ->
      (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π') ∥) ->
      (match s with Fallback | Term => isred_full Γ t π | _ => True end) ->
      (match s with Fallback | Term => isred_full Γ t' π' | _ => True end) ->
      (match s with | Fallback => prog_discr t t' | _ => True end) ->
      match s with
      | Reduction
      | Term
      | Fallback => ConversionResult (conv_term leq Γ t π t' π')
      | Args => ConversionResult (forall Σ, abstract_env_ext_rel X Σ ->
                   ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π)
                       (decompose_stack_eta π).1 (decompose_stack_eta π').1 ∥)
      end.

  Definition Aux s Γ t1 π1 t2 π2 (f1 : wf_stack π1) (f2 : wf_stack π2) h2 :=
     forall s' t1' π1' t2' π2'
       (f1' : wf_stack π1') (f2' : wf_stack π2')
       (h1' : wtp Γ t1' π1')
       (h2' : wtp Γ t2' π2'),
       conv_stack_ctx Γ π1 π2 ->
       R Γ
         (mkpack Γ s' t1' π1' t2' π2' f1' f2' h2')
         (mkpack Γ s t1 π1 t2 π2 f1 f2 h2) ->
       Ret s' Γ t1' π1' t2' π2'.

  (* rev 15 C2: the E [_isconv_args'] measures every call against the entry pack [y], a fixed
     parameter (base's [Aux'] measures against the current state and moves back by [expand],
     which the side-1 virtual call cannot satisfy: its side-1 position equals the entry's). *)
  Definition AuxE' Γ (y : pack Γ) :=
    forall s' t1' π1' t2' π2' (f1' : wf_stack π1') (f2' : wf_stack π2')
      (h1' : wtp Γ t1' π1') (h2' : wtp Γ t2' π2'),
      R Γ (mkpack Γ s' t1' π1' t2' π2' f1' f2' h2') y ->
      Ret s' Γ t1' π1' t2' π2'.

  Notation expand aux := (fun a b c d e f g h i j k => aux _ _ _ _ _ _ _ _ _ _ _) (only parsing).

  Local Notation yes := (Success _) (only parsing).
  Local Notation no := (fun e => Error e) (only parsing).

  (* TODO NOTE
     repack could also take another argument of type
     ConversionError -> ConversionError
     to keep a full error trace (we currently only do it partially).
  *)
  Local Notation repack e :=
    (match e with Success h => Success _ | Error er => Error er end)
    (only parsing).

  (* The holes after the states: [f1' f2' h1' h2' hx R], then Ret's [leq hx' hv1 hv2 hwf1 hwf2]
     and the three state-dependent premises. *)
  Notation isconv_red_raw leq t1 π1 t2 π2 aux :=
    (aux Reduction t1 π1 t2 π2 _ _ _ _ _ _ leq _ _ _ _ _ I I I) (only parsing).
  Notation isconv_prog_raw leq t1 π1 t2 π2 aux :=
    (aux Term t1 π1 t2 π2 _ _ _ _ _ _ leq _ _ _ _ _ _ _ I) (only parsing).
  Notation isconv_args_raw leq t1 π1 t2 π2 aux :=
    (aux Args t1 π1 t2 π2 _ _ _ _ _ _ leq _ _ _ _ _ I I I) (only parsing).
  Notation isconv_fallback_raw leq t1 π1 t2 π2 aux :=
    (aux Fallback t1 π1 t2 π2 _ _ _ _ _ _ leq _ _ _ _ _ _ _ _) (only parsing).

  Notation isconv_red leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args leq t1 π1 t2 π2 aux :=
    (repack (isconv_args_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_fallback leq t1 π1 t2 π2 aux :=
    (repack (isconv_fallback_raw leq t1 π1 t2 π2 aux)) (only parsing).

  (* G2 (rev 14 B4) and G2b (EtaConv, see the log's STATEMENT CHANGES): the rebuilt stack is
     well formed, and a rigid head (λ, Π, sort, primitive) carries no pending η run, without
     which the Term state's [isred_full] (whnf of the η view) is false. *)
  Definition rebuilt_ok (t' : term) (args' : list term) (ρ : stack) : bool :=
    wf_stack (appstack args' ρ) && eta_head_ok t' ρ.

  (* rev 13 B3/F-9: reduction runs on the decomposed spine only, through reduce_args_E, in the
     focus's own context (the η context on an Eta_arg side). *)
  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hv1 : virt_ok t1 π1 = true) (hv2 : virt_ok t2 π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Reduction Γ t1 π1 t2 π2 f1 f2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=

    _isconv_red Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2 aux
    with inspect (decompose_stack π1) := {
    | @exist (args1, ρ1) e1 with inspect (decompose_stack π2) := {
      | @exist (args2, ρ2) e2
        with inspect (reduce_args_E RedFlags.nodelta X_type X
                                    (Γ ,,, focus_context π1) t1 args1 _) := {
        | @exist (t1', args1') eq1
          with inspect (reduce_args_E RedFlags.nodelta X_type X
                                      (Γ ,,, focus_context π2) t2 args2 _) := {
          | @exist (t2', args2') eq2
            with inspect (rebuilt_ok t1' args1' ρ1 && rebuilt_ok t2' args2' ρ2) := {
            | @exist true g2 =>
              isconv_prog leq t1' (appstack args1' ρ1) t2' (appstack args2' ρ2) aux ;
            | @exist false _ =>
              no (EtaStackRefusal (Γ ,,, focus_context π1) t1 (Γ ,,, focus_context π2) t2)
            }
          }
        }
      }
    }.
  Next Obligation.
    symmetry in e1.
    pose proof (heΣ _ wfΣ); sq.
    eapply welltyped_zipc_stack_context ; eauto.
  Qed.
  Next Obligation.
    clear aux eq1.
    symmetry in e2.
    pose proof (heΣ _ wfΣ); sq.
    now eapply welltyped_zipc_stack_context ; eauto.
  Qed.
  Next Obligation.
    simpl_reduce_stack Σ wfΣ.
    pose proof (hΣ _ wfΣ); sq.
    eapply red_welltyped ; try assumption ; revgoals.
    - zip fold. eapply red_context_zip. simpl_stacks. eapply r0.
    - cbn. simpl_stacks. eauto.
  Qed.
  Next Obligation.
    simpl_reduce_stack Σ wfΣ.
    pose proof (hΣ _ wfΣ); sq.
    eapply red_welltyped ; try assumption ; revgoals.
    - zip fold. eapply red_context_zip. simpl_stacks. eapply r.
    - cbn. simpl_stacks. eauto.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ X Γ t π h) as c1
    end.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match type of eq1 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
      pose proof (reduce_stack_Req f _ X _ wfΣ _ _ _ hh) as [ e | h ]
    end.
     - assert (ee1 := eq1). rewrite e in ee1. inversion ee1. subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?X ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2 ;
        pose proof (reduce_stack_context f Σ X Γ t π h) as c2
      end.
      rewrite <- eq2 in d2. cbn in d2.
      rewrite <- eq2 in c2. cbn in c2.
      rewrite stack_context_appstack in c2. cbn in c2.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      match type of eq2 with
      | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
        pose proof (reduce_stack_Req f _ X Σ wfΣ _ _ _ hh) as [ ee | h ]
      end.
      + assert (ee2 := eq2). rewrite ee in ee2. inversion ee2. subst.
        unshelve eapply R_stateR.
        * simpl. rewrite stack_cat_appstack. red. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. constructor.
      + rewrite <- eq2 in h.
        rewrite stack_context_appstack in h.
        dependent destruction h.
        * cbn in H. rewrite zipc_appstack in H. cbn in H.
          unshelve eapply R_cored2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl.
             rewrite zipc_appstack. rewrite zipc_stack_cat.
             repeat zip fold. intros; eapply cored_context.
             erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
        * destruct y' as [q hq].
          cbn in H0. inversion H0. subst.
          unshelve eapply R_positionR2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. f_equal.
             rewrite zipc_stack_cat.
             rewrite <- H2.
             rewrite 2!zipc_appstack. cbn. reflexivity.
          -- simpl.
             unfold posR in H. cbn in H.
             rewrite stack_position_appstack in H. cbn in H.
             rewrite stack_position_stack_cat.
             rewrite stack_position_appstack.
             eapply positionR_poscat.
             assumption.
    - rewrite <- eq1 in h.
      rewrite stack_context_appstack in h.
      dependent destruction h.
      + cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply R_cored. simpl.
        rewrite zipc_appstack. rewrite zipc_stack_cat.
        repeat zip fold. intros; eapply cored_context.
        erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR ; simpl.
        * f_equal.
          rewrite zipc_stack_cat.
          rewrite <- H2.
          rewrite 2!zipc_appstack. cbn. reflexivity.
        * unfold posR in H. cbn in H.
          rewrite stack_position_appstack in H. cbn in H.
          rewrite stack_position_stack_cat.
          rewrite stack_position_appstack.
          eapply positionR_poscat.
          assumption.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    simpl_reduce_stack Σ wfΣ.
    eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    simpl_reduce_stack Σ wfΣ.
    specialize (isr0 eq_refl) as (?&?).
    split; [easy|].
    simpl_stacks.
    intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&?).
    split; [easy|].
    simpl_stacks.
    intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ), (hx _ wfΣ).
    apply -> conv_cum_red_conv_iff; eauto.
    eapply h; eauto.
  Qed.

  Opaque reduce_args_E.
  (* T4 (rev 14 B4): the push [appstack l (App_l … :: θ)] needs a stack without Eta_arg; on
     false the answer is [None] (dead on reachable states: [virt_ok_not_head]). Site 3 of the
     11 reduce_stack sites: [args := []]. *)
  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : wtp Γ (tFix mfix idx) π)
    : option (term * stack) :=

    unfold_one_fix Γ mfix idx π h with inspect (no_Eta_arg π) := {
    | @exist false _ := None ;
    | @exist true hna with inspect (unfold_fix mfix idx) := {
      | @exist (Some (arg, fn)) eq1 with inspect (decompose_stack_at π arg) := {
        | @exist (Some (l, c, θ)) eq2 with inspect (reduce_args_E RedFlags.default X_type X
                                                     (Γ ,,, stack_context θ) c [] _) := {
          | @exist (cred, args') eq3 with construct_viewc cred := {
            | view_construct ind n ui :=
              Some (fn, appstack l (App_l (mkApps (tConstruct ind n ui) args') :: θ)) ;
            | view_other cred h' := None
            }
          } ;
        | _ := None
        } ;
      | _ := None
      }
    }.
  Next Obligation.
    destruct (hΣ _ wfΣ).
    cbn. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    rewrite zipc_appstack in h. cbn in h.
    zip fold in h. specialize (h _ wfΣ). apply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_App in h as hh ; auto.
    destruct hh as [na [A' [B' [? [? ?]]]]].
    eexists. eassumption.
  Qed.
  Transparent reduce_stack.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zipp :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp fn ξ) ∥.
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; try discriminate.
    all: noconf eq.
    unfold zipp.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack θ). intros l' s' e'.
    simpl.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    constructor.
    rewrite stack_context_appstack. simpl.
    rewrite 2!mkApps_app. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    rewrite stack_context_appstack.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge; auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps; auto.
  Qed.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn ξ) ∥.
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    clear Heq1 Heq2. cbn in r1.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    do 2 zip fold. constructor. eapply red_context_zip.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite -> nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps; auto.
  Qed.

  Lemma unfold_one_fix_cored :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored (fst Σ) Γ (zipc fn ξ) (zipc (tFix mfix idx) π).
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros ; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of eq3 with
    | _ = reduce_stack ?flags _ ?X ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags _ X Σ wfΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags _ X Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    do 2 zip fold. eapply cored_context.
    eapply cored_red_trans.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite -> nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite -> decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_decompose :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof using Type.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. cbn.
    case_eq (decompose_stack θ). intros l0 s1 H2.
    reflexivity.
  Qed.

  (** A full weak-head run of the default-flag machine ([reduce_stack]) on a
      constant-headed state, in [zipp] form (design §7.3, steps 1 and 2).
      [None] when it makes no progress, that is when the application is already
      a weak-head normal form under default flags: an axiom, or an unsaturated,
      inert, stuck or rigid operation. *)
  Opaque reduce_args_E.
  (* Site 11 of the 11 reduce_stack sites: [args := (decompose_stack π).1]. Called only from
     the Const view of [_isconv_prog], under T1, which supplies [hna]. *)
  Equations unfold_one_prim (Γ : context) (c : kername) (u : Instance.t) (π : stack)
            (hna : no_Eta_arg π = true)
            (h : wtp Γ (tConst c u) π) : option (term * stack) :=
    unfold_one_prim Γ c u π hna h with inspect (decompose_stack π) := {
    | @exist (args, ρ) eqd
      with inspect (reduce_args_E RedFlags.default X_type X (Γ ,,, stack_context π)
                     (tConst c u) args _) := {
      | @exist (t', args') eqr with inspect (eqb (mkApps t' args') (mkApps (tConst c u) args)) := {
        | @exist true _ := None ;
        | @exist false _ := Some (t', appstack args' ρ)
        }
      }
    }.
  Next Obligation.
    symmetry in eqd.
    pose proof (heΣ _ wfΣ); sq.
    eapply welltyped_zipc_stack_context ; eauto.
  Qed.
  Transparent reduce_stack.

  (** The machine's facts on the [zipp]-form run: its result reduces from the
      application, has no stack tail, and is a weak-head normal form. *)
  Ltac prim_step_facts Σ wfΣ eqr :=
    match type of eqr with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
      let r := fresh "r" in let d := fresh "d" in let wh := fresh "wh" in
      pose proof (reduce_stack_sound f _ X Σ wfΣ Γ t π hh) as [r];
      pose proof (reduce_stack_decompose f _ X Γ t π hh) as d;
      pose proof (reduce_stack_whnf f _ X Γ t π hh Σ wfΣ) as wh;
      rewrite <- eqr in r, d, wh; cbn in r, d, wh
    end.

  Lemma unfold_one_prim_shape Γ c u π h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π h ->
    ∑ args ρ l,
      [× decompose_stack π = (args, ρ), ξ = appstack l ρ,
         (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
            ∥ red Σ (Γ ,,, stack_context π) (mkApps (tConst c u) args) (mkApps t' l) ∥) &
         mkApps t' l <> mkApps (tConst c u) args].
  Proof using Type.
    funelim (unfold_one_prim Γ c u π h); intros [=]; subst.
    match type of eqr with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
      pose proof (reduce_stack_decompose f _ X Γ t π hh) as d
    end.
    rewrite <- eqr in d. cbn in d.
    rewrite decompose_stack_appstack in d. cbn in d.
    destruct (decompose_stack π') as [l s] eqn:ed. cbn in d. subst s.
    apply decompose_stack_eq in ed. subst π'.
    exists args, ρ, l. split.
    - now symmetry.
    - now rewrite stack_cat_appstack.
    - intros Σ wfΣ.
      match type of eqr with
      | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?hh =>
        pose proof (reduce_stack_sound f _ X Σ wfΣ Γ t π hh) as [r']
      end.
      rewrite <- eqr in r'. cbn in r'. rewrite !zipc_appstack in r'. cbn in r'.
      constructor. exact r'.
    - intros heq.
      match goal with H : false = eqb _ _ |- _ => pose proof H as hne end.
      unfold zipp in hne. rewrite decompose_stack_appstack in hne. cbn in hne.
      rewrite app_nil_r in hne. rewrite heq in hne.
      rewrite eqb_refl in hne. discriminate hne.
  Qed.

  (** What a successful step gives a re-entry: the stack keeps its context, the
      application reduces in [zipp] and in [zipc] form, and the step is strict. *)
  Lemma unfold_one_prim_facts Γ c u π h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π h ->
    (stack_context ξ = stack_context π) ×
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
       ∥ red Σ (Γ ,,, stack_context π) (zipp (tConst c u) π) (zipp t' ξ) ∥) ×
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
       ∥ red Σ Γ (zipc (tConst c u) π) (zipc t' ξ) ∥) ×
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
       cored Σ Γ (zipc t' ξ) (zipc (tConst c u) π)).
  Proof using Type.
    intros e. destruct (unfold_one_prim_shape _ _ _ _ _ _ _ e) as (args & ρ & l & [ed -> hr hne]).
    pose proof (decompose_stack_twice _ _ _ ed) as hρ.
    apply decompose_stack_eq in ed. subst π.
    assert (ezp : forall t L, zipp t (appstack L ρ) = mkApps t L).
    { intros t L. unfold zipp. rewrite decompose_stack_appstack. rewrite hρ. cbn. now rewrite app_nil_r. }
    rewrite !ezp. rewrite !stack_context_appstack. rewrite !stack_context_appstack in hr.
    split; [reflexivity|]. split; [exact hr|].
    assert (hrc : forall Σ (wfΣ : abstract_env_ext_rel X Σ),
               ∥ red Σ Γ (zipc (tConst c u) (appstack args ρ)) (zipc t' (appstack l ρ)) ∥).
    { intros Σ wfΣ. destruct (hr _ wfΣ) as [r]. constructor.
      rewrite !zipc_appstack. eapply red_context_zip. exact r. }
    split; [exact hrc|].
    intros Σ wfΣ. destruct (hrc _ wfΣ) as [r].
    eapply red_neq_cored; [exact r|].
    rewrite !zipc_appstack. intros ez. apply zipc_inj in ez. now apply hne.
  Qed.

  Inductive prog_view : term -> term -> Type :=
  | prog_view_App u1 v1 u2 v2 :
      prog_view (tApp u1 v1) (tApp u2 v2)

  | prog_view_Const c1 u1 c2 u2 :
      prog_view (tConst c1 u1) (tConst c2 u2)

  | prog_view_Lambda na1 A1 b1 na2 A2 b2 :
      prog_view (tLambda na1 A1 b1) (tLambda na2 A2 b2)

  | prog_view_Prod na1 A1 B1 na2 A2 B2 :
      prog_view (tProd na1 A1 B1) (tProd na2 A2 B2)

  | prog_view_Case ci p c brs ci' p' c' brs' :
      prog_view (tCase ci p c brs) (tCase ci' p' c' brs')

  | prog_view_Proj p c p' c' :
      prog_view (tProj p c) (tProj p' c')

  | prog_view_Fix mfix idx mfix' idx' :
      prog_view (tFix mfix idx) (tFix mfix' idx')

  | prog_view_CoFix mfix idx mfix' idx' :
      prog_view (tCoFix mfix idx) (tCoFix mfix' idx')

  | prog_view_Prim p p' :
      prog_view (tPrim p) (tPrim p')

  | prog_view_other :
      forall u v, prog_discr u v -> prog_view u v.

  Equations prog_viewc u v : prog_view u v :=
    prog_viewc (tApp u1 v1) (tApp u2 v2) :=
      prog_view_App u1 v1 u2 v2 ;

    prog_viewc (tConst c1 u1) (tConst c2 u2) :=
      prog_view_Const c1 u1 c2 u2 ;

    prog_viewc (tLambda na1 A1 b1) (tLambda na2 A2 b2) :=
      prog_view_Lambda na1 A1 b1 na2 A2 b2 ;

    prog_viewc (tProd na1 A1 B1) (tProd na2 A2 B2) :=
      prog_view_Prod na1 A1 B1 na2 A2 B2 ;

    prog_viewc (tCase ci p c brs) (tCase ci' p' c' brs') :=
      prog_view_Case ci p c brs ci' p' c' brs' ;

    prog_viewc (tProj p c) (tProj p' c') :=
      prog_view_Proj p c p' c' ;

    prog_viewc (tFix mfix idx) (tFix mfix' idx') :=
      prog_view_Fix mfix idx mfix' idx' ;

    prog_viewc (tCoFix mfix idx) (tCoFix mfix' idx') :=
      prog_view_CoFix mfix idx mfix' idx' ;

    prog_viewc (tPrim p) (tPrim p') :=
      prog_view_Prim p p' ;

    prog_viewc u v := prog_view_other u v I.

  Definition eqb_universe_instance :=
    compare_universe_instance (abstract_env_compare_universe X Conv).

  Lemma eqb_universe_instance_spec :
    forall u v Σ (wfΣ : abstract_env_ext_rel X Σ),
      forallb (wf_universeb Σ) (map Universe.make' u) ->
      forallb (wf_universeb Σ) (map Universe.make' v) ->
      eqb_universe_instance u v ->
      cmp_universe_instance (eq_universe (global_ext_constraints Σ)) u v.
  Proof using Type.
    intros u v Σ wfΣ Hu Hv.
    eapply elimT.
    eapply reflect_reflectT, reflect_cmp_universe_instance; tea.
    intros.
    apply iff_reflect.
    eapply abstract_env_compare_universe_correct with (conv_pb := Conv); tas.
    all: now eapply wf_universe_iff.
  Qed.

  Arguments LevelSet.mem : simpl never.

  (* E form (base took [wf Σ] through heΣ and returned the instance consistency, which no
     remaining use reads): T6 through [ctf_context] and [rtf_const]. *)
  Lemma welltyped_zipc_tConst_inv Σ (wfΣ : abstract_env_ext_rel X Σ) Γ c u π :
    no_Eta_arg π ->
    welltypedE Σ Γ (zipc (tConst c u) π) ->
    exists cst, declared_constant Σ c cst.
  Proof using reduce_factsE conv_factsE.
    intros hna h.
    destruct (heΣ _ wfΣ) as [hwf].
    apply (ctf_context Σ Γ _ π hwf hna) in h.
    exact (rtf_const Σ _ c u hwf h).
  Qed.

  Lemma red_conv_cum_l {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ u v.
  Proof using Type.
    intros r. pose proof (hΣ _ wfΣ). sq. now apply red_ws_cumul_pb.
  Qed.

  Lemma red_conv_cum_r {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ v u.
  Proof using Type.
    intros r. pose proof (hΣ _ wfΣ). sq. now apply red_ws_cumul_pb_inv.
  Qed.

  Lemma closed_red_zipp {Σ Γ t u π} :
    is_open_term Γ (zipp t π) ->
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ zipp t π ⇝ zipp u π.
  Proof using Type.
    intros cltπ [clΓ clt r].
    eapply into_closed_red; tea.
    now eapply red_zipp.
  Qed.

  Ltac specialize_Σ wfΣ :=
    repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

  (** Before answering no on two constant-headed whnfs (design §7.3): a
      registered operation is run by [unfold_one_prim] (a full default-flag
      weak-head run), on the left, else on the right, as the kernel does inside
      lazy unfolding ([unfold_ref_with_args], kernel/cClosure.ml).  When
      neither side moves, the answer is no; under G7 it carries no proof (base
      justified it by [closed_red_whnf_mkApps_tConst], deleted here; [ne] is now unused). *)
  Equations(noeqns) unfold_prims (Γ : context) (leq : conv_pb)
            (c : kername) (u : Instance.t) (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tConst c u) π1)
            (c' : kername) (u' : Instance.t) (π2 : stack) (f2 : wf_stack π2)
            (h2 : wtp Γ (tConst c' u') π2)
            (ne : c <> c' \/ (c = c' /\ ~eqb_universe_instance u u'))
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Term Γ (tConst c u) π1 (tConst c' u') π2 f1 f2 h2)
    : ConversionResult (conv_term leq Γ (tConst c u) π1 (tConst c' u') π2) :=
    unfold_prims Γ leq c u π1 f1 h1 c' u' π2 f2 h2 ne hx hg hwf1 hwf2 aux
    with inspect (unfold_one_prim Γ c u π1 _ h1) := {
    | @exist (Some (t1', π1')) eqp1 := isconv_red leq t1' π1' (tConst c' u') π2 aux ;
    | @exist None eqp1 with inspect (unfold_one_prim Γ c' u' π2 _ h2) := {
      | @exist (Some (t2', π2')) eqp2 := isconv_red leq (tConst c u) π1 t2' π2' aux ;
      | @exist None eqp2 := no (NotFoundConstants c c')
      }
    }.
  (* the left side took a step: well-typed, smaller, same context *)
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1) as (_ & _ & hrc & _).
    destruct (hrc _ wfΣ) as [r]. pose proof (hΣ _ wfΣ) as [wΣ].
    pose proof (h1 _ wfΣ) as h1'. eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros Σ wfΣ.
    exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1))) Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1) as (hctx & _).
    rewrite hctx.
    match goal with hw : abstract_env_ext_rel X Σ |- _ => exact (hx _ hw) end.
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1) as (hctx & hrz & _).
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    destruct (hrz _ wfΣ) as [r].
    specialize (h _ wfΣ). rewrite hctx in h.
    pose proof (h1 _ wfΣ) as h1'. eapply welltyped_zipc_zipp in h1'; auto.
    etransitivity; [|exact h].
    eapply (red_conv_cum_l (wfΣ := wfΣ)).
    eapply into_closed_red; [exact r|fvs|fvs].
  Qed.
  (* the right side took a step *)
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2) as (_ & _ & hrc & _).
    destruct (hrc _ wfΣ) as [r]. pose proof (hΣ _ wfΣ) as [wΣ].
    pose proof (h2 _ wfΣ) as h2'. eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros Σ wfΣ.
    exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2))) Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2) as (hctx & _).
    rewrite hctx.
    match goal with hw : abstract_env_ext_rel X Σ |- _ => exact (hx _ hw) end.
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2) as (hctx & hrz & _).
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    destruct (hrz _ wfΣ) as [r].
    specialize (h _ wfΣ).
    pose proof (h2 _ wfΣ) as h2'. eapply welltyped_zipc_zipp in h2'; auto.
    etransitivity; [exact h|].
    pose proof (hx _ wfΣ) as [hx'].
    eapply conv_cum_conv_ctx; eauto.
    eapply (red_conv_cum_r (wfΣ := wfΣ)).
    eapply into_closed_red; [exact r|fvs|fvs].
  Qed.

  (** The same fire-first stage for the second [no] of design §7.3: same head
      and instance, but the argument lists are not convertible.  (G7: base's
      [herr] argument, the [~P] payload of the argument comparison that only
      justified this [no], is dropped with the payload.) *)
  Equations(noeqns) unfold_prims_args (Γ : context) (leq : conv_pb)
            (c : kername) (u : Instance.t) (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tConst c u) π1)
            (c' : kername) (u' : Instance.t) (π2 : stack) (f2 : wf_stack π2)
            (h2 : wtp Γ (tConst c' u') π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Term Γ (tConst c u) π1 (tConst c' u') π2 f1 f2 h2)
    : ConversionResult (conv_term leq Γ (tConst c u) π1 (tConst c' u') π2) :=
    unfold_prims_args Γ leq c u π1 f1 h1 c' u' π2 f2 h2 hx hg hwf1 hwf2 aux
    with inspect (unfold_one_prim Γ c u π1 _ h1) := {
    | @exist (Some (t1', π1')) eqp1 := isconv_red leq t1' π1' (tConst c' u') π2 aux ;
    | @exist None eqp1 with inspect (unfold_one_prim Γ c' u' π2 _ h2) := {
      | @exist (Some (t2', π2')) eqp2 := isconv_red leq (tConst c u) π1 t2' π2' aux ;
      | @exist None eqp2 := no (NotFoundConstant c)
      }
    }.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1) as (_ & _ & hrc & _).
    destruct (hrc _ wfΣ) as [r]. pose proof (hΣ _ wfΣ) as [wΣ].
    pose proof (h1 _ wfΣ) as h1'. eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros Σ wfΣ.
    exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1))) Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1) as (hctx & _).
    rewrite hctx.
    match goal with hw : abstract_env_ext_rel X Σ |- _ => exact (hx _ hw) end.
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp1) as (hctx & hrz & _).
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    destruct (hrz _ wfΣ) as [r].
    specialize (h _ wfΣ). rewrite hctx in h.
    pose proof (h1 _ wfΣ) as h1'. eapply welltyped_zipc_zipp in h1'; auto.
    etransitivity; [|exact h].
    eapply (red_conv_cum_l (wfΣ := wfΣ)).
    eapply into_closed_red; [exact r|fvs|fvs].
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2) as (_ & _ & hrc & _).
    destruct (hrc _ wfΣ) as [r]. pose proof (hΣ _ wfΣ) as [wΣ].
    pose proof (h2 _ wfΣ) as h2'. eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros Σ wfΣ.
    exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2))) Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2) as (hctx & _).
    rewrite hctx.
    match goal with hw : abstract_env_ext_rel X Σ |- _ => exact (hx _ hw) end.
  Qed.
  Next Obligation.
    destruct (unfold_one_prim_facts _ _ _ _ _ _ _ eqp2) as (hctx & hrz & _).
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    destruct (hrz _ wfΣ) as [r].
    specialize (h _ wfΣ).
    pose proof (h2 _ wfΣ) as h2'. eapply welltyped_zipc_zipp in h2'; auto.
    etransitivity; [exact h|].
    pose proof (hx _ wfΣ) as [hx'].
    eapply conv_cum_conv_ctx; eauto.
    eapply (red_conv_cum_r (wfΣ := wfΣ)).
    eapply into_closed_red; [exact r|fvs|fvs].
  Qed.

  Equations(noeqns) unfold_constants (Γ : context) (leq : conv_pb)
            (c : kername) (u : Instance.t) (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tConst c u) π1)
            (c' : kername) (u' : Instance.t) (π2 : stack) (f2 : wf_stack π2)
            (h2 : wtp Γ (tConst c' u') π2)
            (ne : c <> c' \/ (c = c' /\ ~eqb_universe_instance u u'))
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Term Γ (tConst c u) π1 (tConst c' u') π2 f1 f2 h2)
    : ConversionResult (conv_term leq Γ (tConst c u) π1 (tConst c' u') π2) :=

    unfold_constants Γ leq c u π1 f1 h1 c' u' π2 f2 h2 ne hx hg hwf1 hwf2 aux
    with inspect (abstract_env_lookup X c') := {
    | @exist (Some (ConstantDecl {| cst_body := Some b |})) eq1 :=
      isconv_red leq (tConst c u) π1 (subst_instance u' b) π2 aux ;
    (* Inductive or not found *)
    | @exist _ eq1 with inspect (abstract_env_lookup X c) := {
      | @exist (Some (ConstantDecl {| cst_body := Some b |})) eq2 :=
        isconv_red leq (subst_instance u b) π1
                        (tConst c' u') π2 aux ;
      (* Both bodiless or not found: a registered operation may still take a
         machine step before the answer is no (design §7.3, [unfold_prims]). *)
      | @exist _ eq2 := unfold_prims Γ leq c u π1 f1 h1 c' u' π2 f2 h2 ne hx hg hwf1 hwf2 aux
      }
    }.
(*
    Solve Obligations of unfold_constants with
  try destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
  exfalso;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try erewrite <- abstract_env_lookup_correct' in eq1; eauto ;
  try erewrite <- abstract_env_lookup_correct' in eq2; eauto ;
  try clear aux; specialize_Σ wfΣ;
  try solve
      [match goal with
       | [H: welltyped ?Σ ?Γ ?t |- _] =>
         let id := fresh in
         apply welltyped_zipc_tConst_inv in H as id; eauto;
           destruct id as (?&?&?);
           unfold declared_constant in *;
           congruence
       end].*)
  Ltac  solve_unfold_constants aux eq1 eq2 Σ wfΣ :=
  try destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
  exfalso; pose (hΣ Σ wfΣ); sq;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try erewrite <- abstract_env_lookup_correct' in eq1; eauto ;
  try erewrite <- abstract_env_lookup_correct' in eq2; eauto ;
  try unshelve eapply declared_constant_to_gen in eq1; eauto ;
  try unshelve eapply declared_constant_to_gen in eq2; eauto ;
  try clear aux; specialize_Σ wfΣ;
  solve
      [match goal with
       | [H: welltyped ?Σ ?Γ ?t |- _] =>
         let id := fresh in
         apply welltyped_zipc_tConst_inv in H as id; eauto;
           destruct id as (?&decl&?);
           unshelve eapply declared_constant_to_gen in decl; eauto;
           congruence
       end].

  Next Obligation.
    try rewrite <- wf_env_lookup_correct in eq1.
    pose proof (hΣ _ wfΣ).
    sq.
    eapply red_welltyped; try eapply h2; eauto.
    eapply red_zipc.
    eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros. eapply cored_zipc.
    eapply cored_const. erewrite abstract_env_lookup_correct'; eassumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; destruct (hΣ _ wfΣ).
    etransitivity; try eauto.
    eapply red_conv_cum_r ; try assumption.
    specialize (hx _ wfΣ).
    eapply closed_red_zipp.
    * clear aux. eapply welltyped_zipc_zipp in h2; eauto.
      eapply welltyped_is_open_term in h2.
      sq. now rewrite (All2_fold_length hx).
    * eapply into_closed_red; fvs.
      + eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
      + red in h. sq. fvs.
   Unshelve. eauto.
  Qed.
  Next Obligation.
    pose proof (hΣ _ wfΣ). sq.
    eapply red_welltyped ; [eauto|exact (h1 _ wfΣ)|..].
    eapply red_zipc.
    eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros. eapply cored_zipc.
    eapply cored_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (heΣ _ wfΣ) as [wΣ].
    etransitivity ; try eauto.
    eapply red_conv_cum_l ; try assumption.
    eapply closed_red_zipp.
    { eapply welltyped_zipc_zipp in h1; auto; fvs. }
    eapply into_closed_red; fvs.
    + eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
    + specialize (hx _ wfΣ). clear -hx wΣ. sq.  fvs.
    Unshelve. all : eauto.
  Qed.
  (* The defined constant on the left, under a right side that is not a
     constant: impossible by typing.  (The two-bodiless case is unfold_prims'.) *)
  Next Obligation.
    first [solve_unfold_constants aux eq1 eq2 Σ wfΣ | solve_unfold_constants aux eq1 eq2 Σ H].
  Defined.
  Next Obligation.
    first [solve_unfold_constants aux eq1 eq2 Σ wfΣ | solve_unfold_constants aux eq1 eq2 Σ H].
  Qed.
  Next Obligation.
    first [solve_unfold_constants aux eq1 eq2 Σ wfΣ | solve_unfold_constants aux eq1 eq2 Σ H].
  Qed.
  Next Obligation.
    first [solve_unfold_constants aux eq1 eq2 Σ wfΣ | solve_unfold_constants aux eq1 eq2 Σ H].
  Qed.
  Next Obligation.
    first [solve_unfold_constants aux eq1 eq2 Σ wfΣ | solve_unfold_constants aux eq1 eq2 Σ H].
  Qed.
  Next Obligation.
    first [solve_unfold_constants aux eq1 eq2 Σ wfΣ | solve_unfold_constants aux eq1 eq2 Σ H].
  Qed.

  (* E form: T6 through [ctf_context] and [ctf_case_brs_length]. *)
  Lemma welltyped_zipc_tCase_brs_length Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci motive discr brs π :
    no_Eta_arg π ->
    welltypedE Σ Γ (zipc (tCase ci motive discr brs) π) ->
    exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|.
  Proof using conv_factsE.
    intros hna h.
    destruct (heΣ _ wfΣ) as [hwf].
    apply (ctf_context Σ Γ _ π hwf hna) in h.
    exact (ctf_case_brs_length Σ _ ci motive discr brs hwf h).
  Qed.

  Lemma case_conv_brs_inv {Γ ci br br' p c brs1 brs2 π}
  (h : wtp Γ (tCase ci p c (brs1 ++ br :: brs2)) π)
  (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
  (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ br' :: brs2')) π')
  (hx : conv_stack_ctx Γ π π')
  (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
  (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥) :
  ∥ ∑ mdecl idecl,
    [× forall Σ (wfΣ : abstract_env_ext_rel X Σ), declared_inductive Σ ci mdecl idecl,
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_upto_names br.(bcontext) br'.(bcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| br.(bcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| br'.(bcontext)] ∥.
  Proof using Type.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (hΣ _ wfΣ) as [hΣ]. specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct hp as [hp].
    destruct h1 as [h1].
    eapply welltyped_zipc_zipp in h; auto.
    eapply welltyped_zipc_zipp in h'; auto.
    rewrite !zipp_as_mkApps in h, h'.
    destruct h as [s h]. destruct h' as [s' h'].
    eapply PCUICValidity.inversion_mkApps in h as [A [hcase _]].
    eapply PCUICValidity.inversion_mkApps in h' as [A' [hcase' _]].
    destruct hp as [].
    eapply inversion_Case in hcase as [mdecl [idecl [decli [indices [hcase _]]]]]; auto.
    eapply inversion_Case in hcase' as [mdecl' [idecl' [decli' [indices' [hcase' _]]]]]; auto.
    pose proof (decli_ := decli); pose proof (decli'_ := decli').
    unshelve eapply declared_inductive_to_gen in decli, decli'; eauto.
    destruct (declared_inductive_inj decli decli'). subst mdecl' idecl'.
    constructor.
    assert (clm' : test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
      #|pparams p'| br'.(bcontext)).
    { rewrite test_context_k_closed_on_free_vars_ctx.
      destruct hcase'.
      eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
      depelim a2. clear a1 a2.
      destruct p0 as [p0 _].
      cbn in p0.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact p0.
      rewrite <-closedn_ctx_on_free_vars.
      destruct ci. cbn.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (PCUICInstConv.closedn_ctx_cstr_branch_context (c:=(ci_ind, #|x|)) (idecl:=idecl)).
        split; auto. rewrite e; cbn. rewrite nth_error_app_ge; auto.
        now rewrite Nat.sub_diag; cbn. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
    }
    rewrite test_context_k_closed_on_free_vars_ctx.
    destruct hcase.
    eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
    depelim a2. eapply All2i_length in a1; clear a2.
    destruct p0 as [p0 _].
    destruct hcase'.
    eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
    depelim a3. eapply All2i_length in a2. clear a3.
    destruct p1 as [p1 _].
    rewrite e in e0. cbn in *.
    pose proof (All2_length h1). rewrite <- a1 in H.
    rewrite <- a2 in H. eapply app_inj_length_l in e0 as [-> eq]; auto.
    noconf eq. exists mdecl, idecl.
    split; tea.
    - intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    - eapply (wf_predicate_length_pars wf_pred).
    - eapply (wf_predicate_length_pars wf_pred0).
    - etransitivity; tea.
      now symmetry.
    - eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact p0.
      rewrite <- closedn_ctx_on_free_vars.
      destruct ci. cbn.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (PCUICInstConv.closedn_ctx_cstr_branch_context (c:=(ci_ind, #|x0|)) (idecl:=idecl)).
        split; auto. rewrite e; cbn. rewrite nth_error_app_ge; auto.
        now rewrite Nat.sub_diag; cbn. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
      Unshelve. all: eauto.
  Qed.


  Equations isconv_branches (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs1 brs2 : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c (brs1 ++ brs2)) π)
    (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ brs2')) π')
    (hx : conv_stack_ctx Γ π π')
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥)
    (aux : Aux Term Γ (tCase ci p c (brs1 ++ brs2)) π (tCase ci p' c' (brs1' ++ brs2')) π' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs2 brs2' ∥)
    by struct brs2 :=

    isconv_branches Γ ci
      p c brs1 ({| bcontext := m; bbody := br |} :: brs2) π h
      p' c' brs1' ({| bcontext := m'; bbody := br' |} :: brs2') π' h' hx hp h1 aux
     with isconv_red_raw Conv
              br (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π)
              br' (Case_branch ci p' c' (brs1', branch_hole_body m', brs2') :: π') aux := {
      | Success h2
        with isconv_branches Γ ci
              p c (brs1 ++ [{|bcontext := m; bbody := br|}]) brs2 π _
              p' c' (brs1' ++ [{| bcontext := m'; bbody := br'|}]) brs2' π' _ hx hp _ (expand aux) := {
        | Success h3 := yes ;
        | Error e := no e
        } ;
      | Error e := no e
    } ;

    isconv_branches Γ ci
      p c brs1 [] π h
      p' c' brs1' [] π' h' hx hp h1 aux := yes ;

    isconv_branches Γ ci
      p c brs1 brs2 π h
      p' c' brs1' brs2' π' h' hx hp h1 aux := False_rect _ _.
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    clear aux.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. destruct (hΣ _ wfΣ).
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
    apply welltyped_zipc_tCase_brs_length in h as (?&?&?&?); eauto.
    apply welltyped_zipc_tCase_brs_length in h' as (?&?&?&?); eauto.
    unshelve eapply declared_inductive_to_gen in H, H1; eauto.
    pose proof (PCUICInductiveInversion.declared_inductive_unique_sig H H1) as u; noconf u.
    rewrite !length_app in H0, H2.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    clear aux.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ. destruct (hΣ _ wfΣ).
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
    apply welltyped_zipc_tCase_brs_length in h as (?&?&?&?); eauto.
    apply welltyped_zipc_tCase_brs_length in h' as (?&?&?&?); eauto.
    unshelve eapply declared_inductive_to_gen in H, H1; eauto.
    pose proof (PCUICInductiveInversion.declared_inductive_unique_sig H H1) as u; noconf u.
    rewrite !length_app in H0, H2.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r.
    rewrite stack_position_cons.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    eapply case_conv_brs_inv in h1; tea.
    rename H into wfΣ; pose proof (hΣ _ wfΣ).
    specialize_Σ wfΣ.
    sq. destruct h1 as [mdecl [idecl [decli eqp eqp' eqm clm clm']]].
    transitivity (Γ ,,, stack_context π ,,, inst_case_context (pparams p') (puinst p') m').
    - unfold app_context; rewrite <-app_assoc.
      inv_on_free_vars.
      eapply inst_case_ws_cumul_ctx_pb; tea.
      * fvs.
      * fvs.
      * eapply hp.
      * eapply hp.
    - unfold app_context. rewrite <- app_assoc. eapply ws_cumul_ctx_pb_app_same; auto.
      rewrite on_free_vars_ctx_app.
      apply andb_true_iff. split; auto. 1:now apply ws_cumul_ctx_pb_closed_left in hx.
      eapply on_free_vars_ctx_inst_case_context; trea.
      destruct hp.
      now eapply (ws_cumul_pb_terms_open_terms_right a).
  Qed.
  Next Obligation.
    now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    destruct (case_conv_brs_inv h p' c' brs1' brs2' _ h') as [[mdecl [idecl [decli eqp eqp' eqm clm clm']]]]; tea.
    specialize_Σ wfΣ.
    destruct h1 as [h1], h2 as [h2].
    constructor. apply All2_app.
    - assumption.
    - constructor.
      2: now constructor.
      simpl.
      unfold zipp in h2.
      split; auto.
      cbn in h2.
      unfold inst_case_branch_context. cbn.
      now unfold app_context; rewrite app_assoc.
  Qed.
  Next Obligation.
    clear aux. unfold isconv_branches_obligations_obligation_13.
    eapply R_irrelevance. 2:tea. cbn.
    f_equal. f_equal. 2:{ f_equal. now rewrite <-app_assoc. }
    f_equal. f_equal. f_equal. now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    destruct (case_conv_brs_inv h p' c' brs1' brs2' _ h') as [[mdecl [idecl [decli eqp eqp' eqm clm clm']]]]; tea.
    specialize_Σ wfΣ.
    destruct h2 as [h2], h3 as [h3].
    constructor.
    constructor; auto.
    unfold zipp in *; simpl in *.
    split; auto.
    rewrite app_context_assoc in h2; auto.
  Qed.

  Equations isconv_branches' (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c brs) π)
    (ci' : case_info)
    (p' : predicate term) (c' : term) (brs' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci' p' c' brs') π')
    (hx : conv_stack_ctx Γ π π')
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (ei : ci = ci')
    (aux : Aux Term Γ (tCase ci p c brs) π (tCase ci' p' c' brs') π' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs brs' ∥) :=

    isconv_branches' Γ ci p c brs π h ci' p' c' brs' π' h' hx hp eci aux :=
      isconv_branches Γ ci p c [] brs π _ p' c' [] brs' π' _ _ _ _ (expand aux).
  Next Obligation.
    constructor. constructor.
  Qed.

  (* Factorise notions of fixpoints *)
  Inductive fix_kind :=
  | IndFix
  | CoIndFix.

  Definition mFix k :=
    match k with
    | IndFix => tFix
    | CoIndFix => tCoFix
    end.

  Definition mFix_mfix fk :=
    match fk with
    | IndFix => Fix
    | CoIndFix => CoFix
    end.

  Definition mFixRargMismatch fk :=
    match fk with
    | IndFix => FixRargMismatch
    | CoIndFix => CoFixRargMismatch
    end.

  Definition mFixMfixMismatch fk :=
    match fk with
    | IndFix => FixMfixMismatch
    | CoIndFix => CoFixMfixMismatch
    end.

  Equations isws_cumul_pb_fix_types (fk : fix_kind) (Γ : context)
    (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v =>
                   (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
                   (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
            ) mfix1 mfix1' ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix2 mfix2' ∥)
    by struct mfix2 :=

    isws_cumul_pb_fix_types
      fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 aux
    with inspect (eqb u.(rarg) v.(rarg)) := {
    | @exist true eq1
      with inspect (eqb_binder_annot u.(dname) v.(dname)) := {
      | @exist true eqann
        with isconv_red_raw Conv
             u.(dtype)
             (mFix_mfix fk (mfix1, def_hole_type u.(dname) u.(dbody) u.(rarg), mfix2) idx :: π)
             v.(dtype)
             (mFix_mfix fk (mfix1', def_hole_type v.(dname) v.(dbody) v.(rarg), mfix2') idx :: π')
             aux
      := {
      | Success h2 with
          isws_cumul_pb_fix_types fk Γ idx
            (mfix1 ++ [u]) mfix2 π _
            (mfix1' ++ [v]) mfix2' π' _
            hx _ (expand aux)
        := {
        | Success h3 := yes ;
        | Error e := no e
        } ;
      | Error e := no e
      } ;
      | @exist false neqann := no (
        FixRargMismatch idx
          (Γ ,,, stack_context π) u mfix1 mfix2
          (Γ ,,, stack_context π') v mfix1' mfix2'
      ) };
    | @exist false eq1 := no (
        mFixRargMismatch fk idx
          (Γ ,,, stack_context π) u mfix1 mfix2
          (Γ ,,, stack_context π') v mfix1' mfix2'
      )
    } ;

    isws_cumul_pb_fix_types fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 aux := yes ;

    (* TODO It might be more efficient to check the lengths first
       and then conclude this case is not possible.
    *)
    isws_cumul_pb_fix_types fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 aux :=
      no (
        mFixMfixMismatch fk idx
          (Γ ,,, stack_context π) (mfix1 ++ mfix2)
          (Γ ,,, stack_context π') (mfix1' ++ mfix2')
      ).

  Next Obligation.
    destruct u. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    destruct v. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    - destruct u. destruct fk. all: reflexivity.
    - rewrite <- app_nil_r, stack_position_cons. destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct fk.
    - simpl. eauto.
    - simpl. eauto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2.
    constructor.
    apply All2_app. 1: assumption.
    constructor. 2: constructor.
    change (true = eqb u.(rarg) v.(rarg)) in eq1.
    destruct (eqb_specT u.(rarg) v.(rarg)). 2: discriminate.
    symmetry in eqann.
    apply eqb_binder_annot_spec in eqann.
    split; auto.
    destruct fk; simpl in *; auto.
    all: intros; erewrite (abstract_env_ext_irr _ _ wfΣ); intuition eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    clear aux.
    eapply R_irrelevance; tea; cbn.
    now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2. sq.
    constructor.
    2: eauto.
    change (true = eqb u.(rarg) v.(rarg)) in eq1.
    destruct (eqb_specT u.(rarg) v.(rarg)). 2: discriminate.
    symmetry in eqann.
    apply eqb_binder_annot_spec in eqann.
    clear eq1.
    destruct fk.
    all: split; [ intros; erewrite (abstract_env_ext_irr _ _ wfΣ) | ]; intuition eauto .
    Unshelve. all: eauto.
  Qed.

  Lemma stack_entry_context_mFix_mfix_bd :
    forall fk na ty ra mfix1 mfix2 idx,
      stack_entry_context (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx) =
      fix_context_alt (map def_sig mfix1 ++ (na,ty) :: map def_sig mfix2).
  Proof using Type.
    intros fk na ty ra mfix1 mfix2 idx.
    destruct fk. all: reflexivity.
  Qed.

  Equations isws_cumul_pb_fix_bodies (fk : fix_kind) (Γ : context) (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix1 mfix1' ∥)
    (ha : ∥ All2 (fun u v =>
                    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
                    (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
           ) (mfix1 ++ mfix2) (mfix1' ++ mfix2') ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix2 mfix2' ∥)
    by struct mfix2 :=

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 ha aux
  with isconv_red_raw Conv
        u.(dbody)
        (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π)
        v.(dbody)
        (mFix_mfix fk (mfix1', def_hole_body v.(dname) v.(dtype) v.(rarg), mfix2') idx :: π')
        aux
  := {
  | Success h2
    with isws_cumul_pb_fix_bodies fk Γ idx
           (mfix1 ++ [u]) mfix2 π _
           (mfix1' ++ [v]) mfix2' π' _
           hx _ _ (expand aux)
    := {
    | Success h3 := yes ;
    | Error e := no e
    } ;
  | Error e := no e
  } ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 ha aux := yes ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 ha aux :=
    False_rect _ _.

  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !length_app in ea. simpl in ea. lia.
  Qed.
  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !length_app in ea. simpl in ea. lia.
  Qed.
  Next Obligation.
    destruct u. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    destruct v. destruct fk. all: eauto.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    - destruct u. destruct fk. all: reflexivity.
    - rewrite <- app_nil_r, stack_position_cons.
      destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _  wfΣ) as [wΣ], ha as [ha], hx as [hx].
    clear - wfΣ wΣ ha hx. constructor.
    rewrite 2!stack_entry_context_mFix_mfix_bd.
    change (dname u, dtype u) with (def_sig u).
    change (dname v, dtype v) with (def_sig v).
    repeat match goal with
    | |- context [ ?f ?x :: map ?f ?l ] =>
      change (f x :: map f l) with (map f (x :: l))
    end.
    rewrite <- 2!map_app.
    revert ha.
    generalize (mfix1 ++ u :: mfix2). intro Δ.
    generalize (mfix1' ++ v :: mfix2'). intro Δ'.
    intro ha.
    rewrite !app_context_assoc.
    revert hx ha.
    generalize (Γ ,,, stack_context π').
    generalize (Γ ,,, stack_context π).
    clear Γ. intros Γ Γ' hx ha.
    assert (h :
      All2
        (fun d d' => (Σ ;;; Γ ⊢ d.2 = d'.2) * eq_binder_annot d.1 d'.1)
        (map def_sig Δ) (map def_sig Δ')
    ).
    { apply All2_map. eapply All2_impl. 1: eassumption.
      intros [na ty bo ra] [na' ty' bo' ra'] [? [? ?]].
      specialize (w _ wfΣ). simpl in *. split; tas.
    }
    clear ha.
    revert h.
    generalize (map def_sig Δ). clear Δ. intro Δ.
    generalize (map def_sig Δ'). clear Δ'. intro Δ'.
    intro h.
    unfold fix_context_alt.
    match goal with
    | |- ws_cumul_ctx_pb _ _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') =>
      assert (hi :
        All2i (fun i d d' =>
          forall Ξ,
            is_closed_context (Γ ,,, Ξ) ->
            #|Ξ| = i ->
            ws_cumul_decls Conv Σ (Γ ,,, Ξ) d d'
        ) 0 l l'
      )
    end.
    { eapply All2i_mapi.
      generalize 0 at 3. intro n.
      induction h in n |- *. 1: constructor.
      constructor. 2: eapply IHh.
      destruct r.
      intros Ξ cl eΞ. constructor; tas.
      rewrite <- eΞ.
      eapply @weakening_ws_cumul_pb with (Γ' := []). all: try assumption.

    }
    clear h.
    revert hi.
    match goal with
    | |- context [ ws_cumul_ctx_pb _ _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') ] =>
      generalize l' ;
      generalize l
    end.
    clear Δ Δ'. intros Δ Δ' h.
    apply All2i_rev in h. simpl in h.
    revert h.
    rewrite <- (List.length_rev Δ).
    generalize (List.rev Δ). clear Δ. intro Δ.
    generalize (List.rev Δ'). clear Δ'. intro Δ'.
    intro h.
    set (ln := #|Δ|) in *.
    set (m := 0) in *.
    assert (e : ln - m = #|Δ|) by lia.
    clearbody ln m.
    induction h.
    - eauto.
    - simpl in *.
      forward IHh by lia.
      constructor.
      + eapply IHh.
      + eapply r0. 2:lia.
        clear - wΣ IHh. fvs.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2], ha as [ha].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2. (* simpl in h2. *)
    constructor.
    apply All2_app.
    - eapply All2_impl. 1: exact h1.
      simpl. intros [? ? ? ?] [? ? ? ?] hh.
      simpl in *.
      rewrite map_app. simpl.
      rewrite <- !app_assoc. simpl.
      assumption.
    - constructor. 2: constructor.
      rewrite map_app. simpl.
      rewrite <- !app_assoc. simpl.
      destruct u as [na ty bo ra], v as [na' ty' bo' ra']. simpl in *.
      unfold def_sig at 2. simpl.
      destruct fk.
      + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.
       + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct ha as [ha].
    constructor.
    rewrite <- !app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    clear aux.
    eapply R_irrelevance; tea; cbn.
    now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    specialize_Σ wfΣ.
    destruct hx as [hx], h1 as [h1], h2 as [h2], h3 as [h3].
    destruct (hΣ _ wfΣ) as [wΣ].
    unfold zipp in h2. simpl in h2.
    constructor.
    constructor.
    - destruct u as [na ty bo ra], v as [na' ty' bo' ra']. simpl in *.
      unfold def_sig at 2. simpl.
      destruct fk.
      + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.
      + intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
       rewrite app_context_assoc in h2; eauto.

    - eapply All2_impl. 1: exact h3.
      simpl. intros [? ? ? ?] [? ? ? ?] hh.
      simpl in *.
      rewrite map_app in hh. simpl in hh.
      rewrite <- !app_assoc in hh. simpl in hh.
      assumption.
    Unshelve. all: eauto.
  Qed.

  Equations isws_cumul_pb_Fix (fk : fix_kind) (Γ : context)
    (mfix : mfixpoint term) (idx : nat) (π : stack)
    (h : wtp Γ (mFix fk mfix idx) π)
    (mfix' : mfixpoint term) (idx' : nat) (π' : stack)
    (h' : wtp Γ (mFix fk mfix' idx') π')
    (hx : conv_stack_ctx Γ π π')
    (ei : idx = idx')
    (aux : Aux Term Γ (mFix fk mfix idx) π (mFix fk mfix' idx') π' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context mfix ⊢ u.(dbody) = v.(dbody)) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ∥) :=

      isws_cumul_pb_Fix fk Γ mfix idx π h mfix' idx' π' h' hx ei aux
    with
      isws_cumul_pb_fix_types fk Γ idx
        [] mfix π _
        [] mfix' π' _
        hx _ (expand aux)
    := {
    | Success h1
      with
        isws_cumul_pb_fix_bodies fk Γ idx
          [] mfix π _
          [] mfix' π' _
          hx _ _ (expand aux)
      := {
      | Success h2 := yes ;
      | Error e := no e
      } ;
    | Error e := no e
    }.

  Next Obligation.
    destruct h1 as [h1], h2 as [h2].
    constructor.
    rewrite fix_context_fix_context_alt.
    pose proof (All2_mix h1 h2) as h3.
    eapply All2_impl. 1: exact h3.
    intros [? ? ? ?] [? ? ? ?] ?. simpl in *.
    intuition eauto.
  Qed.

  Definition compare_global_instance_correct {Σ}
    (wfΣ : abstract_env_ext_rel X Σ) pb ref n l l' :
      wf_instance Σ l ->
      wf_instance Σ l' ->
      cmp_global_instance Σ (compare_universe Σ) pb ref n l l' <->
      abstract_env_compare_global_instance pb ref n l l'.
  Proof.
    intros hl hl'. apply reflect_iff. eapply reflect_cmp_global_instance; eauto.
    all: try rewrite -> wf_universeb_instance_forall.
    - intros ? ? Hu Hu'; apply iff_reflect; apply (abstract_env_compare_universe_correct _ wfΣ).
      all: now apply wf_universe_iff.
    - intros ? ? Hu Hu'; apply iff_reflect; apply (abstract_env_compare_universe_correct _ wfΣ).
      all: now apply wf_universe_iff.
    - intros; now eapply abstract_env_lookup_correct'.
    - revert hl. apply reflect_iff, wf_instanceP.
    - revert hl'. apply reflect_iff, wf_instanceP.
  Qed.

  Lemma cmpb_term_correct Σ (wfΣ : abstract_env_ext_rel X Σ) pb napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    cmpb_term_napp pb napp t u <~>
    compare_term_napp Σ Σ pb napp t u.
  Proof.
    intros ht hu.
    eassert _ as H.
    2: split; [eapply elimT|eapply introT]; apply H.
    eapply reflect_eq_term_upto_univ; tea.
    1,2: intros ????; apply iff_reflect, abstract_env_compare_universe_correct; tea; now apply wf_universe_iff.
    1,2: intros ????; apply iff_reflect, abstract_env_compare_sort_correct; tea; now apply wf_sort_iff.
    1,2: intros ??????; apply iff_reflect, compare_global_instance_correct; tea.
    all: rewrite -> wf_universeb_instance_forall in *; now eapply wf_instance_iff.
  Qed.

  (* Base [welltyped_zipp_inv]/[welltyped_zipc_inv]/[welltyped_wf] took [wf Σ], which the E
     environment does not give (wfE does not imply wf). E forms: the stack inversion is the
     named hypothesis [ctf_context] (T6), stated with "π has no Eta_arg" (every use is under
     T1); well-formed universes of an E-typed term is the named hypothesis
     [ctf_wf_universes] (T-row). Both are fields of [ConvTypedFacts welltypedE wf_extE]. *)
  Lemma welltyped_zipc_inv Σ Γ t π : wf_extE Σ -> no_Eta_arg π ->
    welltypedE Σ Γ (zipc t π) -> welltypedE Σ (Γ,,, stack_context π) t.
  Proof using conv_factsE.
    intros hwf hna Ht. exact (ctf_context Σ Γ t π hwf hna Ht).
  Qed.

  Lemma welltyped_wf Σ Γ t : wf_extE Σ -> welltypedE Σ Γ t -> wf_universes Σ t.
  Proof using conv_factsE.
    intros hwf Ht. exact (ctf_wf_universes Σ Γ t hwf Ht).
  Qed.

  Equations (noeqns) isconv_predicate_params_aux
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : p1.(pparams) = pre1 ++ post1)
            (eq2 : p2.(pparams) = pre2 ++ post2) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π1) post1 post2∥) :=
    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2
      hx aux pre1 pre2 [] [] eq1 eq2 => yes;

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2
      hx aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
      with isconv_red_raw
           Conv
           t1 (Case_pred
                 ci1
                 (pred_hole_params pre1 post1 p1.(puinst) p1.(pcontext) p1.(preturn))
                 c1 brs1 :: π1)
           t2 (Case_pred
                 ci2
                 (pred_hole_params pre2 post2 p2.(puinst) p2.(pcontext) p2.(preturn))
                 c2 brs2 :: π2) aux := {

      | Error ce => no ce;

      | Success conv_tm
          with isconv_predicate_params_aux
               Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {

        | Error ce => no ce;

        | Success conv_rest => yes
        }
      };

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux
      pre1 pre2 post1 post2 eq eq2 => no (CasePredParamsUnequalLength
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2).
  Next Obligation.
    destruct p1; auto.
  Qed.
  Next Obligation.
    destruct p2; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct p1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    specialize_Σ wfΣ.
    destruct conv_tm, conv_rest.
    unfold zipp in X; simpl in *.
    constructor; constructor; auto.
  Qed.

  Lemma case_conv_preds_inv Σ (wfΣ : abstract_env_ext_rel X Σ) {Γ ci p c brs brs' π}
  (h : wtp Γ (tCase ci p c brs) π)
  (p' : predicate term) (c' : term)
  (π' : stack) (h' : wtp Γ (tCase ci p' c' brs') π')
  (hx : conv_stack_ctx Γ π π')
  (hp : ∥ ws_cumul_pb_terms Σ (Γ,,, stack_context π) (pparams p) (pparams p') ∥) :
  ∥ ∑ mdecl idecl,
    [× declared_inductive Σ ci mdecl idecl,
      forallb (wf_universeb Σ) (map Universe.make' (puinst p)),
      forallb (wf_universeb Σ) (map Universe.make' (puinst p')),
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_upto_names p.(pcontext) p'.(pcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| p.(pcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| p'.(pcontext)] ∥.
  Proof using Type.
    destruct (hΣ _ wfΣ). specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct hp as [hp].
    eapply welltyped_zipc_zipp in h; auto.
    eapply welltyped_zipc_zipp in h'; auto.
    rewrite !zipp_as_mkApps in h, h'.
    destruct h as [s h]. destruct h' as [s' h'].
    eapply PCUICValidity.inversion_mkApps in h as [A [hcase _]].
    eapply PCUICValidity.inversion_mkApps in h' as [A' [hcase' _]].
    eapply inversion_Case in hcase as [mdecl [idecl [decli [indices [hcase _]]]]]; auto.
    eapply inversion_Case in hcase' as [mdecl' [idecl' [decli' [indices' [hcase' _]]]]]; auto.
    pose proof (decli_ := decli); pose proof (decli'_ := decli').
    unshelve eapply declared_inductive_to_gen in decli, decli'; eauto.
    destruct (declared_inductive_inj decli decli'). subst mdecl' idecl'.
    constructor.
    assert (clp : test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
      #|pparams p| p.(pcontext)).
    { rewrite test_context_k_closed_on_free_vars_ctx.
      destruct hcase.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact conv_pctx.
      rewrite <- closedn_ctx_on_free_vars.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (closed_ind_predicate_context); tea.
        eapply declared_minductive_closed; tea. exact decli'_. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
    }
    rewrite test_context_k_closed_on_free_vars_ctx.
    exists mdecl, idecl.
    destruct hcase. destruct hcase'.
    split; tea.
    - eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
      intros; apply wf_universe_iff; eauto.
    - eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
      intros; apply wf_universe_iff; eauto.
    - eapply (wf_predicate_length_pars wf_pred).
    - eapply (wf_predicate_length_pars wf_pred0).
    - etransitivity; tea.
      now symmetry.
    - now rewrite <- test_context_k_closed_on_free_vars_ctx.
    - rewrite test_context_k_closed_on_free_vars_ctx.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact conv_pctx0.
      rewrite <- closedn_ctx_on_free_vars.
      relativize #|pparams p'|.
      { eapply (closed_ind_predicate_context); tea.
        eapply declared_minductive_closed; tea. exact decli'_. }
      rewrite (wf_predicate_length_pars wf_pred0).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli_).
  Qed.

  Definition isconv_predicate_params
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2) :=
    isconv_predicate_params_aux Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux [] []
                                p1.(pparams) p2.(pparams) eq_refl eq_refl.

  Equations (noeqns) isconv_predicate
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (eqci : ci1 = ci2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2)
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_predicate Σ (Γ,,, stack_context π1) p1 p2∥) :=

    isconv_predicate Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx eqci aux
      with isconv_predicate_params
           Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux := {

      | Error ce => no ce;

      | Success conv_params
        with inspect (eqb_universe_instance p1.(puinst) p2.(puinst)) := {

        | exist false not_eq_insts => no (CasePredUnequalUniverseInstances
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2);

        | exist true eq_insts
            with isconv_red_raw
                 Conv p1.(preturn)
                      (Case_pred ci1 (pred_hole_return p1.(pparams) p1.(puinst) p1.(pcontext))
                                 c1 brs1 :: π1)
                      p2.(preturn)
                      (Case_pred ci2 (pred_hole_return p2.(pparams) p2.(puinst) p2.(pcontext))
                                 c2 brs2 :: π2)
                      aux := {

            | Error ce => no ce;

            | Success conv_ret => yes
          }
        }
      }.
  Next Obligation.
    destruct p1; cbn in *; subst; auto.
  Qed.
  Next Obligation.
    destruct p2; cbn in *; subst; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct p1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ).
    eapply eq_sym, eqb_universe_instance_spec in eq_insts; eauto.
    - destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params _ wfΣ)) as []; tea.
      specialize_Σ wfΣ.    destruct hx as [hx].
    destruct conv_params as [conv_params].
    constructor.
    unfold app_context; rewrite <- !app_assoc.
    destruct X1 as [mdecl [idecl []]].
    etransitivity.
    * inv_on_free_vars. eapply (inst_case_ws_cumul_ctx_pb d e e0 i1 i2); tea. fvs.
    * eapply ws_cumul_ctx_pb_app_same. 2:eapply hx.
      rewrite on_free_vars_ctx_app.
      apply andb_true_iff. split; auto.
      1:now eapply ws_cumul_ctx_pb_closed_left in hx.
      eapply on_free_vars_ctx_inst_case_context; trea.
      fvs.
     - destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params Σ wfΣ)) as []; tea.
       destruct X1 as [mdecl [idecl []]]. eauto.
     - destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params Σ wfΣ)) as []; tea.
       destruct X1 as [mdecl [idecl []]]. eauto.
  Qed.
  Next Obligation.
    unfold zipp in conv_ret; simpl in conv_ret.
    destruct (case_conv_preds_inv _ wfΣ h1 _ _ _ h2 hx (conv_params Σ wfΣ)) as []; tea.
    eapply eq_sym, eqb_universe_instance_spec in eq_insts; eauto.
    - specialize_Σ wfΣ. destruct hx as [hx]. destruct conv_params as [conv_params].
    destruct conv_ret as [h].
    split. split; auto.
    2:rewrite app_context_assoc in h; auto.
    now destruct X0 as [mdecl [idecl []]].
    - now destruct X0 as [mdecl [idecl []]].
    - now destruct X0 as [mdecl [idecl []]].
  Qed.

Notation tPrimArray a := (tPrim (primArray; primArrayModel a)).

Equations (noeqns) isconv_array_values_aux
            (Γ : context)
            (a1 : array_model term)
            (π1 : stack)
            (h1 : wtp Γ (tPrimArray a1) π1)
            (a2 : array_model term)
            (π2 : stack)
            (h2 : wtp Γ (tPrimArray a2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tPrimArray a1) π1 (tPrimArray a2) π2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : a1.(array_value) = pre1 ++ post1)
            (eq2 : a2.(array_value) = pre2 ++ post2) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π1) post1 post2∥) :=
    isconv_array_values_aux
      Γ a1 π1 h1 a2 π2 h2
      hx aux pre1 pre2 [] [] eq1 eq2 => yes;

    isconv_array_values_aux
      Γ a1 π1 h1 a2 π2 h2
      hx aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
      with isconv_red_raw
           Conv
           t1 (PrimArray_val a1.(array_level)
                pre1 post1
                a1.(array_default) a1.(array_type) :: π1)
           t2 (PrimArray_val a2.(array_level)
                pre2 post2
                a2.(array_default) a2.(array_type) :: π2) aux := {

      | Error ce => no ce;

      | Success conv_tm
          with isconv_array_values_aux
               Γ a1 π1 h1 a2 π2 h2 hx aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {

        | Error ce => no ce;

        | Success conv_rest => yes
        }
      };

    isconv_array_values_aux
      Γ a1 π1 h1 a2 π2 h2 hx aux
      pre1 pre2 post1 post2 eq eq2 => no (ArrayValuesNotSameLength
                                            (Γ,,, stack_context π1) a1
                                            (Γ,,, stack_context π2) a2).
  Next Obligation.
    destruct a1; auto.
  Qed.
  Next Obligation.
    destruct a2; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct a1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    specialize_Σ wfΣ.
    destruct conv_tm, conv_rest.
    unfold zipp in X; simpl in *.
    constructor; constructor; auto.
  Qed.

  Definition isconv_array_values
    (Γ : context)
    (a1 : array_model term)
    (π1 : stack)
    (h1 : wtp Γ (tPrimArray a1) π1)
    (a2 : array_model term)
    (π2 : stack)
    (h2 : wtp Γ (tPrimArray a2) π2)
    (hx : conv_stack_ctx Γ π1 π2)
    (aux : Aux Term Γ (tPrimArray a1) π1 (tPrimArray a2) π2 h2) :=
    isconv_array_values_aux Γ a1 π1 h1 a2 π2 h2 hx aux [] [] a1.(array_value) a2.(array_value) eq_refl eq_refl.

  (* See https://github.com/coq/coq/blob/master/kernel/reduction.ml#L367 *)
  (* T1 (rev 14 B4): every view except [prog_view_other] needs both stacks without Eta_arg; the
     equation [hg] is passed to the helper Equations. On false: the deliberate refusal point. *)
  Opaque reduce_args_E.
  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hv1 : virt_ok t1 π1 = true) (hv2 : virt_ok t2 π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (ir1 : isred_full Γ t1 π1) (ir2 : isred_full Γ t2 π2)
            (aux : Aux Term Γ t1 π1 t2 π2 f1 f2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=

    _isconv_prog Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2 ir1 ir2 aux
    with inspect (no_Eta_arg π1 && no_Eta_arg π2) := {
    | @exist false _ with prog_viewc t1 t2 := {
      | prog_view_other t1 t2 h := isconv_fallback leq t1 π1 t2 π2 aux ;
      | _ := no (EtaStackRefusal (Γ ,,, focus_context π1) t1 (Γ ,,, focus_context π2) t2)
      } ;
    | @exist true hg with prog_viewc t1 t2 := {
    | prog_view_App _ _ _ _ := False_rect _ _;

    | prog_view_Const c u c' u' with eq_dec c c' := {
      | left eq1 with inspect (eqb_universe_instance u u') := {
        | @exist true eq2 with isconv_args_raw leq (tConst c u) π1 (tConst c' u') π2 aux := {
          | Success h := yes ;
          (* Unfold both constants at once *)
          | Error e with inspect (abstract_env_lookup X c) := {
            | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq3 :=
              isconv_red leq (subst_instance u body) π1
                             (subst_instance u' body) π2 aux ;
            (* Bodiless, inductive or not found: a registered operation may
               still take a machine step before the answer is no (§7.3). *)
            | @exist _ _ := unfold_prims_args Γ leq c u π1 f1 h1 c' u' π2 f2 h2 hx hg hwf1 hwf2 aux
            }
          } ;
        (* If universes are different, we unfold one of the constants *)
        | @exist false uneq_u := unfold_constants Γ leq c u π1 f1 h1 c' u' π2 f2 h2 _ hx hg hwf1 hwf2 aux
        } ;
      (* If the two constants are different, we unfold one of them *)
      | right uneq_c := unfold_constants Γ leq c u π1 f1 h1 c' u' π2 f2 h2 _ hx hg hwf1 hwf2 aux
      } ;

    | prog_view_Lambda na A1 t1 na' A2 t2
      with isconv_red_raw Conv A1 (Lambda_ty na t1 :: π1)
                               A2 (Lambda_ty na' t2 :: π2) aux := {
      | Success h with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red Conv
                     t1 (Lambda_bd na A1 :: π1)
                     t2 (Lambda_bd na' A2 :: π2) aux ;
        | exist false e :=
          no (
            LambdaNotConvertibleAnn
              (Γ ,,, stack_context π1) na A1 t1
              (Γ ,,, stack_context π2) na' A2 t2
          ) };
      | Error e :=
        no (
          LambdaNotConvertibleTypes
            (Γ ,,, stack_context π1) na A1 t1
            (Γ ,,, stack_context π2) na' A2 t2 e
        )
      } ;

    | prog_view_Prod na A1 B1 na' A2 B2
      with isconv_red_raw Conv A1 (Prod_l na B1 :: π1) A2 (Prod_l na' B2 :: π2) aux := {
      | Success h  with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red leq
                   B1 (Prod_r na A1 :: π1)
                   B2 (Prod_r na' A2 :: π2) aux ;
        | exist false e :=
          no (
            ProdNotConvertibleAnn
              (Γ ,,, stack_context π1) na A1 B1
              (Γ ,,, stack_context π2) na' A2 B2
          ) };
      | Error e :=
        no (
          ProdNotConvertibleDomains
            (Γ ,,, stack_context π1) na A1 B1
            (Γ ,,, stack_context π2) na' A2 B2 e
        )
      } ;

    | prog_view_Case ci p c brs ci' p' c' brs'
      with inspect (reduce_termE RedFlags.default (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq2 with inspect (reduce_termE RedFlags.default (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq3 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb ci ci') := {
              | @exist true eq5
                  with isconv_predicate Γ ci p c brs π1 f1 _ ci' p' c' brs' π2 f2 _ hx hg hwf1 hwf2 _ aux := {
                | Success convp with isconv_red_raw Conv
                                  c (Case_discr ci p brs :: π1)
                                  c' (Case_discr ci' p' brs' :: π2) aux := {
                  | Success convdiscr with isconv_branches' Γ ci p c brs π1 f1 _ ci' p' c' brs' π2 f2 _ hx hg hwf1 hwf2 _ _ aux := {
                    | Success convbrs with isconv_args_raw leq (tCase ci p c brs) π1 (tCase ci' p' c' brs') π2 aux := {
                      | Success convargs := yes ;
                      | Error e := no e
                      } ;
                    | Error e := no e
                    } ;
                  | Error e := no e
                  } ;
                | Error e := no e
                } ;
              | @exist false eq5 :=
                no (
                  CaseOnDifferentInd
                    (Γ ,,, stack_context π1) ci p c brs
                    (Γ ,,, stack_context π2) ci' p' c' brs'
                )
              } ;
            | @exist false eq4 :=
              isconv_red leq
                (tCase ci p c brs) π1
                (tCase ci' p' cred' brs') π2
                aux
            }
          } ;
        | @exist false eq3 :=
          isconv_red leq
            (tCase ci p cred brs) π1
            (tCase ci' p' c' brs') π2
            aux
        }
      } ;

    | prog_view_Proj p c p' c' with inspect (reduce_termE RedFlags.default (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq3 with inspect (reduce_termE RedFlags.default (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq2 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb p p') := {
              | @exist true eq5 with isconv_red_raw Conv c (Proj p :: π1) c' (Proj p' :: π2) aux := {
                | Success convdiscr := isconv_args leq (tProj p c) π1 (tProj p' c') π2 aux ;
                | Error e := no e
                } ;
              | @exist false eq5 :=
                no (
                  DistinctStuckProj
                    (Γ ,,, stack_context π1) p c
                    (Γ ,,, stack_context π2) p' c'
                )
              } ;
            | @exist false eq4 :=
              isconv_red leq
                (tProj p c) π1
                (tProj p' cred') π2
                aux
          }
        } ;
        | @exist false eq3 :=
          isconv_red leq
            (tProj p cred) π1
            (tProj p' c') π2
            aux
      }
    } ;
    | prog_view_Fix mfix idx mfix' idx'
      with inspect (unfold_one_fix Γ mfix idx π1 _) := {
      | @exist (Some (fn, θ)) eq1 with inspect (decompose_stack θ) := {
        | @exist (l', θ') eq2
          with inspect (reduce_args_E RedFlags.nodelta X_type X (Γ ,,, stack_context θ') fn l' _) := {
          | @exist (fn', args') eq3 with inspect (rebuilt_ok fn' args' θ') := {
            | @exist true g3 := isconv_prog leq fn' (appstack args' θ') (tFix mfix' idx') π2 aux ;
            | @exist false _ := no (EtaStackRefusal (Γ ,,, stack_context π1) (tFix mfix idx)
                                                    (Γ ,,, stack_context π2) (tFix mfix' idx'))
            }
          }
        } ;
      | @exist None eee with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
        | @exist (Some (fn, θ)) eq1
          with inspect (decompose_stack θ) := {
          | @exist (l', θ') eq2
            with inspect (reduce_args_E RedFlags.nodelta X_type X (Γ ,,, stack_context θ') fn l' _) := {
            | @exist (fn', args') eq3 with inspect (rebuilt_ok fn' args' θ') := {
              | @exist true g3 := isconv_prog leq (tFix mfix idx) π1 fn' (appstack args' θ') aux ;
              | @exist false _ := no (EtaStackRefusal (Γ ,,, stack_context π1) (tFix mfix idx)
                                                      (Γ ,,, stack_context π2) (tFix mfix' idx'))
              }
            }
          } ;
        | @exist None eq1 with inspect (eqb idx idx') := {
          | @exist true eq4 with isws_cumul_pb_Fix IndFix Γ mfix idx π1 f1 _ mfix' idx' π2 f2 _ hx hg hwf1 hwf2 _ aux := {
            | Success convfix with isconv_args_raw leq (tFix mfix idx) π1 (tFix mfix' idx') π2 aux := {
              | Success convargs := yes ;
              | Error e := no e
              } ;
            | Error e := no e
            } ;
          | @exist false idx_uneq :=
            no (
              CannotUnfoldFix
                (Γ ,,, stack_context π1) mfix idx
                (Γ ,,, stack_context π2) mfix' idx'
            )
          }
        }
      } ;

    | prog_view_CoFix mfix idx mfix' idx'
      with inspect (eqb idx idx') := {
      | @exist true eq4 with isws_cumul_pb_Fix CoIndFix Γ mfix idx π1 f1 _ mfix' idx' π2 f2 _ hx hg hwf1 hwf2 _ aux := {
        | Success convfix with isconv_args_raw leq (tCoFix mfix idx) π1 (tCoFix mfix' idx') π2 aux := {
          | Success convargs := yes ;
          | Error e := no e
          } ;
        | Error e := no e
        } ;
      | @exist false idx_uneq :=
        no (
          DistinctCoFix
            (Γ ,,, stack_context π1) mfix idx
            (Γ ,,, stack_context π2) mfix' idx'
        )
      } ;

    | prog_view_Prim p p' with eq_dec (prim_val_tag p) (prim_val_tag p') := {
      | right tag_uneq := no (DistinctPrimTags (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p')
      | left eqtag with p, p' := {
        | (primInt; primIntModel i) | (primInt; primIntModel i') with inspect (eqb i i') :=
          { | @exist true eqi := yes
            | @exist false neqi := no (DistinctPrimValues (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p') }
        | (primFloat; primFloatModel f) | (primFloat; primFloatModel f') with inspect (eqb f f') :=
          { | @exist true eqf := yes
            | @exist false neqf := no (DistinctPrimValues (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p') }
        | (primString; primStringModel f) | (primString; primStringModel f') with inspect (eqb f f') :=
          { | @exist true eqf := yes
            | @exist false neqf := no (DistinctPrimValues (Γ ,,, stack_context π1) p (Γ ,,, stack_context π2) p') }
        | (primArray; primArrayModel a) | (primArray; primArrayModel a')
          with inspect (abstract_env_compare_universe X Conv (Universe.make' (array_level a)) (Universe.make' (array_level a'))) :=
          { | @exist false neql := no (ArrayNotConvertibleLevels (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a')
            | @exist true eql with isconv_red_raw Conv (array_type a) (PrimArray_ty a.(array_level) a.(array_value) a.(array_default) :: π1)
                (array_type a') (PrimArray_ty a'.(array_level) a'.(array_value) a'.(array_default) :: π2) aux := {
              | Success convdiscrty with isconv_red_raw Conv (array_default a) (PrimArray_def a.(array_level) a.(array_value) a.(array_type) :: π1)
                  (array_default a') (PrimArray_def a'.(array_level) a'.(array_value) a'.(array_type) :: π2) aux := {
                | Success convdiscrdef with isconv_array_values Γ a π1 f1 _ a' π2 f2 _ hx hg hwf1 hwf2 aux := {
                  | Success convdiscrval := yes
                  | Error e := no (ArrayNotConvertibleValues (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a' e)
                }
                | Error e := no (ArrayNotConvertibleDefault (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a' e)
              } ;
            | Error e := no (ArrayNotConvertibleTypes (Γ ,,, stack_context π1) a (Γ ,,, stack_context π2) a' e)
            }
          }
        }
    } ;

    | prog_view_other t1 t2 h :=
      isconv_fallback leq t1 π1 t2 π2 aux
    } }.

  (* tApp *)
  Next Obligation.
    destruct ir1 as [ha1 _]. discriminate ha1.
  Qed.

  (* tConst *)
  Next Obligation.
    eapply R_stateR. all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; destruct (hΣ _ wfΣ). clear aux.
    specialize_Σ wfΣ.
    apply conv_cum_zipp; auto.
    constructor. eapply ws_cumul_eq_pb.
    constructor. all:fvs.
    - destruct h. eapply welltyped_zipc_zipp in h1; auto. fvs.
    - constructor. eapply eqb_universe_instance_spec; eauto.
      + eapply welltyped_zipc_tConst_inv in h1 as (?&?&?); eauto;
        eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
        intros; apply wf_universe_iff; eauto.
      + eapply welltyped_zipc_tConst_inv in h2 as (?&?&?); eauto;
        eapply Forall_forallb; try eapply consistent_instance_wf_sort; eauto.
        intros; apply wf_universe_iff; eauto.
  Qed.
  Next Obligation.
    pose (heΣ _ wfΣ). specialize_Σ wfΣ. sq.
    eapply red_welltyped ; [auto|..].
    - exact h1.
    - eapply red_zipc.
      eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    pose (heΣ _ wfΣ). clear aux. specialize_Σ wfΣ. sq.
    eapply red_welltyped ; [auto|..].
    - exact h2.
    - eapply red_zipc.
      eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros.
    eapply cored_zipc.
    eapply cored_const.
    erewrite abstract_env_lookup_correct'; eauto.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (hΣ _ wfΣ).
    specialize_Σ wfΣ.
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply closed_red_zipp. 1:eapply welltyped_zipc_zipp in h1; fvs.
      eapply into_closed_red.
      * eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
      * eapply welltyped_zipc_zipp in h1; fvs.
      * eapply welltyped_zipc_zipp in h1; fvs.
    - etransitivity ; try eassumption.
      eapply red_conv_cum_r ; try assumption.
      eapply closed_red_zipp; auto.
      2:{ eapply into_closed_red; auto.
        * eapply red_const. erewrite abstract_env_lookup_correct'; eauto.
        * eapply welltyped_zipc_zipp in h1; fvs. }
      clear aux. eapply welltyped_zipc_zipp in h2; eauto.
      destruct hx as [hx]. rewrite (All2_fold_length hx); fvs.
      Unshelve. all:eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    right; split; [easy|].
    now rewrite <- uneq_u.
  Qed.

  (* tLambda *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in e. now apply eqb_binder_annot_spec.
    - assumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct h0 as [h0].
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct (hΣ _ wfΣ).
    symmetry in e; apply eqb_binder_annot_spec in e.
    now eapply conv_cum_Lambda.
  Qed.

  (* tProd *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in e.
      now apply eqb_binder_annot_spec.
    - assumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct h0 as [h0].
    destruct hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    apply mkApps_Prod_nil in h1 as ->; auto.
    apply mkApps_Prod_nil in h2 as ->; auto.
    destruct h.
    symmetry in e.
    apply eqb_binder_annot_spec in e.
    split; eapply ws_cumul_pb_Prod; auto.
  Qed.
  (* tCase *)
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    zip fold in h1. apply welltyped_context in h1 ; auto. simpl in h1.
    destruct h1 as [T h1].
    apply inversion_Case in h1 as hh ; auto.
    destruct hh as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    clear aux.
    zip fold in h2. eapply welltyped_context in h2 ; eauto. simpl in h2.
    destruct h2 as [T h2].
    apply inversion_Case in h2 as hh ; auto.
    destruct hh as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    now apply eqb_eq.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r, stack_position_cons.
    eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    now apply eqb_eq.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    pose proof hx as hx'.
    rename H into wfΣ; specialize_Σ wfΣ.
    pose proof (heΣ _ wfΣ) as [].
    apply conv_cum_zipp; auto.
    destruct convp as [h1'], convbrs as [h2'], convargs as [h3].
    destruct convdiscr as [cdiscr]. cbn in cdiscr.
    unfold zipp in h1, h2. simpl in h1, h2.
    sq.
    apply ws_cumul_eq_pb.
    change (eq_dec_to_bool ci ci') with (eqb ci ci') in eq5.
    destruct (eqb_specT ci ci'). 2: discriminate.
    subst. eapply ws_cumul_pb_Case. all: tas.
    * clear aux eq2 eq4. eapply welltyped_zipc_zipp in h1; eauto.
      eapply welltyped_is_open_term in h1.
      rewrite zipp_as_mkApps in h1.
      rewrite on_free_vars_mkApps in h1.
      now apply andb_true_iff in h1 as [].
    * clear aux eq2 eq4. eapply welltyped_zipc_zipp in h2; eauto.
      eapply welltyped_is_open_term in h2.
      rewrite zipp_as_mkApps in h2.
      rewrite on_free_vars_mkApps in h2.
      unfold is_open_case. rewrite (All2_fold_length hx').
      now apply andb_true_iff in h2 as [].
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ) as []. pose proof h2 as h2'.
    specialize_Σ wfΣ.
    match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    eapply red_welltyped ; [auto|..].
    - exact h2'.
    - eapply red_zipc.
      eapply red_case_c; auto. eapply hr.
  Qed.
  Next Obligation.
    edestruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    specialize_Σ wfΣ.
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c' [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq4.
      Transparent reduce_term.
      unfold reduce_term.
      rewrite e'. cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq4.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros.  eapply cored_zipc. eapply cored_case.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.

  Next Obligation.
    rename H into wfΣ; pose proof (hΣ _ wfΣ) as w.
    pose proof hx as hx'; specialize_Σ wfΣ. destruct w.
    destruct hx' as [hx'].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eassumption.
    - eapply conv_cum_conv_ctx; tea.
      eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_case_c. eapply hr'.
      * fvs.
      * clear aux eq4 h hr'.
        clear hr. eapply welltyped_zipc_zipp in h2; fvs.
        Unshelve. all:eauto.
  Qed.

  Next Obligation.
    pose proof (heΣ _ wfΣ) as []. pose proof h1 as h1'.
    clear aux eq3. specialize_Σ wfΣ.
    match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    sq.
    eapply red_welltyped ; [auto|..].
    - exact h1'.
    - eapply red_zipc.
      apply red_case_c, hr.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq3.
      unfold reduce_term.
      rewrite e'.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq3.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
        cbn in Hc. rtoProp; intuition.
    }
    unshelve eapply R_cored.
    simpl. intros; eapply cored_zipc. eapply cored_case.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ; specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_case_c, hr'.
      * fvs.
      * clear eq3 h hr' hr; eapply welltyped_zipc_zipp in h1; fvs.
    - assumption.
    Unshelve. all:eauto.
  Qed.

  (* tProj *)
  Next Obligation.
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    zip fold in h1. eapply welltyped_context in h1 ; eauto. simpl in h1.
    destruct h1 as [T h1].
    apply inversion_Proj in h1 as hh. 2: auto.
    destruct hh as [? [? [? [? [? [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (hΣ _ wfΣ) as [wΣ].
    zip fold in h2. eapply welltyped_context in h2 as h2' ; eauto. simpl in h2'.
    destruct h2' as [T h2'].
    apply inversion_Proj in h2' as hh. 2: auto.
    destruct hh as [? [? [? [? [? [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    eapply R_aux_positionR. all: simpl.
    - reflexivity.
    - rewrite <- app_nil_r, stack_position_cons. apply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ. destruct (heΣ _ wfΣ) as [wΣ].
    specialize_Σ wfΣ.
    destruct convdiscr as [h1'].
    change (true = eqb p p') in eq5.
    destruct (eqb_spec p p'). 2: discriminate. subst.
    apply conv_cum_zipp; auto.
    clear eq3 eq4 aux. eapply conv_conv_cum_l.
    now eapply ws_cumul_pb_Proj_c.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ) as [].
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    eapply red_welltyped ; [auto|..].
    - exact (h2 _ wfΣ).
    - eapply red_zipc.
      eapply red_proj_c, hr.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c' [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq4.
      unfold reduce_term.
      rewrite e'.
      cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq4.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c').
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h2 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. intros; eapply cored_zipc. eapply cored_proj.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eassumption.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ. specialize_Σ wfΣ.
    pose proof (hΣ _ wfΣ) as w. destruct w.
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eassumption.
    - eapply conv_cum_conv_ctx; tea.
      eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr'.
      * fvs.
      * clear hr hr' h eq4 aux. eapply welltyped_zipc_zipp in h2; fvs.
      Unshelve. all:eauto.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ) as [].
    match goal with
      | |- context [ reduce_term ?f _ ?X ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f _ X Γ t h) as Hr; edestruct Hr as [hr]
    end; eauto.
    sq.
    eapply red_welltyped ; [auto|..].
    - exact (h1 _ wfΣ).
    - eapply red_zipc.
      eapply red_proj_c, hr.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    match goal with
    | |- context [ reduce_term ?f _ ?X ?Γ c ?h ] =>
      destruct (reduce_stack_Req f _ X _ wfΣ Γ c [] h) as [e' | hr]
    end.
    1:{
      enough false by auto. rewrite eq3.
      unfold reduce_term.
      rewrite e'.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    dependent destruction hr.
    2:{
      enough false by auto. rewrite eq3.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term.
      rewrite <- H2.
      cbn.
      assert (wf_universes Σ c).
      2: eapply cmpb_term_correct; tea; cbnr.
      - pose proof h1 as Hc. specialize_Σ wfΣ. pose proof (hΣ _  wfΣ); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
    }
    unshelve eapply R_cored.
    simpl. intros; eapply cored_zipc. eapply cored_proj.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eassumption.
    Unshelve. all: eauto. all: intros; eapply abstract_env_compare_sort_correct with (conv_pb := Conv); eauto; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ. specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct (hr _ wfΣ) as [hr'].
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr'.
      * fvs.
      * clear eq3 aux hr hr' h. eapply welltyped_zipc_zipp in h1; fvs.
    - assumption.
    Unshelve. all:eauto.
  Qed.

  (* tFix *)
  Next Obligation.
    pose proof (hΣ _ wfΣ) as hΣ.
    cbn. rewrite zipc_appstack. cbn.
    eapply unfold_one_fix_red_zipp in eq1 as r; eauto.
    sq.
    apply unfold_one_fix_decompose in eq1 as d.
    rewrite <- eq2 in d. simpl in d.
    unfold zipp in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    rewrite e1 in r.
    rewrite e1 in d. simpl in d. subst.
    eapply welltyped_zipc_zipp in h1 as hh1; eauto.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    unfold zipp in hh1. rewrite e1 in hh1.
    pose proof (red_welltyped _ hΣ hh1 r) as hh.
    rewrite stack_context_appstack in hh.
    assumption.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ).
    eapply unfold_one_fix_red in eq1 as r1; eauto.
    eapply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ wfΣ.
    simpl_stacks.
    sq.
    eapply red_welltyped.
    1: eauto.
    1: exact (h1 _ wfΣ).
    etransitivity.
    2: { apply red_zipc.
         rewrite stack_context_decompose.
         exact r. }
    simpl_stacks.
    eassumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (heΣ _ wfΣ) as heΣ.
    specialize_Σ wf.
    eapply unfold_one_fix_cored in eq1 as r1; eauto.
    eapply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored. simpl. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    eapply red_cored_cored ; try eassumption.
    eapply clrel_rel in r2.
    apply red_context_zip in r2. cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    assumption.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ H.
    now simpl_stacks.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; [easy|]. intros.
    cbn in *. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now simpl_stacks.
    Unshelve. all:eauto.
  Qed.

  (* E form: scoping from [ref_open_term] (ReduceEnvFacts at E, PROVED in the bridge) on the
     structural spine, which [wt_zipc_stack_context] types. *)
  Lemma wt_zip_mkapps Σ (wfΣ:abstract_env_ext_rel X Σ) Γ f π :
    no_Eta_arg π ->
    welltypedE Σ Γ (zipc f π) -> is_open_term (Γ ,,, stack_context π) (mkApps f (decompose_stack π).1).
  Proof using conv_factsE.
    intros hna h.
    destruct (heΣ _ wfΣ) as [hwf].
    destruct (decompose_stack π) as [args ρ] eqn:hd. cbn [fst].
    eapply (ref_open_term (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf).
    exact (wt_zipc_stack_context Σ Γ f π ρ args hwf hna hd h).
  Qed.

  Next Obligation.
    eapply unfold_one_fix_red_zipp in eq1 as r1; eauto.
    eapply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ H.
    simpl_reduce_stack Σ H.
    destruct (hΣ _ H), r1  as [r1].
    eapply conv_cum_trans; auto.
    eapply red_conv_cum_l.
    etransitivity. 2:eauto.
    eapply into_closed_red; tea; [fvs|].
    eapply (f_equal stack_context) in d1.
    rewrite !stack_context_decompose in d1. rewrite <- d1.
    now eapply wt_zip_mkapps.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    pose proof (heΣ _ wfΣ).
    eapply unfold_one_fix_red_zipp in eq1 as r; eauto.
    sq.
    apply unfold_one_fix_decompose in eq1 as d.
    clear aux eq1.
    eapply welltyped_zipc_zipp in h2; eauto.
    cbn in *.
    simpl_stacks.
    eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    pose proof (hΣ _ wfΣ) as hΣ.
    eapply unfold_one_fix_red in eq1 as r1; eauto.
    sq.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f _ X Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    pose proof (red_welltyped _ hΣ (h2 _ wfΣ) r1) as hh.
    apply clrel_rel, red_context_zip in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_welltyped _ hΣ hh r2) as hh'.
    rewrite zipc_stack_cat. assumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (heΣ _ wfΣ) as heΣ.
    eapply unfold_one_fix_cored in eq1 as r1; eauto.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored2. all: try reflexivity. simpl. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    eapply red_cored_cored ; try eassumption.
    cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    do 2 zip fold. eapply red_context_zip, r2.
    Unshelve. eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in d2. cbn in d2.
     rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq2 in d1. simpl in d1.
    case_eq (decompose_stack π2). intros args2 ρ2 e2.
    rewrite e2 in d1. simpl in d1. subst.
    case_eq (decompose_stack ρ). intros l ξ e'.
    rewrite e' in d2. simpl in d2. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack.
    rewrite stack_context_appstack.
    apply decompose_stack_eq in e2 as ?. subst.
    clear eq3.
    rewrite stack_context_appstack in hx.
    eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; [easy|]. intros. erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    simpl_stacks.
    eauto.
  Unshelve. all: eauto.
  Qed.
  Next Obligation.
    eapply unfold_one_fix_red_zipp in eq1 as r1; eauto.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts Σ H.
    simpl_reduce_stack Σ H.
    destruct r1 as [r1]. specialize_Σ H.
    destruct (hΣ _ H), hx.
    eapply conv_cum_red_conv.
    1,4: eauto.
    * eapply closed_red_refl; [fvs|].
      now eapply wt_zip_mkapps.
    * etransitivity; eauto.
      eapply into_closed_red.
      + eapply r1.
      + fvs.
      + eapply (f_equal stack_context) in d1.
        rewrite !stack_context_decompose in d1. rewrite <- d1.
        now eapply wt_zip_mkapps.
  Qed.
  Next Obligation.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_stateR.
    all: simpl.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    pose proof (hΣ _ H) as [hΣ]. specialize_Σ H.
    apply conv_cum_zipp; auto.
    destruct convfix as [h1'].
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_specT idx idx'). 2: discriminate.
    subst.
    eapply ws_cumul_pb_Fix; eauto.
    - clear aux eee. eapply welltyped_zipc_zipp in h1; fvs.
    - eapply All2_impl; eauto. intros.
      split; try eapply X0; eauto.
      split; try eapply X0; eauto.
  Qed.

  (* tCoFix *)
  Next Obligation.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_stateR.
    all: simpl.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    apply conv_cum_zipp; auto.
    destruct convfix as [h1'].
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_specT idx idx'). 2: discriminate.
    subst.
    eapply ws_cumul_pb_CoFix; eauto.
    - clear aux h1'. eapply welltyped_zipc_zipp in h1; fvs.
    - eapply All2_impl; eauto. now cbn; intros.
  Qed.

  (* Primitive arrays *)
  Next Obligation.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    eapply conv_cum_zipp; eauto.
    * sq. eapply ws_cumul_pb_Prim; eauto.
      + symmetry in eqi; eapply eqb_eq in eqi. subst i'.
        constructor.
      + specialize (hx Σ wfΣ) as []. fvs.
    * specialize (hx Σ wfΣ).
      specialize (h1 Σ wfΣ).
      apply welltyped_zipc_zipp in h1; auto.
      clear aux.
      eapply welltyped_zipc_zipp in h2; eauto.
      rewrite !zipp_as_mkApps in h1, h2 |- *.
      apply mkApps_Prim_nil in h1 as ->; auto.
      apply mkApps_Prim_nil in h2 as ->; auto.
  Qed.

  Next Obligation.
  Proof.
    symmetry in eqf.
    apply eqb_eq in eqf; subst f'.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    clear aux.
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2; cbn.
    red. sq. eapply ws_cumul_pb_Prim; eauto; fvs.
    constructor.
  Qed.

  Next Obligation.
  Proof.
    symmetry in eqf.
    apply eqb_eq in eqf; subst f'.
    rename H into wfΣ. pose proof (hΣ _ wfΣ) as [hΣ].
    clear aux.
    specialize (hx Σ wfΣ).
    specialize (h1 Σ wfΣ).
    specialize (h2 Σ wfΣ).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    apply mkApps_Prim_nil in h1; auto.
    apply mkApps_Prim_nil in h2; auto.
    rewrite h1 h2; cbn.
    red. sq. eapply ws_cumul_pb_Prim; eauto; fvs.
    constructor.
  Qed.

  Next Obligation.
  Proof.
    destruct a; eauto.
  Qed.

  Next Obligation.
  Proof.
    destruct a'; eauto.
  Qed.

  Next Obligation.
  Proof.
    eapply R_positionR. all: simpl.
    - now destruct a.
    - rewrite <- app_nil_r, stack_position_cons.
      eapply positionR_poscat. constructor.
  Qed.

  Next Obligation.
  Proof.
    now destruct a.
  Qed.

  Next Obligation.
  Proof.
    now destruct a'; eauto.
  Qed.

  Next Obligation.
  Proof.
    eapply R_positionR. all: simpl.
    - now destruct a.
    - rewrite <- app_nil_r, stack_position_cons.
      eapply positionR_poscat. constructor.
  Qed.

  Next Obligation.
  Proof.
    pose proof (hΣ _ H) as [hΣ].
    specialize (h1 Σ H). clear aux.
    specialize (h2 Σ H).
    apply welltyped_zipc_zipp in h1; eauto.
    eapply welltyped_zipc_zipp in h2; eauto.
    rewrite !zipp_as_mkApps in h1, h2 |- *.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h1); auto.
    pose proof (mkApps_Prim_nil _ _ _ _ _ h2); auto.
    rewrite H0 H1; cbn.
    specialize (convdiscrty _ H) as [convty].
    specialize (convdiscrdef _ H) as [convdef].
    specialize (convdiscrval _ H) as [convval].
    cbn in convty, convdef.
    symmetry in eql.
    eapply abstract_env_compare_universe_correct with (conv_pb := Conv) in eql; eauto.
    2:{ destruct h1 as [? ty]; eapply typing_wf_universes in ty; eauto.
        move/andP: ty => []. rewrite H0 /=. cbn -[wf_universeb].
        rtoProp; intuition auto.
        now move/wf_universe_reflect: H3. }
    2:{ destruct h2 as [? ty]; eapply typing_wf_universes in ty; eauto.
        move/andP: ty => []. rewrite H1 /=. cbn -[wf_universeb].
        rtoProp; intuition auto.
        now move/wf_universe_reflect: H3. }
    constructor. eapply ws_cumul_pb_Prim; eauto; fvs.
    constructor; eauto.
  Qed.

  (* Fallback *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.

  (* The E Args machinery (plan I7 rev 13 B2, rev 14 NB2, rev 15 C1/C2).
     The entry pack [y] is the Args pack [_isconv_args] builds, with side i at
     (ti, appstack Li θi), θi := (decompose_stack πi).2; every call is measured against it
     ([AuxE']). Side 1 keeps its head [t1] and its consumed arguments [args1] apart; side 2
     folds its consumed arguments [ca2] into its head ([mkApps t2 ca2]), as base.
     The η argument list of side i is [map (eta_rename θi 0) Li ++ eta_virtuals (eta_run θi)]
     (decompose_stack_eta), compared pairwise in side 1's η context [Γ ,,, stack_context_eta θ1]
     (which is also that of every state below: App_r and Eta_arg [] push no η declaration).
     Real pairs: T3 guard, then base's App_r descent (R_positionR,
     positionR_App_r_appstack_gen). Virtual pairs (after the real spine of one side): the
     virtual side is (virtual_focus m j, Eta_arg ti [] :: appstack Li θi) (rev 14 NB2, in the
     shape of K4_virtual_descent_frame_left/_right, rev 15 C1), the real side is guarded by G4.
     When both real spines are consumed the two virtual tails are syntactically equal iff they
     have the same length ([skipn j (eta_virtuals m) = eta_virtuals (m - j)]). *)

  Notation Epack Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h2 :=
    (mkpack Γ Args t1 (appstack L1 θ1) t2 (appstack L2 θ2) f1 f2 h2) (only parsing).

  Notation args_spec Γ θ1 θ2 l1 vs1 l2 vs2 :=
    (forall Σ, abstract_env_ext_rel X Σ ->
       ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta θ1)
           (map (eta_rename θ1 0) l1 ++ vs1) (map (eta_rename θ2 0) l2 ++ vs2) ∥) (only parsing).

  (* Both real spines consumed: the remaining virtual tails. *)
  Equations(noeqns) _isconv_args_vv (Γ : context) (θ1 θ2 : stack)
            (t1 : term) (args1 : list term) (t2 : term) (ca2 : list term)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ1) ∥)
            (j1 j2 : nat)
    : ConversionResult (args_spec Γ θ1 θ2 [] (skipn j1 (eta_virtuals (eta_run θ1)))
                                         [] (skipn j2 (eta_virtuals (eta_run θ2)))) :=
    _isconv_args_vv Γ θ1 θ2 t1 args1 t2 ca2 hwf1 j1 j2
    with inspect (Nat.eqb (eta_run θ1 - j1) (eta_run θ2 - j2)) := {
    | @exist true eqm := yes ;
    | @exist false _ := no (StackMismatch (Γ ,,, stack_context θ1) t1 args1 []
                                          (Γ ,,, stack_context θ2) t2 [])
    }.

  (* Side 1's real spine consumed (it is [L1] entirely): its virtual j1 against side 2's
     real arguments [l2]. *)
  Equations(noeqns) _isconv_args_vl (leq : conv_pb) (Γ : context)
            (t1 : term) (L1 : list term) (θ1 : stack) (t2 : term) (L2 : list term) (θ2 : stack)
            (f1 : wf_stack (appstack L1 θ1)) (f2 : wf_stack (appstack L2 θ2))
            (h1 : wtp Γ t1 (appstack L1 θ1)) (h2 : wtp Γ t2 (appstack L2 θ2))
            (hθ1 : isStackApp θ1 = false) (hθ2 : isStackApp θ2 = false)
            (hx : conv_stack_ctx Γ θ1 θ2)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ2) ∥)
            (aux : AuxE' Γ (Epack Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h2))
            (j1 : nat) (ca2 l2 : list term) (e2 : ca2 ++ l2 = L2)
    : ConversionResult (args_spec Γ θ1 θ2 [] (skipn j1 (eta_virtuals (eta_run θ1)))
                                         l2 (eta_virtuals (eta_run θ2))) by struct l2 :=
    _isconv_args_vl leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux j1 ca2 (u2 :: l2) e2
    with inspect (Nat.ltb j1 (eta_run θ1)) := {
    | @exist false _ := no (StackMismatch (Γ ,,, stack_context θ1) t1 L1 []
                                          (Γ ,,, stack_context θ2) (mkApps t2 ca2) (u2 :: l2)) ;
    | @exist true hj with inspect (no_Eta_arg θ2) := {          (* G4 *)
      | @exist false _ := no (EtaStackRefusal (Γ ,,, stack_context_eta θ1) (virtual_focus (eta_run θ1) j1)
                                              (Γ ,,, stack_context θ2) u2) ;
      | @exist true g4
        with aux Reduction (virtual_focus (eta_run θ1) j1) (Eta_arg t1 [] :: appstack L1 θ1)
                           u2 (App_r (mkApps t2 ca2) :: appstack l2 θ2)
                           _ _ _ _ _ Conv _ _ _ _ _ I I I := {
        | Success H1
          with _isconv_args_vl leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux
                               (S j1) (ca2 ++ [u2]) l2 _ := {
          | Success H2 := yes ;
          | Error e := no (StackTailError leq (Γ ,,, stack_context θ1) t1 L1
                                          (virtual_focus (eta_run θ1) j1) []
                                          (Γ ,,, stack_context θ2) (mkApps t2 ca2) u2 l2 e)
          } ;
        | Error e := no (StackHeadError leq (Γ ,,, stack_context θ1) t1 L1
                                        (virtual_focus (eta_run θ1) j1) []
                                        (Γ ,,, stack_context θ2) (mkApps t2 ca2) u2 l2 e)
        }
      }
    } ;
    _isconv_args_vl leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux j1 ca2 [] e2
    with _isconv_args_vv Γ θ1 θ2 t1 L1 t2 ca2 hwf1 j1 0 := {
    | Success H := yes ;
    | Error e := no e
    }.

  (* Side 2's real spine consumed: side 1's real arguments [l1] against side 2's virtual j2. *)
  Equations(noeqns) _isconv_args_vr (leq : conv_pb) (Γ : context)
            (t1 : term) (L1 : list term) (θ1 : stack) (t2 : term) (L2 : list term) (θ2 : stack)
            (f1 : wf_stack (appstack L1 θ1)) (f2 : wf_stack (appstack L2 θ2))
            (h1 : wtp Γ t1 (appstack L1 θ1)) (h2 : wtp Γ t2 (appstack L2 θ2))
            (hθ1 : isStackApp θ1 = false) (hθ2 : isStackApp θ2 = false)
            (hx : conv_stack_ctx Γ θ1 θ2)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ2) ∥)
            (aux : AuxE' Γ (Epack Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h2))
            (args1 l1 : list term) (e1 : args1 ++ l1 = L1) (j2 : nat)
    : ConversionResult (args_spec Γ θ1 θ2 l1 (eta_virtuals (eta_run θ1))
                                         [] (skipn j2 (eta_virtuals (eta_run θ2)))) by struct l1 :=
    _isconv_args_vr leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux args1 (u1 :: l1) e1 j2
    with inspect (Nat.ltb j2 (eta_run θ2)) := {
    | @exist false _ := no (StackMismatch (Γ ,,, stack_context θ1) t1 args1 (u1 :: l1)
                                          (Γ ,,, stack_context θ2) (mkApps t2 L2) []) ;
    | @exist true hj with inspect (no_Eta_arg θ1) := {          (* G4 *)
      | @exist false _ := no (EtaStackRefusal (Γ ,,, stack_context θ1) u1
                                              (Γ ,,, stack_context_eta θ2) (virtual_focus (eta_run θ2) j2)) ;
      | @exist true g4
        with aux Reduction u1 (App_r (mkApps t1 args1) :: appstack l1 θ1)
                           (virtual_focus (eta_run θ2) j2) (Eta_arg t2 [] :: appstack L2 θ2)
                           _ _ _ _ _ Conv _ _ _ _ _ I I I := {
        | Success H1
          with _isconv_args_vr leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux
                               (args1 ++ [u1]) l1 _ (S j2) := {
          | Success H2 := yes ;
          | Error e := no (StackTailError leq (Γ ,,, stack_context θ1) t1 args1 u1 l1
                                          (Γ ,,, stack_context θ2) (mkApps t2 L2)
                                          (virtual_focus (eta_run θ2) j2) [] e)
          } ;
        | Error e := no (StackHeadError leq (Γ ,,, stack_context θ1) t1 args1 u1 l1
                                        (Γ ,,, stack_context θ2) (mkApps t2 L2)
                                        (virtual_focus (eta_run θ2) j2) [] e)
        }
      }
    } ;
    _isconv_args_vr leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux args1 [] e1 j2
    with _isconv_args_vv Γ θ1 θ2 t1 args1 t2 L2 hwf1 0 j2 := {
    | Success H := yes ;
    | Error e := no e
    }.

  (* The real phase: both sides have real arguments left (base's recursion), T3 before the
     App_r push; then the virtual tails. *)
  Equations(noeqns) _isconv_args' (leq : conv_pb) (Γ : context)
            (t1 : term) (L1 : list term) (θ1 : stack) (t2 : term) (L2 : list term) (θ2 : stack)
            (f1 : wf_stack (appstack L1 θ1)) (f2 : wf_stack (appstack L2 θ2))
            (h1 : wtp Γ t1 (appstack L1 θ1)) (h2 : wtp Γ t2 (appstack L2 θ2))
            (hθ1 : isStackApp θ1 = false) (hθ2 : isStackApp θ2 = false)
            (hx : conv_stack_ctx Γ θ1 θ2)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta θ2) ∥)
            (aux : AuxE' Γ (Epack Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h2))
            (args1 l1 : list term) (e1 : args1 ++ l1 = L1)
            (ca2 l2 : list term) (e2 : ca2 ++ l2 = L2)
    : ConversionResult (args_spec Γ θ1 θ2 l1 (eta_virtuals (eta_run θ1))
                                         l2 (eta_virtuals (eta_run θ2))) by struct l1 :=
    _isconv_args' leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux args1 (u1 :: l1) e1 ca2 (u2 :: l2) e2
    with inspect (no_Eta_arg θ1 && no_Eta_arg θ2) := {         (* T3 *)
    | @exist false _ := no (EtaStackRefusal (Γ ,,, stack_context θ1) u1 (Γ ,,, stack_context θ2) u2) ;
    | @exist true g3
      with aux Reduction u1 (App_r (mkApps t1 args1) :: appstack l1 θ1)
                         u2 (App_r (mkApps t2 ca2) :: appstack l2 θ2)
                         _ _ _ _ _ Conv _ _ _ _ _ I I I := {
      | Success H1
        with _isconv_args' leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux
                           (args1 ++ [u1]) l1 _ (ca2 ++ [u2]) l2 _ := {
        | Success H2 := yes ;
        | Error e :=
          no (
            StackTailError
              leq
              (Γ ,,, stack_context θ1) t1 args1 u1 l1
              (Γ ,,, stack_context θ2) (mkApps t2 ca2) u2 l2 e
          )
        } ;
      | Error e :=
        no (
          StackHeadError
            leq
            (Γ ,,, stack_context θ1) t1 args1 u1 l1
            (Γ ,,, stack_context θ2) (mkApps t2 ca2) u2 l2 e
        )
      }
    } ;

    _isconv_args' leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux args1 [] e1 ca2 l2 e2
    with _isconv_args_vl leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux 0 ca2 l2 e2 := {
    | Success H := yes ;
    | Error e := no e
    } ;

    _isconv_args' leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux args1 l1 e1 ca2 [] e2
    with _isconv_args_vr leq Γ t1 L1 θ1 t2 L2 θ2 f1 f2 h1 h2 hθ1 hθ2 hx hwf1 hwf2 aux args1 l1 e1 0 := {
    | Success H := yes ;
    | Error e := no e
    }.
  Next Obligation.
    split. 1: reflexivity.
    rewrite !stack_position_cons.
    eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rewrite 2!stack_context_appstack.
    eauto.
  Qed.
  Next Obligation.
    rewrite mkApps_app. eauto.
  Qed.
  Next Obligation.
    rewrite length_app in h. cbn in h. lia.
  Defined.
  Next Obligation.
    rewrite length_app in h. cbn in h.
      simpl. split.
      + rewrite mkApps_app in H. assumption.
      + rewrite !stack_position_cons !stack_position_appstack.
        rewrite <- !app_assoc. apply positionR_poscat.
        assert (h' : forall n m, positionR (repeat app_l n ++ [app_r]) (repeat app_l m)).
        { clear. intro n. induction n ; intro m.
          - destruct m ; constructor.
          - destruct m.
            + constructor.
            + cbn. constructor. apply IHn.
        }
        simpl.
        rewrite <- repeat_snoc.
        apply (h' #|d| (S #|l1|)).
  Qed.
  Next Obligation.
    specialize_Σ wfΣ.
    destruct (hΣ _ wfΣ) as [wΣ].
    destruct H1 as [H1].
    unfold zipp. simpl.
    unfold zipp in H1. simpl in H1.
    rewrite stack_context_appstack in H1.
    destruct H2 as [H2].
    constructor; constructor; auto.
  Qed.

  Equations(noeqns) _isconv_args (leq : conv_pb) (Γ : context)
           (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
           (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
           (hx : conv_stack_ctx Γ π1 π2)
           (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
           (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
           (aux : Aux Args Γ t1 π1 t2 π2 f1 f2 h2)
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
                          ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π1)
                              (decompose_stack_eta π1).1 (decompose_stack_eta π2).1 ∥) :=
    _isconv_args leq Γ t1 π1 f1 h1 t2 π2 f2 h2 hx hwf1 hwf2 aux with inspect (decompose_stack π1) := {
    | @exist (l1, θ1) eq1 with inspect (decompose_stack π2) := {
      | @exist (l2, θ2) eq2
        with _isconv_args' leq Γ t1 l1 θ1 t2 l2 θ2 _ _ _ _ _ _ _ _ _ _ [] l1 eq_refl [] l2 eq_refl := {
        | Success h := yes ;
        | Error e := no e
        }
      }
    }.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    eauto.
  Qed.
  Next Obligation.
    eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    eauto.
  Qed.
  Next Obligation.
    eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite 2!stack_context_appstack in hx.
    eauto.
  Qed.
  Next Obligation.
    eapply (aux Reduction). all: auto.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    instantiate (1 := h2').
    simpl in H0. destruct H0 as [eq hp].
    unshelve eapply R_positionR. 2: assumption.
    simpl. rewrite eq. reflexivity.
  Defined.
  (* The obligation tactic wipes out a useful hypothesis here? *)
  Obligation Tactic := idtac.
  Next Obligation.
    intros; cbn in *.
    rewrite <- (stack_context_decompose π1).
    rewrite <- eq1, <- eq2.
    auto.
  Qed.
  Obligation Tactic :=
    Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf.

  (* Site 6 of the 11 reduce_stack sites: [args := []]. *)
  Equations unfold_one_case (Γ : context) (ci : case_info)
            (p : predicate term) (c : term) (brs : list (branch term))
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (tCase ci p c brs)) : option term :=
    unfold_one_case Γ ci p c brs h
    with inspect (reduce_args_E RedFlags.default X_type X Γ c [] _) := {
    | @exist (cred, args) eq with cc_viewc cred := {
      | ccview_construct ind' n ui with inspect (nth_error brs n) := {
        | exist (Some br) eqbr := Some (iota_red ci.(ci_npar) p args br) ;
        | exist None eqbr := False_rect _ _ } ;
      | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
        | @exist (Some (narg, fn)) eq2 := Some (tCase ci p (mkApps fn args) brs) ;
        | @exist None eq2 := False_rect _ _
        } ;
      | ccview_other cred _ := None
      }
    }.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [wΣ]. specialize_Σ wfΣ.
    cbn. destruct h as [T h].
    apply inversion_Case in h ; auto.
    destruct h as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (hΣ _ wfΣ) as [hΣ].
    assert (r' : red Σ Γ (tCase ci p c brs)
      (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs))
      by eapply red_case_c, r.
    pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
    destruct h'.
    apply PCUICInductiveInversion.invert_Case_Construct in X0 as (?&?&?&?); auto.
    congruence.
  Qed.

  Next Obligation.
  Proof.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (h _ wfΣ) as (?&typ); auto.
    destruct (hΣ _ wfΣ).
    apply inversion_Case in typ as [mdecl [idecl [isdecl [indices [[] cum]]]]]; auto.
    eapply PCUICSR.subject_reduction in scrut_ty. 2:auto. 2:exact r.
    eapply PCUICValidity.inversion_mkApps in scrut_ty as (?&typ&?); auto.
    apply inversion_CoFix in typ as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    now rewrite e in eq2.
  Qed.

  Lemma unfold_one_case_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs h t,
      Some t = unfold_one_case Γ ci p c brs h ->
      cored Σ Γ t (tCase ci p c brs).
  Proof using Type.
    intros Σ wfΣ Γ ci p c brs h t e.
    revert e.
    funelim (unfold_one_case Γ ci p c brs h).
    all:try Program.Tactics.bang.
    all: intros eq'' ; noconf eq''.
    - clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      destruct (hΣ _ wfΣ) as [hΣ].
      assert (r' : red Σ Γ (tCase ci p c brs)
          (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs))
        by eapply red_case_c, r.
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      eapply Case_Construct_ind_eq in h' ; eauto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_iota. 1: now symmetry.
        destruct (h _ wfΣ) as (?&typ).
        eapply PCUICSR.subject_reduction in typ; eauto.
        apply PCUICInductiveInversion.invert_Case_Construct in typ as (?&?&?&?); auto.
        rewrite H0 in eqbr; noconf eqbr. eauto.
      + eapply red_case_c, r.
    - clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      assert (r' : red Σ Γ (tCase ci p c brs)
                     (tCase ci p (mkApps (tCoFix mfix idx) (decompose_stack ρ).1) brs))
        by eapply red_case_c, r.
      destruct (hΣ _ wfΣ) as [hΣ].
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_case. eauto.
      + eapply red_case_c, r.
  Qed.

  (* Site 7 of the 11 reduce_stack sites: [args := []]. *)
  Equations unfold_one_proj (Γ : context) (p : projection) (c : term)
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (tProj p c)) : option term :=

    unfold_one_proj Γ p c h with p := {
    | mkProjection i pars narg with inspect (reduce_args_E RedFlags.default X_type X Γ c [] _) := {
      | @exist (cred, args) eq with cc0_viewc cred := {
        | cc0view_construct ind' ui with inspect (nth_error args (pars + narg)) := {
          | @exist (Some arg) eq2 := Some arg ;
          | @exist None eq2 := False_rect _ _
          } ;
        | cc0view_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
          | @exist (Some (rarg, fn)) eq2 :=
            Some (tProj p (mkApps fn args)) ;
          | @exist None eq2 := False_rect _ _
          } ;
        | cc0view_other cred _ := None
        }
      }
    }.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [wΣ].
    cbn. destruct (h _ wfΣ) as [T h'].
    apply inversion_Proj in h' ; auto.
    destruct h' as [uni [mdecl [idecl [pdecl [args' [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (h _ wfΣ) as (?&typ); auto.
    destruct (hΣ _ wfΣ).
    eapply PCUICSR.subject_reduction in typ.
    2: auto.
    2: apply red_proj_c, r.
    apply PCUICInductiveInversion.invert_Proj_Construct in typ as (<-&_&?); auto.
    apply eq_sym, nth_error_None in eq2. cbn in H.
    lia.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    destruct (h _ wfΣ) as (?&typ); auto.
    destruct (hΣ _ wfΣ).
    apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply PCUICSR.subject_reduction in t. 2:eauto. 2:exact r.
    apply PCUICValidity.inversion_mkApps in t as (?&?&?); auto.
    apply inversion_CoFix in t as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    rewrite e0 in eq2.
    congruence.
  Qed.

  Lemma unfold_one_proj_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ p c h t,
      Some t = unfold_one_proj Γ p c h ->
      cored Σ Γ t (tProj p c).
  Proof using Type.
    intros Σ wfΣ Γ p c h t e.
    revert e.
    funelim (unfold_one_proj Γ p c h).
    all: intros eq'' ; noconf eq''.
    - set (p := {| proj_ind := i; proj_npars := pars; proj_arg := narg |}).
       clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      pose proof (red_proj_c p _ _ r) as r'.
      destruct (hΣ _ wfΣ) as [hΣ].
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      apply Proj_Construct_ind_eq in h' ; auto. subst.
      eapply cored_red_cored.
      + constructor. eapply (red_proj _ _ p). eauto.
      + eapply red_proj_c, r.
    - match type of eq'' with
      | _ = False_rect _ ?f => destruct f
      end.
    -  set (p := {| proj_ind := i; proj_npars := pars; proj_arg := narg |}).
      clear H H0 H1.
      simpl_reduce_stack Σ wfΣ.
      pose proof (red_proj_c p _ _ r) as r'.
      destruct (hΣ _ wfΣ) as [hΣ].
      pose proof (red_welltyped _ hΣ (h _ wfΣ) r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_proj. eauto.
      + eapply red_proj_c, r.
    - match type of eq'' with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  (* T2 (rev 14 B4): each tFix/tCase/tProj/tConst arm runs only on a stack without Eta_arg and
     answers [None] otherwise (the tFix arm through unfold_one_fix's T4). Dead on reachable
     states by [virt_ok_not_head]; never a refusal, so no η acceptance is lost in the fallback. *)
  Equations reducible_head (Γ : context) (t : term) (π : stack)
            (h : wtp Γ t π)
    : option (term × stack) :=

    reducible_head Γ (tFix mfix idx) π h := unfold_one_fix Γ mfix idx π h ;

    reducible_head Γ (tCase ci p c brs) π h with inspect (no_Eta_arg π) := {
    | @exist false _ := None ;
    | @exist true hna
      with inspect (unfold_one_case (Γ ,,, stack_context π) ci p c brs _) := {
      | @exist (Some t) eq := Some (t, π) ;
      | @exist None _ := None
      }
    } ;

    reducible_head Γ (tProj p c) π h with inspect (no_Eta_arg π) := {
    | @exist false _ := None ;
    | @exist true hna
      with inspect (unfold_one_proj (Γ ,,, stack_context π) p c _) := {
      | @exist (Some t) eq := Some (t, π) ;
      | @exist None _ := None
      }
    } ;

    reducible_head Γ (tConst c u) π h with inspect (no_Eta_arg π) := {
    | @exist false _ := None ;
    | @exist true hna
      with inspect (abstract_env_lookup X c) := {
      | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq :=
        Some (subst_instance u body, π) ;
      (* bodiless or not found: a registered operation may take a machine step
         (design §7.3, last paragraph) *)
      | @exist _ _ := unfold_one_prim Γ c u π hna h
      }
    } ;

    reducible_head Γ _ π h := None.
  Next Obligation.
    zip fold in h.
    pose (abstract_env_ext_sq_wf _ X _ wfΣ).
    sq.
    eapply welltyped_context in h ; eauto.
  Qed.
  Next Obligation.
    pose (abstract_env_ext_sq_wf _ X _ wfΣ).
    sq.
    zip fold in h.
    eapply welltyped_context in h ; eauto.
  Qed.

  Lemma reducible_head_red_zipp :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp t π) (zipp fn ξ) ∥.
  Proof using Type.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; try noconf ee.
    all: try solve [ match goal with ee : Some (_, _) = unfold_one_prim _ _ _ _ _ |- _ =>
                       exact (fst (snd (unfold_one_prim_facts _ _ _ _ _ _ _ ee)) _ wfΣ) end ].
    - eapply unfold_one_fix_red_zipp; eauto.
    - constructor. simpl_stacks.
      eapply red_mkApps_f.
      eapply trans_red.
      + reflexivity.
      + eapply red_delta.
      * unfold declared_constant, declared_constant_gen.
        erewrite abstract_env_lookup_correct; eauto.
        * reflexivity.
    - eapply unfold_one_case_cored in eq as r; eauto.
      apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
    - eapply unfold_one_proj_cored in eq as r; eauto.
      apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
  Qed.

  Lemma reducible_head_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      cored Σ Γ (zipc fn ξ) (zipc t π).
  Proof using Type.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; try noconf ee.
    all: try solve [ match goal with ee : Some (_, _) = unfold_one_prim _ _ _ _ _ |- _ =>
                       exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ ee))) _ wfΣ) end ].
    - eapply unfold_one_fix_cored; eauto.
    - repeat zip fold. eapply cored_context.
      constructor. eapply red_delta.
      + unfold declared_constant, declared_constant_gen.
        erewrite abstract_env_lookup_correct; eauto.
      + reflexivity.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_case_cored; eauto.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_proj_cored; eauto.
  Qed.

  Lemma reducible_head_decompose :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof using Type.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; try noconf ee.
    all: try solve [ match goal with ee : Some (_, _) = unfold_one_prim _ _ _ _ _ |- _ =>
      destruct (unfold_one_prim_shape _ _ _ _ _ _ _ ee) as (args & ρ & l & [ed eξ _ _]);
      rewrite ed; subst; rewrite decompose_stack_appstack;
      rewrite (decompose_stack_twice _ _ _ ed); reflexivity end ].
    - eapply unfold_one_fix_decompose. eassumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* The η view of the fallback: which side, if any, is a λ (plan I7 "When"). In the fallback
     [prog_discr] holds, so at most one side is a λ. *)
  Inductive eta_view : term -> term -> Type :=
  | eta_view_left na A b t2 : eta_view (tLambda na A b) t2
  | eta_view_right t1 na A b : isLambda t1 = false -> eta_view t1 (tLambda na A b)
  | eta_view_other t1 t2 : isLambda t1 = false -> isLambda t2 = false -> eta_view t1 t2.

  Equations eta_viewc (t1 t2 : term) : eta_view t1 t2 :=
    eta_viewc (tLambda na A b) t2 := eta_view_left na A b t2 ;
    eta_viewc t1 (tLambda na A b) := eta_view_right t1 na A b _ ;
    eta_viewc t1 t2 := eta_view_other t1 t2 _ _.

  (* TODO Factorise *)
  Equations(noeqns) _isconv_fallback (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
            (ir1 : isred_full Γ t1 π1) (ir2 : isred_full Γ t2 π2)
            (hdiscr : prog_discr t1 t2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hv1 : virt_ok t1 π1 = true) (hv2 : virt_ok t2 π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Fallback Γ t1 π1 t2 π2 f1 f2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=
    _isconv_fallback Γ leq t1 π1 f1 h1 t2 π2 f2 h2 ir1 ir2 hdiscr hx hv1 hv2 hwf1 hwf2 aux
    with inspect (reducible_head Γ t1 π1 h1) := {
    | exist (Some (rt1, ρ1)) eq1 with inspect (decompose_stack ρ1) := {
      | exist (l1, θ1) eq2
        (* site 8 of the 11 reduce_stack sites *)
        with inspect (reduce_args_E RedFlags.nodelta X_type X (Γ ,,, stack_context ρ1) rt1 l1 _) := {
        | exist (rt1', l1') eq3 with inspect (rebuilt_ok rt1' l1' θ1) := {
          | exist true g2 := isconv_prog leq rt1' (appstack l1' θ1) t2 π2 aux ;
          | exist false _ := no (EtaStackRefusal (Γ ,,, focus_context π1) t1 (Γ ,,, focus_context π2) t2)
          }
        }
      } ;
    | exist None nored1 with inspect (reducible_head Γ t2 π2 h2) := {
      | exist (Some (rt2, ρ2)) eq1 with inspect (decompose_stack ρ2) := {
        | exist (l2, θ2) eq2
          (* site 9 of the 11 reduce_stack sites *)
          with inspect (reduce_args_E RedFlags.nodelta X_type X (Γ ,,, stack_context ρ2) rt2 l2 _) := {
          | exist (rt2', l2') eq3 with inspect (rebuilt_ok rt2' l2' θ2) := {
            | exist true g2 := isconv_prog leq t1 π1 rt2' (appstack l2' θ2) aux ;
            | exist false _ := no (EtaStackRefusal (Γ ,,, focus_context π1) t1 (Γ ,,, focus_context π2) t2)
            }
          }
        } ;
      (* I7 "Where": both sides answered [None]; the η step comes in place of the path to
         cmpb_term_napp/HeadMismatch. *)
      | exist None nored2 with eta_viewc t1 t2 := {
        (* λ on side 1 (rev 14 NB1): side 1 descends by Lambda_bd, side 2 gets the frame
           Eta_app na (eta_rename π1 0 A) after its spine; the comparison is at Conv (S1),
           entering at Reduction (rev 10); G3 guards the Lambda_bd push. *)
        | eta_view_left na A b t2
          with inspect (no_Eta_arg π1) := {
          | @exist false _ := no (EtaStackRefusal (Γ ,,, focus_context π1) (tLambda na A b)
                                                  (Γ ,,, focus_context π2) t2) ;
          | @exist true g3 with inspect (decompose_stack π2) := {
            | @exist (args2, ρ2) eq2
              with isconv_red_raw Conv b (Lambda_bd na A :: π1)
                     t2 (appstack args2 (Eta_app na (eta_rename π1 0 A) :: ρ2)) aux := {
              | Success h := yes ;
              | Error e := no e
              }
            }
          } ;
        (* λ on side 2: the same with the sides exchanged. *)
        | eta_view_right t1 na A b nl1
          with inspect (no_Eta_arg π2) := {
          | @exist false _ := no (EtaStackRefusal (Γ ,,, focus_context π1) t1
                                                  (Γ ,,, focus_context π2) (tLambda na A b)) ;
          | @exist true g3 with inspect (decompose_stack π1) := {
            | @exist (args1, ρ1) eq1
              with isconv_red_raw Conv t1 (appstack args1 (Eta_app na (eta_rename π2 0 A) :: ρ1))
                     b (Lambda_bd na A :: π2) aux := {
              | Success h := yes ;
              | Error e := no e
              }
            }
          } ;
        (* No λ: base's head comparison on the η views (heads read through eta_rename, napp
           counts the virtual arguments, plan I7's site list), then K1. *)
        | eta_view_other t1 t2 nl1 nl2
          with inspect (cmpb_term_napp leq #|(decompose_stack_eta π1).1|
                          (eta_rename π1 0 t1) (eta_rename π2 0 t2)) := {
          | exist true eq1 := isconv_args leq t1 π1 t2 π2 aux;
          | exist false noteq
            with inspect (must_expand_check (abstract_env_lookup X) eqb_term
                            abstract_env_compare_global_instance
                            t1 (decompose_stack_eta π1).1 t2 (decompose_stack_eta π2).1) := {
            (* K1 (plan row K1, EtaK1-patch.md): the kernel's MustExpand for under-applied
               tInd/tConstruct heads with unequal instances (conversion.ml V9.2.0 :186-232,
               :270-286, :634-638, :546-547): heads and remaining binder types checked here,
               arguments by the machine, exactly as in the cmpb_term_napp success arm above. *)
            | exist true k1 := isconv_args leq t1 π1 t2 π2 aux;
            | exist false _ :=
              no (
                  HeadMismatch
                    leq
                    (Γ ,,, stack_context_eta π1) t1
                    (Γ ,,, stack_context_eta π2) t2
                )
            }
          }
        }
      }
    }.
  Next Obligation.
    eapply reducible_head_red_zipp in eq1 as r; eauto.
    pose proof (hΣ := hΣ _ wfΣ).
    sq.
    apply reducible_head_decompose in eq1 as d.
    eapply welltyped_zipc_zipp in h1 as hh1; eauto.
    cbn in *.
    pose proof (red_welltyped _ hΣ hh1 r) as hh.
    simpl_stacks.
    assumption.
  Qed.
  Next Obligation.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply cored_red in r1.
    pose proof (hΣ _ wfΣ).
    sq.
    simpl_reduce_stack Σ wfΣ.
    eapply red_welltyped; revgoals. 3:auto.
    - zip fold. eapply red_context_zip. simpl_stacks. exact r.
    - cbn.
      simpl_stacks.
      eapply red_welltyped. 1:auto.
      2: exact r1.
      eauto.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. intros.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π1). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X Σ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply red_context_zip, r2.
  Qed.
  Next Obligation.
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ H.
    eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; auto. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now simpl_stacks.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    eapply reducible_head_red_zipp in eq1 as r1; eauto.
    destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ H.
    destruct (hΣ _ H) as [wΣ].
    etransitivity ; try eauto.
    eapply red_conv_cum_l; try eauto.
    etransitivity ; try eassumption.
    eapply into_closed_red; tea.
    * fvs.
    * eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1. rewrite <- d1.
      now eapply wt_zip_mkapps.
  Unshelve. all:eauto.
  Qed.
  Next Obligation.
    eapply reducible_head_red_zipp in eq1 as r; eauto.
    pose proof (hΣ := hΣ _ wfΣ).
    sq.
    apply reducible_head_decompose in eq1 as d.
    cbn.
    eapply welltyped_zipc_zipp in h2 as hh2 ; eauto.
    pose proof (red_welltyped _ hΣ hh2 r) as hh.
    simpl_stacks.
    assumption.
  Qed.
  Next Obligation.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply cored_red in r1.
    pose proof (hΣ := hΣ _ wfΣ).
    sq.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    rewrite stack_cat_appstack.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    pose proof (eq_sym eq2) as eq2'.
    apply decompose_stack_eq in eq2'. subst.
    rewrite stack_context_appstack in r2.
    eapply red_welltyped; [auto|..] ; revgoals.
    - zip fold. eapply red_context_zip, r2.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_welltyped; try apply r1 ; eauto.
  Qed.
  Next Obligation.
    eapply R_cored2. all: simpl. all: try reflexivity.
    intros.
    eapply reducible_head_cored in eq1 as r1; eauto.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π2). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f _ ?X ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f _ X _ wfΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ X _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply red_context_zip, r2.
  Qed.
  Next Obligation.
    eapply reducible_head_decompose in eq1 as d1.
    now simpl_reduce_stack Σ H.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    simpl_reduce_stack Σ wfΣ.
    specialize (isr eq_refl) as (?&_).
    split; auto. intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    now simpl_stacks.
    Unshelve. all: eauto.
  Qed.
  Next Obligation.
    destruct (hΣ _ H) as [wΣ].
    eapply reducible_head_red_zipp in eq1 as r1; eauto.
    destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack Σ H.
    destruct (hx _ H) as [hx'].
    etransitivity ; try eauto.
    eapply conv_cum_conv_ctx.
    - eapply red_conv_cum_r.
      etransitivity; tea.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      rewrite <- d1. now eapply wt_zip_mkapps.
    - eauto.
    Unshelve. all:eauto.
  Qed.
  Next Obligation.
    eapply R_stateR. all: simpl. all: try reflexivity.
    constructor.
    Qed.

  Next Obligation.
    destruct (h _ H), (hΣ _ H).
    eapply ws_cumul_pb_terms_alt in X0 as (argsr&argsr'&[]).
    rewrite !zipp_as_mkApps.
    apply conv_cum_alt; auto.
    constructor; eexists _, _.
    constructor.
    - apply PCUICInductiveInversion.closed_red_mkApps; tea.
      * clear aux nored1. eapply welltyped_zipc_zipp in h1; fvs.
      * clear aux nored1. eapply wt_zip_mkapps in h1; eauto.
        rewrite on_free_vars_mkApps in h1. now apply andb_true_iff in h1.
    - apply PCUICInductiveInversion.closed_red_mkApps; tea.
      * clear aux nored1. eapply welltyped_zipc_zipp in h1; fvs.
      * clear aux nored1 nored2. eapply wt_zip_mkapps in h1; eauto.
        eapply wt_zip_mkapps in h2; eauto.  destruct (hx _ H).
        rewrite (All2_fold_length X0).
        rewrite on_free_vars_mkApps in h2. now apply andb_true_iff in h2.
    - apply eq_term_upto_univ_napp_mkApps; auto.
      rewrite Nat.add_0_r.
      apply All2_length in a.
      rewrite a in eq1.
      eapply cmpb_term_correct; tea.
      + pose proof h1 as Hc. specialize_Σ H. pose proof (hΣ _  H); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
      + pose proof h2 as Hc. specialize_Σ H. pose proof (hΣ _  H); sq.
        apply welltyped_zipc_inv in Hc; eauto.
        apply welltyped_wf in Hc; eauto.
      + now symmetry.
  Qed.

  Equations _isconv (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
            (aux : Aux s Γ t1 π1 t2 π2 f1 f2 h2)
  : Ret s Γ t1 π1 t2 π2 :=
    _isconv Reduction Γ t1 π1 f1 h1 t2 π2 f2 h2 aux :=
      λ { | leq | hx | hv1 | hv2 | hwf1 | hwf2 | _ | _ | _ :=
            _isconv_red Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2 aux } ;

    _isconv Term Γ t1 π1 f1 h1 t2 π2 f2 h2 aux :=
      λ { | leq | hx | hv1 | hv2 | hwf1 | hwf2 | r1 | r2 | _ :=
            _isconv_prog Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2 r1 r2 aux } ;

    _isconv Args Γ t1 π1 f1 h1 t2 π2 f2 h2 aux :=
      λ { | leq | hx | _ | _ | hwf1 | hwf2 | _ | _ | _ :=
            _isconv_args leq Γ t1 π1 f1 h1 t2 π2 f2 h2 hx hwf1 hwf2 aux } ;

    _isconv Fallback Γ t1 π1 f1 h1 t2 π2 f2 h2 aux :=
      λ { | leq | hx | hv1 | hv2 | hwf1 | hwf2 | r1 | r2 | hd :=
            _isconv_fallback Γ leq t1 π1 f1 h1 t2 π2 f2 h2 r1 r2 hd hx hv1 hv2 hwf1 hwf2 aux }.

  Lemma welltyped_R_zipc Σ (wfΣ : abstract_env_ext_rel X Σ) Γ :
    forall x y : pack Γ, welltypedE Σ Γ (zipc (tm1 x) (stk1 x)) -> R Γ y x -> welltypedE Σ Γ (zipc (tm1 y) (stk1 y)).
  Proof using reduce_factsE.
    intros x y H HR.
    pose proof (heΣ := heΣ _ wfΣ). sq.
    destruct x, y; cbn in *.
    red in HR. cbn in HR. red in HR. cbn in HR.
    depind HR.
    - cbn in *.
      eapply cored'_postpone in H as [u' [cor eq]]; [|exact wfΣ].
      destruct eq as [<-].
      eapply (wt_red (wt := welltypedE) (wfP := wf_extE)); [exact heΣ|exact H0|].
      now eapply cored_red.
    - simpl in *. destruct e. now rewrite e.
  Qed.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
    : Ret s Γ t1 π1 t2 π2 :=

    isconv_full s Γ t1 π1 f1 h1 t2 π2 f2 h2 hx :=
      Fix_F (R := R Γ)
            (fun '(mkpack s' t1' π1' t2' π2' f1' f2' h2') =>
              wtp Γ t1' π1' ->
              wtp Γ t2' π2' ->
              Ret s' Γ t1' π1' t2' π2'
            )
            (fun pp f => _)
            (x := mkpack Γ s t1 π1 t2 π2 f1 f2 _)
            _ _ _ _.
  Next Obligation.
    unshelve eapply _isconv. all: try assumption.
    intros s' t1' π1' t2' π2' f1' f2' h1' h2' hx' hR.
    eapply (f (mkpack Γ s' t1' π1' t2' π2' f1' f2' h2')); tea.
    destruct pp. eapply R_irrelevance; tea; cbn. reflexivity.
  Defined.
  Next Obligation.
  match goal with | |- Acc _ ?X => set (u := X) end.
  revert h1.
  change ((forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ (zipc (tm1 u) (stk1 u))) -> Acc (R Γ) u).
  generalize u.
  refine (Acc_intro_generator
            (R:=R Γ)
            (P:=fun u => forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (zipc (tm1 u) (stk1 u)))
            (fun x y Px Hy => _) 1000 _); intros.
  - simpl in *. eapply welltyped_R_zipc; eauto.
  - eapply R_Acc; eassumption.
  Defined.

  Inductive ConversionResultSummary :=
  | ConvSuccess : ConversionResultSummary
  | ConvError : ConversionError -> ConversionResultSummary.

  Definition isconv Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2 :=
    match isconv_full Reduction Γ t1 π1 f1 h1 t2 π2 f2 h2 leq hx hv1 hv2 hwf1 hwf2 I I I with
    | Success _ => ConvSuccess
    | Error e => ConvError e
    end.

  (* I6: [isconv_sound] keeps its statement, over E (η views, ws_cumul_pbE). *)
  Theorem isconv_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2,
      isconv Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2 = ConvSuccess ->
      conv_cumE leq Σ (Γ ,,, stack_context_eta π1) (zipp_eta t1 π1) (zipp_eta t2 π2).
  Proof using Type.
    unfold isconv.
    intros Σ wfΣ Γ leq t1 π1 f1 h1 t2 π2 f2 h2 hx hv1 hv2 hwf1 hwf2.
    destruct isconv_full as [].
    - auto.
    - discriminate.
  Qed.

  Program Definition isconv_term Γ leq t1
    (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ t1) t2
    (h2 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ t2) :=
    isconv Γ leq t1 [] eq_refl h1 t2 [] eq_refl h2 _ eq_refl eq_refl _ _.

  Next Obligation.
    destruct (h1 _ H) as [T ht], (abstract_env_ext_sq_wf _ _ _ H) as [wΣ].
    sq. eapply ws_cumul_ctx_pbE_refl.
    cbn. eapply (@wf_local_closed_contextE _ Σ Γ wΣ).
    now eapply typingE_wf_local.
  Qed.
  Next Obligation.
    destruct (h1 _ H) as [T ht]. sq. cbn. now eapply typingE_wf_local.
  Qed.
  Next Obligation.
    destruct (h2 _ H) as [T ht]. sq. cbn. now eapply typingE_wf_local.
  Qed.

  Theorem isconv_term_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ leq t1 h1 t2 h2,
      isconv_term Γ leq t1 h1 t2 h2 = ConvSuccess ->
      conv_cumE leq Σ Γ t1 t2.
  Proof using Type.
    intros Σ wfΣ Γ leq t1 h1 t2 h2.
    unfold isconv_term. intro h.
    eapply isconv_sound in h; eauto.
  Qed.
  (* K6 row / G7: base's [isconv_complete] and [isconv_term_complete] are deleted.
     Under decision (C) a refusal claims nothing, and [ConversionResult] carries no
     [~P] payload to prove them from. *)

  Transparent reduce_stack.

End Conversion.

(*
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.
Definition default_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined.

Lemma test_conv :
match
  isconv_term (cf := default_checker_flags)
    (nor := default_normal)
     canonical_abstract_env_ext_impl
    {|
      referenced_impl_env_ext :=
        ({|
           universes :=
             (LevelSet.add Level.lzero LevelSet.empty, ConstraintSet.empty);
           declarations := []
         |}, Monomorphic_ctx);
      referenced_impl_ext_wf := TODO "foo"
    |} [] Cumul (tSort (Universe.lType (Universe.make' (Level.lzero, 0))))
    (TODO "") (tSort (Universe.lType (Universe.make' (Level.lzero, 0))))
    (TODO "")
with
| ConvSuccess => "success"
| ConvError _ => TODO "foo"
end = "success".
Proof.
  lazy. reflexivity.
Defined.
*)
