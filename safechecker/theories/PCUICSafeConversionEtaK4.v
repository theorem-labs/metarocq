(* Distributed under the terms of the MIT license. *)
(* K4: the termination measure of the η conversion checker, over the stack of
   [PCUICPositionEta], its well-foundedness, and the descent lemmas the checker's
   obligations use (plan.md §2 I7 revisions 12-15).

   The measure is base's lexicographic [R_aux] (safechecker/theories/
   PCUICSafeConversion.v) on
     (side-1 term, side-1 position, side-2 term, side-2 position, state)
   over the η stack, with the E well-typedness [welltypedE] in [wtp]/[wterm]/[wcored]
   (rev 14, B3 conditions) and base's three descent lemmas [R_positionR],
   [R_positionR2] and [R_stateR] restated for it. [R_aux_Acc]/[R_Acc] are proved over
   [NormalizationInE] ([PCUICSNEta]), through [normalization_uptoE], the E copy of
   [PCUICSN.normalization_upto]. They discharge the descents:

     (1)  the η branch with the λ on side 1            -> R_positionR
     (1') the η branch with the λ on side 2            -> R_positionR2
          (rev 14 NB1: two domains, A in Lambda_bd and A' in Eta_app)
     (2)  the virtual pair of the E _isconv_args', entering at Reduction as in base,
          measured against the entry pack (rev 15 C1/C2):
          frame on side 1 -> R_positionR2, frame on side 2 -> R_positionR
     (3)  the same-constant argument call (prog_view_Const -> isconv_args_raw in
          base)                                         -> R_stateR

   Both η frames are transparent to [zipc] ([Eta_app] by [fill_hole = id],
   [Eta_arg] because its [fill_hole] restores the real term) and are skipped by
   [stack_position], so no descent raises the measure.

   The pack carries a [wf_stack] proof for each side: the widened invariant of rev 12
   (D-b), under which only η frames lie above the last [Eta_arg] and no [Eta_arg] lies
   below the first real frame (an η step on the virtual side pushes [Eta_app] above an
   [Eta_arg]). [stack_pos_wf] then gives a valid position for every state.

   [conv_stack_ctx_eta] (rev 14 NB1) and [conv_stack_ctx_eta_eta_step] (rev 15 C4) are
   here because they read [abstract_env_ext_rel]; their Σ-level content is
   [PCUICPositionEtaTyping.ws_cumul_ctx_pbE_eta_step].

   Section hypothesis: [normalization_in] (the E normalization premise of every E
   section, ENV contract). It has no satisfying instance, and none is possible: it is
   strong normalization of PCUIC with η, an assumption exactly as base [NormalizationIn]
   is for the base checker (see the header of [PCUICSNEta]). *)
From Stdlib Require Import ProofIrrelevance ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality PCUICOnFreeVars
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICSN PCUICUtils PCUICTypingEta PCUICSNEta PCUICContextConversionEta
     PCUICPositionEtaTyping.
From MetaRocq.SafeChecker Require Import PCUICErrors.
(* the abstract environment over wfE/wf_extE (ENV contract), after anything that could
   load base PCUICWfEnv *)
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta.

(* LAST, so that the eta stack shadows the base one for the unqualified names. *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(* The [` x] = [proj1_sig x] notation is dropped from scope by the PCUICPositionEta
   import above; re-declare it locally so the copied order code parses as in base. *)
Local Notation "` x" := (proj1_sig x) (at level 10, format "` x").

(* The E copy of [PCUICSN.normalization_upto] (PCUICSN.v:156-166). *)
Lemma normalization_uptoE {cf} {no : normalizing_flags} (Σ : global_env_ext)
  {normalization : NormalizationInE Σ} Γ u :
  welltypedE Σ Γ u -> Acc (cored' Σ Γ) u.
Proof.
  intros h. eapply Acc_cored_cored'.
  - exact (normalization Γ u h).
  - constructor. reflexivity.
Qed.

(* base [PCUICSafeReduce.Acc_equiv] (PCUICSafeReduce.v:412-418); that file loads base
   PCUICWfEnv, so it is restated here. *)
Lemma Acc_equivE A (R R' : A -> A -> Prop) (Heq : forall a a', R a a' <-> R' a a') a :
  Acc R a -> Acc R' a.
Proof. induction 1 as [a _ IH]. constructor. intros y hy. apply IH. now apply Heq. Qed.

Section ConversionEtaK4.

  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_extE Σ -> Σ ∼_ext X -> NormalizationInE Σ}.

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_extE Σ ∥ := abstract_env_ext_wf _ wfΣ.

  Set Equations Transparent.
  Set Equations With UIP.

  (** The state component of the measure (base, unchanged). *)
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

  (** The base pack, plus the [wf_stack] witness of each side's stack: it is what
      makes [stack_pos_wf] total over the virtual-argument state as well. *)
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

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
  Proof using normalization_in.
    intros Γ [u hu].
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
    pose proof (heΣ _ wfΣ) as [heΣ].
    pose proof (hu _ wfΣ) as h.
    apply (normalization_uptoE Σ (normalization := normalization_in Σ heΣ wfΣ)) in h.
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

  (** * K4's measure, over the PCUICPositionEta stack.

      Lexicographic in: side-1 term (modulo [eqt], ordered by [cored']), side-1
      position, side-2 term, side-2 position, state. *)
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

  (* base [R_aux_Acc] (PCUICSafeConversion.v:203-298), over welltypedE and
     NormalizationInE *)
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
    - pose proof (heΣ _ wfΣ) as [hwf].
      eapply Acc_equivE; try eapply (normalization_uptoE Σ (normalization := normalization_in Σ hwf wfΣ)); eauto.
      split; eauto; intros.
      erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    Unshelve. all: eauto.
  Qed.

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos_wf (tm1 u) (stk1 u) (swf1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos_wf (tm2 u) (stk2 u) (swf2 u)) (only parsing).

  Notation obpack u :=
    (pzt u ; (pps1 u, (pwt u; (pps2 u, st u)))) (only parsing).

  Definition R Γ (u v : pack Γ) :=
    R_aux Γ (obpack u) (obpack v).

  (* base [R_Acc] (PCUICSafeConversion.v:312-320), over welltypedE *)
  Lemma R_Acc :
    forall Γ u,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (zipc (tm1 u) (stk1 u))) ->
      Acc (R Γ) u.
  Proof using normalization_in.
    intros Γ u h.
    eapply Acc_fun with (f := fun x => obpack x).
    apply R_aux_Acc. assumption.
  Qed.

  (** The three descent lemmas the obligations are discharged with. *)

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
    intros Γ [s1 t1 π1 u1 σ1 f1 g1 h1] [s2 t2 π2 u2 σ2 f2 g2 h2] e h. simpl in *.
    eapply R_aux_positionR ; simpl.
    - assumption.
    - assumption.
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
    intros Γ [s1 t1 π1 u1 σ1 f1 g1 h1] [s2 t2 π2 u2 σ2 f2 g2 h2] e1 e2 e3 h.
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
    intros Γ [s1 t1 π1 u1 σ1 f1 g1 h1] [s2 t2 π2 u2 σ2 f2 g2 h2] e1 e2 e3 e4 h.
    simpl in *.
    eapply R_aux_stateR. all: simpl. all: auto.
  Qed.

  (** * K4's acceptance list, discharged. *)

  (** (1) The η branch with the λ ON SIDE 1 (rev 14 NB1: the λ's domain [A] and the
      pushed frame's domain [A'] are independent; the side-2 frame is
      [Eta_app na (eta_rename π1 0 A)] at the call site).

      Side 1 descends into the λ body with the base [Lambda_bd] frame, so its [zipc]
      reassembles the very same term ([eqt]) and its position strictly deepens; the
      non-λ side 2 only gains the read-time [Eta_app] frame after its spine, which is
      transparent to both, so [A'] is never read. Components 1-2 decrease:
      [R_positionR]. *)
  Lemma K4_eta_branch_lambda_left :
    forall Γ na A A' b π1 t2 args ρ2
      (f1  : wf_stack (Lambda_bd na A :: π1))
      (f1' : wf_stack π1)
      (f2  : wf_stack (appstack args (Eta_app na A' :: ρ2)))
      (f2' : wf_stack (appstack args ρ2))
      (h2  : wtp Γ t2 (appstack args (Eta_app na A' :: ρ2)))
      (h2' : wtp Γ t2 (appstack args ρ2)),
      R Γ (mkpack Γ Reduction b (Lambda_bd na A :: π1)
                    t2 (appstack args (Eta_app na A' :: ρ2)) f1 f2 h2)
          (mkpack Γ Fallback (tLambda na A b) π1
                    t2 (appstack args ρ2) f1' f2' h2').
  Proof using Type.
    intros Γ na A A' b π1 t2 args ρ2 f1 f1' f2 f2' h2 h2'.
    eapply R_positionR.
    - constructor. apply zipc_Lambda_bd.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_Lambda_bd.
  Qed.

  (** (1') The η branch with the λ on side 2 (two domains, as (1)).

      Side 1 is the non-λ side: it only gains the [Eta_app] frame after its spine,
      so its term and its position are unchanged; side 2 descends by [Lambda_bd],
      its term is unchanged and its position strictly deepens. Components 1-2 are
      equal and components 3-4 decrease: [R_positionR2]. *)
  Lemma K4_eta_branch_lambda_right :
    forall Γ t1 args ρ1 na A A' b π2
      (f1  : wf_stack (appstack args (Eta_app na A' :: ρ1)))
      (f1' : wf_stack (appstack args ρ1))
      (f2  : wf_stack (Lambda_bd na A :: π2))
      (f2' : wf_stack π2)
      (h2  : wtp Γ b (Lambda_bd na A :: π2))
      (h2' : wtp Γ (tLambda na A b) π2),
      R Γ (mkpack Γ Reduction t1 (appstack args (Eta_app na A' :: ρ1))
                    b (Lambda_bd na A :: π2) f1 f2 h2)
          (mkpack Γ Fallback t1 (appstack args ρ1)
                    (tLambda na A b) π2 f1' f2' h2').
  Proof using Type.
    intros Γ t1 args ρ1 na A A' b π2 f1 f1' f2 f2' h2 h2'.
    eapply R_positionR2.
    - constructor. apply zipc_appstack_Eta_app.
    - cbn [stack_pos_wf proj1_sig]. apply stack_position_appstack_Eta_app.
    - constructor. apply zipc_Lambda_bd.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_Lambda_bd.
  Qed.

  (* the real side's descent by [App_r] into the entry spine [ca ++ u :: a] reassembles
     the entry term *)
  Lemma zipc_App_r_appstack_entry t ca u a π :
    zipc u (App_r (mkApps t ca) :: appstack a π) = zipc t (appstack (ca ++ u :: a) π).
  Proof using Type.
    cbn [zipc fill_hole]. rewrite !zipc_appstack mkApps_app. reflexivity.
  Qed.

  (** (2) The virtual pair of the E [_isconv_args'] (rev 15 C1), measured against the
      entry pack (rev 15 C2); the entry spine is written [ca ++ u :: a].

      Frame on side 1: side 1's focus is the virtual [tRel k] under [Eta_arg t1 []],
      so its [zipc] and its position are those of the entry ([zipc_Eta_arg_nil],
      [stack_position_Eta_arg]); side 2 descends by [App_r] into its real argument,
      whose term is the entry's and whose position strictly deepens
      ([positionR_App_r_appstack_gen]): [R_positionR2]. *)
  Lemma K4_virtual_descent_frame_left :
    forall Γ t1 l1 θ1 t2 ca2 u2 a2 π2 k
      (f1  : wf_stack (Eta_arg t1 [] :: appstack l1 θ1)) (f1' : wf_stack (appstack l1 θ1))
      (f2  : wf_stack (App_r (mkApps t2 ca2) :: appstack a2 π2))
      (f2' : wf_stack (appstack (ca2 ++ u2 :: a2) π2))
      (h2  : wtp Γ u2 (App_r (mkApps t2 ca2) :: appstack a2 π2))
      (h2' : wtp Γ t2 (appstack (ca2 ++ u2 :: a2) π2)),
      R Γ (mkpack Γ Reduction (tRel k) (Eta_arg t1 [] :: appstack l1 θ1)
                    u2 (App_r (mkApps t2 ca2) :: appstack a2 π2) f1 f2 h2)
          (mkpack Γ Args t1 (appstack l1 θ1) t2 (appstack (ca2 ++ u2 :: a2) π2) f1' f2' h2').
  Proof using Type.
    intros Γ t1 l1 θ1 t2 ca2 u2 a2 π2 k f1 f1' f2 f2' h2 h2'.
    eapply R_positionR2.
    - constructor. apply zipc_Eta_arg_nil.
    - cbn [stack_pos_wf proj1_sig]. apply stack_position_Eta_arg.
    - change (eqt (zipc u2 (App_r (mkApps t2 ca2) :: appstack a2 π2))
                  (zipc t2 (appstack (ca2 ++ u2 :: a2) π2))).
      constructor. apply zipc_App_r_appstack_entry.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_App_r_appstack_gen.
      rewrite length_app. cbn. lia.
  Qed.

  (** Frame on side 2 (the sides exchanged): side 1 descends by [App_r] into its real
      argument, so components 1-2 already decrease, and side 2's shape is irrelevant:
      [R_positionR]. *)
  Lemma K4_virtual_descent_frame_right :
    forall Γ t1 ca1 u1 a1 θ1 t2 π2 k
      (f1  : wf_stack (App_r (mkApps t1 ca1) :: appstack a1 θ1))
      (f1' : wf_stack (appstack (ca1 ++ u1 :: a1) θ1))
      (f2  : wf_stack (Eta_arg t2 [] :: π2)) (f2' : wf_stack π2)
      (h2  : wtp Γ (tRel k) (Eta_arg t2 [] :: π2)) (h2' : wtp Γ t2 π2),
      R Γ (mkpack Γ Reduction u1 (App_r (mkApps t1 ca1) :: appstack a1 θ1)
                    (tRel k) (Eta_arg t2 [] :: π2) f1 f2 h2)
          (mkpack Γ Args t1 (appstack (ca1 ++ u1 :: a1) θ1) t2 π2 f1' f2' h2').
  Proof using Type.
    intros Γ t1 ca1 u1 a1 θ1 t2 π2 k f1 f1' f2 f2' h2 h2'.
    eapply R_positionR.
    - constructor. apply zipc_App_r_appstack_entry.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_App_r_appstack_gen.
      rewrite length_app. cbn. lia.
  Qed.

  (** (3) The same-constant argument call ([prog_view_Const] -> [isconv_args_raw]
      in base).

      Both sides keep their term, stack and position; only the state moves from
      [Term] to [Args]. A measure on the terms alone rises on this call (on
      [c (fun x => x)] against [c (fun y => y)]); the base state component carries
      it: with the η frames skipped by [stack_position], nothing here changed, and
      [R_stateR] closes it. *)
  Lemma K4_same_constant_args_call :
    forall Γ t1 π1 t2 π2 (f1 : wf_stack π1) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2),
      R Γ (mkpack Γ Args t1 π1 t2 π2 f1 f2 h2)
          (mkpack Γ Term t1 π1 t2 π2 f1 f2 h2).
  Proof using Type.
    intros Γ t1 π1 t2 π2 f1 f2 h2.
    eapply R_stateR.
    - constructor. reflexivity.
    - reflexivity.
    - constructor. reflexivity.
    - reflexivity.
    - cbn. constructor.
  Qed.

End ConversionEtaK4.

(** * The η context relation of the conversion state (rev 14 NB1, rev 15 C4). *)
Section ConvStackCtxEta.
  Context {cf : checker_flags} {X_type : abstract_env_impl}.

  (* rev 14 (NB1): the conversion state compares the η contexts. [ws_cumul_ctx_pbE] at
     frac/eta has no [FInstFollowKernel] argument (PCUICContextConversionEta.v:44). *)
  Definition conv_stack_ctx_eta (X : X_type.π2.π1) (Γ : context) (π1 π2 : stack) : Prop :=
    forall Σ, abstract_env_ext_rel X Σ ->
      ∥ ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta π1) (Γ ,,, stack_context_eta π2) ∥.

  (* rev 15 (C4) *)
  Lemma conv_stack_ctx_eta_eta_step X Γ na A π_i args ρ_j :
    (forall Σ, abstract_env_ext_rel X Σ ->
       is_open_term (Γ ,,, stack_context_eta π_i) (eta_rename π_i 0 A)) ->
    conv_stack_ctx_eta X Γ π_i (appstack args ρ_j) ->
    conv_stack_ctx_eta X Γ (Lambda_bd na A :: π_i) (appstack args (Eta_app na (eta_rename π_i 0 A) :: ρ_j)).
  Proof.
    intros hA hx Σ wfΣ. destruct (hx Σ wfΣ) as [h]. constructor.
    exact (ws_cumul_ctx_pbE_eta_step Σ Γ na A π_i args ρ_j (hA Σ wfΣ) h).
  Qed.
End ConvStackCtxEta.
