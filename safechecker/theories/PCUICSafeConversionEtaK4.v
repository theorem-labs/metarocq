(* Distributed under the terms of the MIT license. *)
(* BET-315 eta lane (L5), row K4: the TERMINATION MEASURE for the eta branch, stated
   over the PCUICPositionEta stack, and its acceptance obligations.

   K4 is the plan's declared hypothesis (plan.md rev 11 §3, risk rank 2). This file
   states the measure in Coq — the base lexicographic [R_aux] of
   safechecker/theories/PCUICSafeConversion.v:191, on
     (side-1 term, side-1 position, side-2 term, side-2 position, state)
   — over the new stack, together with the three descent lemmas [R_positionR] (:395),
   [R_positionR2] (:467) and [R_stateR] (:512), and then DISCHARGES the acceptance
   list of K4 with them:

     (1)  the eta branch with the lambda on side 1   -> R_positionR
     (1') the eta branch with the lambda on side 2   -> R_positionR2
     (2)  the virtual-argument descent of the E _isconv_args', entering at Reduction
          as in base (gate F-1), frame on either side -> R_positionR2 / R_stateR
     (3)  the same-constant argument call (prog_view_Const -> isconv_args_raw,
          PCUICSafeConversion.v:3390-3393, the call that killed revision 3-4's outer
          measure mu)                                  -> R_stateR

   Both eta frames are transparent to [zipc] ([Eta_app] by [fill_hole = id],
   [Eta_arg] because its [fill_hole] restores the real term) and are SKIPPED by
   [stack_position], so no descent raises the measure: each one leaves a prefix of the
   lexicographic tuple equal and strictly decreases the next component.

   The pack carries a [wf_stack] proof for each side (PCUICPositionEta): a normal
   state's stack has no [Eta_arg]; the virtual-argument state's stack has the
   [Eta_arg] as head with a no-[Eta_arg] tail. [stack_pos_wf] then gives a valid
   position for EVERY pack, the virtual one included.

   Well-foundedness of [R_aux] ([R_aux_Acc], :217) is the base proof over
   [NormalizationIn] and is untouched by the frames: it is independent of the stack
   type, depending only on [cored'], [posR] and [stateR]. It is not restated here
   because no obligation below needs it. *)
From Stdlib Require Import ProofIrrelevance ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICSN PCUICUtils.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv.

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

Section ConversionEtaK4.

  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

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

  Notation wtp Γ t π :=
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc t π)) (only parsing).

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

  Definition wterm Γ := { t : term | forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` u) (` v).

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

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos_wf (tm1 u) (stk1 u) (swf1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos_wf (tm2 u) (stk2 u) (swf2 u)) (only parsing).

  Notation obpack u :=
    (pzt u ; (pps1 u, (pwt u; (pps2 u, st u)))) (only parsing).

  Definition R Γ (u v : pack Γ) :=
    R_aux Γ (obpack u) (obpack v).

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

  (** (1) The eta branch with the LAMBDA ON SIDE 1.

      Side 1 descends into the lambda body with the base [Lambda_bd] frame, so its
      [zipc] reassembles the very same term ([eqt]) and its position strictly
      deepens; the non-lambda side 2 only gains the read-time [Eta_app] frame after
      its spine, which is transparent to both. Components 1-2 decrease, so this is
      [R_positionR]. *)
  Lemma K4_eta_branch_lambda_left :
    forall Γ na A b π1 t2 args ρ2
      (f1  : wf_stack (Lambda_bd na A :: π1))
      (f1' : wf_stack π1)
      (f2  : wf_stack (appstack args (Eta_app na A :: ρ2)))
      (f2' : wf_stack (appstack args ρ2))
      (h2  : wtp Γ t2 (appstack args (Eta_app na A :: ρ2)))
      (h2' : wtp Γ t2 (appstack args ρ2)),
      R Γ (mkpack Γ Reduction b (Lambda_bd na A :: π1)
                    t2 (appstack args (Eta_app na A :: ρ2)) f1 f2 h2)
          (mkpack Γ Fallback (tLambda na A b) π1
                    t2 (appstack args ρ2) f1' f2' h2').
  Proof using Type.
    intros Γ na A b π1 t2 args ρ2 f1 f1' f2 f2' h2 h2'.
    eapply R_positionR.
    - constructor. apply zipc_Lambda_bd.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_Lambda_bd.
  Qed.

  (** (1') The eta branch with the LAMBDA ON SIDE 2.

      Side 1 is the non-lambda side: it only gains the [Eta_app] frame after its
      spine, so its term AND its position are unchanged; side 2 descends by
      [Lambda_bd], its term is unchanged and its position strictly deepens.
      Components 1-2 are equal and components 3-4 decrease, so this is
      [R_positionR2] — not [R_positionR], which would need a side-1 decrease that
      does not exist here (gate F-1's objection to the revision 6-9 entry). *)
  Lemma K4_eta_branch_lambda_right :
    forall Γ t1 args ρ1 na A b π2
      (f1  : wf_stack (appstack args (Eta_app na A :: ρ1)))
      (f1' : wf_stack (appstack args ρ1))
      (f2  : wf_stack (Lambda_bd na A :: π2))
      (f2' : wf_stack π2)
      (h2  : wtp Γ b (Lambda_bd na A :: π2))
      (h2' : wtp Γ (tLambda na A b) π2),
      R Γ (mkpack Γ Reduction t1 (appstack args (Eta_app na A :: ρ1))
                    b (Lambda_bd na A :: π2) f1 f2 h2)
          (mkpack Γ Fallback t1 (appstack args ρ1)
                    (tLambda na A b) π2 f1' f2' h2').
  Proof using Type.
    intros Γ t1 args ρ1 na A b π2 f1 f1' f2 f2' h2 h2'.
    eapply R_positionR2.
    - constructor. apply zipc_appstack_Eta_app.
    - cbn [stack_pos_wf proj1_sig]. apply stack_position_appstack_Eta_app.
    - constructor. apply zipc_Lambda_bd.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_Lambda_bd.
  Qed.

  (** (2) The VIRTUAL-ARGUMENT DESCENT of the E [_isconv_args'], entering at
      [Reduction] as in base (gate F-1).

      Frame on side 1: side 1's focus becomes the virtual [tRel 0] under the
      focus-dropping [Eta_arg], so its [zipc] is the unchanged real term and its
      position is unchanged (the fold skips the frame); side 2 descends by [App_r]
      into its real argument (one-sided-virtual lemma), so its position strictly
      deepens. Components 1-2 equal, components 3-4 decrease: [R_positionR2]. *)
  Lemma K4_virtual_descent_frame_left :
    forall Γ t1 args na A ρ1 t2 u2 l2 π2
      (f1  : wf_stack (Eta_arg t1 args :: Eta_app na A :: ρ1))
      (f1' : wf_stack (Eta_app na A :: ρ1))
      (f2  : wf_stack (App_r t2 :: appstack l2 π2))
      (f2' : wf_stack (appstack (u2 :: l2) π2))
      (h2  : wtp Γ u2 (App_r t2 :: appstack l2 π2))
      (h2' : wtp Γ t2 (appstack (u2 :: l2) π2)),
      R Γ (mkpack Γ Reduction (tRel 0) (Eta_arg t1 args :: Eta_app na A :: ρ1)
                    u2 (App_r t2 :: appstack l2 π2) f1 f2 h2)
          (mkpack Γ Args (mkApps t1 args) (Eta_app na A :: ρ1)
                    t2 (appstack (u2 :: l2) π2) f1' f2' h2').
  Proof using Type.
    intros Γ t1 args na A ρ1 t2 u2 l2 π2 f1 f1' f2 f2' h2 h2'.
    eapply R_positionR2.
    - constructor. reflexivity.
    - reflexivity.
    - constructor. reflexivity.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_App_r_appstack.
  Qed.

  (** Frame on side 2 (the sides exchanged): side 1 descends by [App_r] into its
      real argument, so components 1-2 already decrease: [R_positionR]. *)
  Lemma K4_virtual_descent_frame_right :
    forall Γ t1 u1 l1 π1 t2 args na A ρ2
      (f1  : wf_stack (App_r t1 :: appstack l1 π1))
      (f1' : wf_stack (appstack (u1 :: l1) π1))
      (f2  : wf_stack (Eta_arg t2 args :: Eta_app na A :: ρ2))
      (f2' : wf_stack (Eta_app na A :: ρ2))
      (h2  : wtp Γ (tRel 0) (Eta_arg t2 args :: Eta_app na A :: ρ2))
      (h2' : wtp Γ (mkApps t2 args) (Eta_app na A :: ρ2)),
      R Γ (mkpack Γ Reduction u1 (App_r t1 :: appstack l1 π1)
                    (tRel 0) (Eta_arg t2 args :: Eta_app na A :: ρ2) f1 f2 h2)
          (mkpack Γ Args t1 (appstack (u1 :: l1) π1)
                    (mkApps t2 args) (Eta_app na A :: ρ2) f1' f2' h2').
  Proof using Type.
    intros Γ t1 u1 l1 π1 t2 args na A ρ2 f1 f1' f2 f2' h2 h2'.
    eapply R_positionR.
    - constructor. reflexivity.
    - cbn [stack_pos_wf proj1_sig]. apply positionR_App_r_appstack.
  Qed.

  (** The same descent when the state is what moves instead (the virtual pair reached
      with both positions already equal): [R_stateR]. *)
  Lemma K4_virtual_descent_stateR :
    forall Γ t1 args na A ρ1 t2 π2
      (f1  : wf_stack (Eta_arg t1 args :: Eta_app na A :: ρ1))
      (f1' : wf_stack (Eta_app na A :: ρ1))
      (f2  : wf_stack π2)
      (h2  : wtp Γ t2 π2),
      R Γ (mkpack Γ Args (tRel 0) (Eta_arg t1 args :: Eta_app na A :: ρ1)
                    t2 π2 f1 f2 h2)
          (mkpack Γ Term (mkApps t1 args) (Eta_app na A :: ρ1)
                    t2 π2 f1' f2 h2).
  Proof using Type.
    intros Γ t1 args na A ρ1 t2 π2 f1 f1' f2 h2.
    eapply R_stateR.
    - constructor. reflexivity.
    - reflexivity.
    - constructor. reflexivity.
    - reflexivity.
    - cbn. constructor.
  Qed.

  (** (3) The SAME-CONSTANT ARGUMENT CALL
      ([prog_view_Const] -> [isconv_args_raw], PCUICSafeConversion.v:3390-3393).

      Both sides keep their term, stack and position; only the state moves from
      [Term] to [Args]. This is the call on which revision 3-4's outer measure [mu]
      ROSE (it rises on [c (fun x => x)] vs [c (fun y => y)], plan.md B2(c)), which
      is why [mu] stays deleted and the base state component carries it: with the eta
      frames skipped by [stack_position], nothing here changed, and [R_stateR]
      closes it. *)
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
