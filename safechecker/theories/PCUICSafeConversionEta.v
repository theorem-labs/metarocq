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
   - REDUCE (EtaReduce, entries 06:58Z and 07:35Z): the bridge PCUICSafeReduceEtaBridge over
     PCUICSafeReduceEta (base PCUICPosition.stack, welltypedE): [reduce_args_E flags X_type X Γ t
     args h] with [h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ (PCUICPosition.zip
     (t, PCUICPosition.appstack args []))]; facts [reduce_args_E_sound/_whnf/_isred/_Req/_spec],
     [reduce_stack_app_only], [app_only_zip], [stack_context_appstack_bridge],
     [zipp_appstack_bridge], [reduce_stack_vass], [reduce_args_E_vass], and (07:35Z, statement
     change) [stack_position_appstack_bridge args args'] = an iff between the two positionR
     orders on [appstack args' []]/[appstack args []]; the named E-facts hypothesis is the class
     instance [reduce_factsE : ReduceTypedFactsE] (a Prop: the nine GENUINE fields of
     [ReduceTypedFacts] at [welltypedE]); the machine's [ReduceTypedFacts welltypedE wf_extE] is
     the bridge's instance [reduce_typed_facts_E], built from it and six proved fields;
     [reduce_env_facts_E : ReduceEnvFacts welltypedE wf_extE] is PROVED in the bridge. The
     other E use of the machine is [reduce_termE] below = [PCUICSafeReduceEta.reduce_term
     (wt := welltypedE) (wfP := wf_extE) (normalization_in := normalization_in)]. The
     conversion calls reduction ONLY through these (plan rev 14 "B3 conditions").
   - POSITION (EtaPosK4, entries 06:48Z and 07:39Z, @ 240372c9): plan I7 rev 12-15 Coq text
     verbatim ([wf_stack], [eta_run], [drop_eta_run], [eta_virtuals], [eta_rename],
     [decompose_stack_eta], [zipp_eta], [stack_entry_context_eta se below], [stack_context_eta],
     [virtual_focus], [focus_context], [is_nil], [virt_ok], [eta_ren], [reducible_head_shape]);
     typed lemmas in PCUICPositionEtaTyping.
   - K4 (EtaPosK4, PCUICSafeConversionEtaK4 @ 240372c9): [pack] with the [wf_stack] fields
     [swf1]/[swf2], [R_aux], [R], [R_Acc] (premise [normalization_in] as above), [R_positionR],
     [R_positionR2], [R_stateR], the descents [K4_eta_branch_lambda_left/_right],
     [K4_virtual_descent_frame_left/_right], [K4_same_constant_args_call], and
     [conv_stack_ctx_eta X Γ π1 π2 := forall Σ, abstract_env_ext_rel X Σ ->
     ∥ ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta π1) (Γ ,,, stack_context_eta π2) ∥].
     Base's [R_aux_irrelevance], [R_irrelevance], [R_cored], [R_aux_cored2], [R_cored2] over the
     K4 pack are in K4 since 767d50c6 (CONTRACTS K4 entry 07:47Z).
   HINT PARITY (registrations that differ from base PCUICSafeConversion.v):
   - conv_cum_trans -> E twin conv_cumE_trans (ClosedBodies), registered as base does
     (top-level plain [Instance]).
   - eqt_refl (base: [Local Instance] in the section, for the local measure) -> none here,
     because this file defines no [eqt]: the measure, [eqt] and its [Local Instance eqt_refl]
     are in PCUICSafeConversionEtaK4, which declares them as base does.
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
     PCUICEtaK6EtaStep PCUICSigmaCalculus PCUICRenameDef PCUICPositionEtaTyping PCUICClosedTypEta
     PCUICRenameTypEta PCUICTypingEtaInd.
(* Loaded, not imported (no shadowing): the E twins of base PCUICConversion's context lemmas,
   used qualified by slice B's [inst_case_ws_cumul_ctx_pbE]. *)
From MetaRocq.PCUIC Require PCUICWsCumulEtaCtx.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfReductionEta PCUICSafeReduceEta
     PCUICSafeReduceEtaBridge PCUICSafeConversionEtaK4.
(* LAST among the stack providers, so the η stack shadows the base one. *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.
(* The E errors (EtaStackRefusal) shadow base PCUICErrors. *)
From MetaRocq.SafeChecker Require Import PCUICErrorsEta.
(* The E view algebra and the typed-facts class ConvTypedFacts (EtaConv's helper file), and
   K1's MustExpand (EtaK1). *)
From MetaRocq.SafeChecker Require Import PCUICSafeConversionEtaFacts PCUICMustExpandEta.
(* The proved fields of [ConvTypedFacts] at [welltypedE] (qualified names; nothing imported). *)
From MetaRocq.SafeChecker Require PCUICEtaTypedFactsProved.
(* LAST (ENV contract). *)
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(* The E counterpart of base [conv_cum], and of base's [conv_cum_trans] instance, registered
   as base registers it (top level, plain [Instance]). Base needs [wf Σ]; the E environment
   gives [ClosedBodies Σ] ([abstract_env_ext_closed_bodies]), all A3's transitivity needs. *)
Definition conv_cumE {cf : checker_flags} leq Σ Γ t u := ∥ ws_cumul_pbE leq Σ Γ t u ∥.

Instance conv_cumE_trans {cf leq} {Σ : global_env_ext} {Γ} :
  ClosedBodies Σ -> RelationClasses.Transitive (@conv_cumE cf leq Σ Γ).
Proof.
  intros cb x y z [h1] [h2]. constructor. etransitivity; eassumption.
Qed.

#[global]
Instance red_brs_refl Σ p Γ: CRelationClasses.Reflexive (@red_brs Σ p Γ).
Proof.
  intros brs.
  eapply All2_same; unfold on_Trel; split; reflexivity.
Qed.

(* [ConvTypedFacts welltypedE wf_extE] from its GENUINE field ([PCUICSafeConversionEtaFacts.
   ConvTypedFactsE], the named hypothesis [conv_factsE] of section [Conversion]) and the two fields
   proved in [PCUICEtaTypedFactsProved]. The kernel checks [ctf_contextE] against [ctf_context] at
   [welltypedE]/[wf_extE]. An instance, so the section finds [ConvTypedFacts welltypedE wf_extE]
   from its hypothesis; [Qed]: opaque, as the section variable it replaces. *)
#[export] Instance conv_typed_facts_E {cf : checker_flags} {G : ConvTypedFactsE} :
  ConvTypedFacts welltypedE wf_extE.
Proof.
  constructor.
  - exact ctf_contextE.
  - exact PCUICEtaTypedFactsProved.ctf_case_brs_length_proved.
  - exact PCUICEtaTypedFactsProved.ctf_wf_universes_proved.
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

  (* REDUCE contract: the named E-facts hypothesis of the reduction machine, the nine GENUINE
     fields of EtaReduce's class at welltypedE ([ReduceTypedFactsE]; T1/T6/W-c facts); the
     machine's [ReduceTypedFacts welltypedE wf_extE] is the bridge's instance
     [reduce_typed_facts_E], built from it and six proved fields. Base instance of the same
     statements: [reduce_typed_facts_base], restated as [reduce_factsE_base_inst] after the
     section. *)
  Context {reduce_factsE : ReduceTypedFactsE}.

  (* The named typed facts of the conversion itself: the GENUINE field [ctf_contextE] (plan row
     T6) of [ConvTypedFactsE]; [ConvTypedFacts welltypedE wf_extE] is [conv_typed_facts_E] above,
     whose fields [ctf_case_brs_length] and [ctf_wf_universes] are proved. Base instance of the
     same statement: [conv_typed_facts_base] in PCUICSafeConversionEtaFacts, restated as
     [conv_factsE_base_inst] after the section. *)
  Context {conv_factsE : ConvTypedFactsE}.

  (* EtaPosK4's section EtaTypingE (PCUICPositionEtaTyping) takes two named hypotheses;
     its lemmas [wf_localE_push_real] (hwf after a real binder push), [wf_localE_eta_step]
     (hwf after the η step) and [eta_rename_typing] are REUSED here, not restated.
     - [typingE_rename_P] is PROVED there (a lemma of PCUICPositionEtaTyping, from
       [typing_rename_PE] of Typing/PCUICRenameTypEta), so [wf_localE_push_real] and
       [eta_rename_typing] no longer take it.
     - [closed_context_conversionE] is a named hypothesis in SQUASHED form (stream lead's
       approval, 11:50Z: a Type-valued section parameter would survive extraction as an argument
       of [isconv_term]); every use destructs it inside a Prop goal. Satisfying instance: the
       squash of EtaPosK4's base instance [closed_context_conversion_inst] (section
       EtaTypingBase): (1) it shows the hypothesis is consistent and the lemmas are about
       something real; (2) it does NOT discharge the typingE instantiation, which waits for row
       T0 (context conversion over typingE).
     - [welltypedE_context] concludes a Prop ([welltypedE]); unchanged. Its instance is
       EtaPosK4's [welltyped_context_inst] (base, with the same two sentences; rows T6/T2a). *)
  Context (closed_context_conversionE : ∥ forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T ∥).
  Context (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    no_Eta_arg (snd t) -> welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t)).

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_extE Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ ClosedBodies Σ ∥ := abstract_env_ext_closed_bodies _ _ _ wfΣ.

  (* REDUCE contract (CONTRACTS.md 07:35Z item 5): the abstract machine's [reduce_term] at
     [wt := welltypedE], [wfP := wf_extE]; used at the two discriminant sites of the Case and
     Proj views (sites 4/5 of the 11), whose results are only compared by [eqb_term]. *)
  Definition reduce_termE (flags : RedFlags.t) (Γ : context) (t : term)
    (h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ t) : term :=
    PCUICSafeReduceEta.reduce_term (wt := welltypedE) (wfP := wf_extE)
      (normalization_in := normalization_in) flags X_type X Γ t h.

  Set Equations Transparent.
  Set Equations With UIP.

  (* K4 (EtaPosK4, PCUICSafeConversionEtaK4 @ 240372c9): the measure over the η stack, with
     its section variables applied. [state], [stateR], [eqt] take no section variable. *)
  Notation wtp Γ t π :=
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (zipc t π)) (only parsing).

  Local Notation pack := (PCUICSafeConversionEtaK4.pack X_type X).
  Local Notation mkpack := (PCUICSafeConversionEtaK4.mkpack X_type X).
  (* K4's [Arguments st {_} _] are section-local, so Γ is explicit after the section: pass it as _. *)
  Local Notation st := (PCUICSafeConversionEtaK4.st X_type X _).
  Local Notation tm1 := (PCUICSafeConversionEtaK4.tm1 X_type X _).
  Local Notation stk1 := (PCUICSafeConversionEtaK4.stk1 X_type X _).
  Local Notation tm2 := (PCUICSafeConversionEtaK4.tm2 X_type X _).
  Local Notation stk2 := (PCUICSafeConversionEtaK4.stk2 X_type X _).
  Local Notation swf1 := (PCUICSafeConversionEtaK4.swf1 X_type X _).
  Local Notation swf2 := (PCUICSafeConversionEtaK4.swf2 X_type X _).
  Local Notation wth := (PCUICSafeConversionEtaK4.wth X_type X _).
  Local Notation wterm := (PCUICSafeConversionEtaK4.wterm X_type X).
  Local Notation R_aux := (PCUICSafeConversionEtaK4.R_aux X_type X).
  Local Notation R := (PCUICSafeConversionEtaK4.R X_type X).
  Local Notation R_positionR := (PCUICSafeConversionEtaK4.R_positionR X_type X).
  Local Notation R_positionR2 := (PCUICSafeConversionEtaK4.R_positionR2 X_type X).
  Local Notation R_stateR := (PCUICSafeConversionEtaK4.R_stateR X_type X).
  Local Notation R_aux_positionR := (PCUICSafeConversionEtaK4.R_aux_positionR X_type X).
  Local Notation K4_eta_branch_lambda_left := (PCUICSafeConversionEtaK4.K4_eta_branch_lambda_left X_type X).
  Local Notation K4_eta_branch_lambda_right := (PCUICSafeConversionEtaK4.K4_eta_branch_lambda_right X_type X).
  Local Notation K4_virtual_descent_frame_left := (PCUICSafeConversionEtaK4.K4_virtual_descent_frame_left X_type X).
  Local Notation K4_virtual_descent_frame_right := (PCUICSafeConversionEtaK4.K4_virtual_descent_frame_right X_type X).
  Local Notation K4_same_constant_args_call := (PCUICSafeConversionEtaK4.K4_same_constant_args_call X_type X).
  Local Notation R_irrelevance := (PCUICSafeConversionEtaK4.R_irrelevance X_type X).
  Local Notation R_cored := (PCUICSafeConversionEtaK4.R_cored X_type X).
  Local Notation R_cored2 := (PCUICSafeConversionEtaK4.R_cored2 X_type X).

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos_wf (tm1 u) (stk1 u) (swf1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos_wf (tm2 u) (stk2 u) (swf2 u)) (only parsing).

  Lemma R_Acc Γ u :
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltypedE Σ Γ (zipc (tm1 u) (stk1 u))) ->
    Acc (R Γ) u.
  Proof using normalization_in.
    exact (@PCUICSafeConversionEtaK4.R_Acc _ _ X_type X normalization_in Γ u).
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).


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

  (* rev 14 NB1: the conversion state compares the η contexts (K4's definition). *)
  Notation conv_stack_ctx Γ π1 π2 :=
    (PCUICSafeConversionEtaK4.conv_stack_ctx_eta X Γ π1 π2) (only parsing).

  (* [conv_cumE] and its transitivity instance [conv_cumE_trans] are at the top of the file. *)

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

  (* E: reduction is called only through [reduce_args_E] (REDUCE contract); its four facts
     (used by slice C's fixpoint-unfolding obligations). *)
  Ltac reduce_args_facts Σ wfΣ :=
    repeat
      match goal with
      | [H: (?a, ?b) = reduce_args_E ?f ?XT ?X ?Γ ?t ?args ?h |- _] =>
        let rid := fresh "r" in
        let whid := fresh "w" in
        let isr := fresh "isr" in
        pose proof (reduce_args_E_sound f XT X Σ wfΣ Γ t args h) as [rid];
        pose proof (reduce_args_E_whnf f XT X Σ wfΣ Γ t args h) as [whid];
        pose proof (reduce_args_E_isred f XT X Γ t args h) as isr;
        rewrite <- H in rid, whid, isr; cbn in rid, whid, isr;
        clear H
      end.

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

  (* The invariant battery for the threaded invariants (wf_stack, virt_ok, no_Eta_arg under
     the T1/T3 guards and the G2 check, list bookkeeping). On the goal dump dump14 it closes
     62 of the 359 obligations the base obligation tactic leaves (lanes/eta/etak/EtaConv.md). *)
  Ltac etak_pre := intros; unfold rebuilt_ok, eta_head_ok in *;
    repeat match goal with
    | H : true = _ |- _ => symmetry in H
    | H : (_ && _) = true |- _ => apply andb_prop in H as [? ?]
    | H : is_true (_ && _) |- _ => apply andb_prop in H as [? ?]
    end.
  (* Late-bound extension of the battery: [fail] here, redefined after the slice D helpers
     (wf_stack/virt_ok of an App_r push, welltypedness of an App_r state) so that those
     obligations are closed at definition time: a pending obligation inside the pack of an R
     obligation of a structurally recursive definition would carry the recursive prototype. *)
  Ltac etak_hint_extra := fail.
  Ltac etak_hint := first
    [ solve [ etak_pre; cbn [no_Eta_arg wf_stack is_eta_frame is_Eta_arg negb andb orb] in *;
              first [ assumption | reflexivity | discriminate | congruence ] ]
    | solve [ etak_pre; unfold virt_ok; rewrite ?no_Eta_arg_appstack;
              cbn [no_Eta_arg is_Eta_arg negb andb orb];
              repeat match goal with H : no_Eta_arg _ = true |- _ => rewrite H end; reflexivity ]
    | solve [ etak_pre; first [ apply wf_stack_no_Eta_arg | eapply virt_ok_reduce
                              | eapply virt_ok_eta_step | eapply wf_stack_eta_step ]; eauto 3 ]
    | solve [ etak_pre; subst; rewrite <- ?app_assoc; reflexivity ]
    | solve [ etak_pre; rewrite ?stack_context_eta_appstack ?stack_context_eta_Eta_arg_appstack in *;
              eauto 3 ]
    | solve [ intros; cbn in *; eauto 3 ]
    | solve [ etak_hint_extra ] ].
  Ltac etak_base_obl := Tactics.program_simplify; CoreTactics.equations_simpl;
    try Tactics.program_solve_wf.
  Ltac etak_obl := first [ solve [etak_base_obl] | solve [etak_hint] | etak_base_obl ].
  Obligation Tactic := etak_obl.

  (* ===== Slice A helpers (EtaSliceA, K3). Every fact below is proved here from the bridge
     (PCUICSafeReduceEtaBridge), the η-stack lemmas of PCUICPositionEta(Typing), the facts file
     (PCUICSafeConversionEtaFacts) and the section's named classes; no new hypothesis. ===== *)
  Ltac A_wfΣ := try match goal with H : abstract_env_ext_rel X _ |- _ => rename H into wfΣ end.

  Lemma A_no_Eta_arg_drop_eta_run ρ : no_Eta_arg ρ -> no_Eta_arg (drop_eta_run ρ).
  Proof.
    induction ρ as [|se ρ IH]; [auto|].
    destruct se; cbn; intros h; try exact h.
    now apply IH.
  Qed.

  (* A real side reduces in its structural context. *)
  Lemma A_focus_context_real π : no_Eta_arg π -> focus_context π = stack_context π.
  Proof.
    intros h. unfold focus_context. cbv zeta.
    destruct (decompose_stack π) as [a r] eqn:E. cbn [snd].
    apply decompose_stack_eq in E. subst π. rewrite no_Eta_arg_appstack in h.
    pose proof (A_no_Eta_arg_drop_eta_run r h) as h'.
    destruct (drop_eta_run r) as [|se σ]; [reflexivity|].
    destruct se; try reflexivity.
    cbn in h'. congruence.
  Qed.

  Lemma A_zip_appstack_nil t args :
    PCUICPosition.zip (t, PCUICPosition.appstack args []) = mkApps t args.
  Proof.
    unfold PCUICPosition.zip. cbn [fst snd]. rewrite PCUICPosition.zipc_appstack. reflexivity.
  Qed.

  Lemma A_zipp_eta_appstack t l ρ : decompose_stack ρ = ([], ρ) ->
    zipp_eta t (appstack l ρ) = mkApps (eta_rename ρ 0 (mkApps t l)) (eta_virtuals (eta_run ρ)).
  Proof.
    intros hρ. unfold zipp_eta.
    have e : decompose_stack (appstack l ρ) = (l, ρ).
    { rewrite decompose_stack_appstack hρ. cbn [fst snd]. now rewrite app_nil_r. }
    rewrite (decompose_stack_eta_eq _ _ _ e). cbn [fst].
    rewrite eta_rename_appstack mkApps_app eta_rename_mkApps. reflexivity.
  Qed.

  Lemma A_sce_appstack π args ρ args' : (args, ρ) = decompose_stack π ->
    stack_context_eta (appstack args' ρ) = stack_context_eta π.
  Proof.
    intros e. rewrite (decompose_stack_eq _ _ _ (eq_sym e)) !stack_context_eta_appstack. reflexivity.
  Qed.

  (* One side of [_isconv_red]: either the side is real ([no_Eta_arg]), or it is a virtual
     focus, a variable without body of the focus context, which reduce_args_E returns as is. *)
  Lemma A_side_cases flags Γ t π args ρ t' args' hr :
    virt_ok t π = true -> (args, ρ) = decompose_stack π ->
    (t', args') = reduce_args_E flags X_type X (Γ ,,, focus_context π) t args hr ->
    no_Eta_arg π = true \/ (no_Eta_arg π = false /\ t' = t /\ args' = [] /\ args = [] /\ ρ = π).
  Proof.
    intros hv e eq.
    destruct (no_Eta_arg π) eqn:hna; [left; reflexivity|right].
    destruct (virt_ok_focus t π hv hna) as (k & decl & [-> hargs hnth hbody]).
    rewrite <- e in hargs. cbn in hargs. subst args.
    assert (hnth' : nth_error (Γ ,,, focus_context π) k = Some decl).
    { unfold app_context. rewrite (nth_error_app_lt _ _ _ (nth_error_Some_length hnth)). exact hnth. }
    rewrite (reduce_args_E_vass flags X_type X _ k decl hr hnth' hbody) in eq.
    injection eq as -> ->.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e)) as eπ.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite eπ. reflexivity.
  Qed.

  (* G1 (#1/#2): the reduction input is well typed in the focus context. *)
  Lemma A_focus_wt Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π args ρ :
    virt_ok t π = true -> (args, ρ) = decompose_stack π -> welltypedE Σ Γ (zipc t π) ->
    ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥ ->
    welltypedE Σ (Γ ,,, focus_context π) (PCUICPosition.zip (t, PCUICPosition.appstack args [])).
  Proof.
    intros hv e h [hwfl]. rewrite A_zip_appstack_nil.
    destruct (heΣ _ wfΣ) as [hwf].
    destruct (no_Eta_arg π) eqn:hna.
    - rewrite (A_focus_context_real π hna).
      exact (wt_zipc_stack_context (wt := welltypedE) (wfP := wf_extE) Σ Γ t π ρ args hwf hna (eq_sym e) h).
    - destruct (virt_ok_focus t π hv hna) as (k & decl & [-> hargs hnth _]).
      rewrite <- e in hargs. cbn in hargs. subst args. cbn [mkApps].
      pose proof (wf_localE_focus_context Σ Γ _ π hv hna hwfl) as hwf'.
      eapply welltypedE_tRel_vass; [exact hwf'|].
      unfold app_context. rewrite (nth_error_app_lt _ _ _ (nth_error_Some_length hnth)). exact hnth.
  Qed.

  (* The new state is well typed (T1 through [wt_red]). *)
  Lemma A_side_wt Σ (wfΣ : abstract_env_ext_rel X Σ) flags Γ t π args ρ t' args' hr :
    virt_ok t π = true -> (args, ρ) = decompose_stack π ->
    (t', args') = reduce_args_E flags X_type X (Γ ,,, focus_context π) t args hr ->
    welltypedE Σ Γ (zipc t π) -> welltypedE Σ Γ (zipc t' (appstack args' ρ)).
  Proof.
    intros hv e eq h.
    destruct (A_side_cases flags Γ t π args ρ t' args' hr hv e eq) as [hna | (_ & -> & -> & _ & ->)].
    2: exact h.
    pose proof (reduce_args_E_sound flags X_type X Σ wfΣ _ t args hr) as [r].
    rewrite <- eq in r. cbn [fst snd] in r.
    rewrite (A_focus_context_real π hna) in r.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e)) as eπ. subst π.
    rewrite stack_context_appstack in r.
    rewrite zipc_appstack in h. rewrite zipc_appstack.
    destruct (heΣ _ wfΣ) as [hwf].
    exact (wt_red _ _ _ _ hwf h (red_context_zip_eta Σ Γ _ _ ρ (clrel_rel r))).
  Qed.

  (* One side's contribution to the measure. *)
  Definition A_step Γ t π t' π' : Prop :=
    (π' = π /\ t' = t) \/
    (forall Σ, abstract_env_ext_rel X Σ -> cored Σ Γ (zipc t' π') (zipc t π)) \/
    (zipc t' π' = zipc t π /\ positionR (stack_position π') (stack_position π)).

  Lemma A_side_step flags Γ t π args ρ t' args' hr :
    virt_ok t π = true -> (args, ρ) = decompose_stack π ->
    (t', args') = reduce_args_E flags X_type X (Γ ,,, focus_context π) t args hr ->
    A_step Γ t π t' (appstack args' ρ).
  Proof.
    intros hv e eq.
    destruct (A_side_cases flags Γ t π args ρ t' args' hr hv e eq) as [hna | (_ & -> & -> & _ & ->)].
    2: { left. split; reflexivity. }
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (decompose_stack_eq _ _ _ (eq_sym e)) as eπ.
    destruct (reduce_args_E_Req flags X_type X Σ wfΣ _ t args hr) as [h | [h | [h1 h2]]].
    - rewrite <- eq in h. injection h as -> ->.
      left. split; [symmetry; exact eπ|reflexivity].
    - rewrite <- eq in h. cbn [fst snd] in h.
      rewrite (A_focus_context_real π hna) in h.
      right; left. intros Σ' wfΣ'.
      pose proof (abstract_env_ext_irr X wfΣ wfΣ') as eΣ. subst Σ'.
      subst π. rewrite stack_context_appstack in h. rewrite no_Eta_arg_appstack in hna.
      rewrite !zipc_appstack. exact (cored_context_eta Σ Γ _ _ ρ hna h).
    - rewrite <- eq in h1, h2. cbn [fst snd] in h1, h2.
      right; right. subst π. split.
      + rewrite !zipc_appstack. rewrite h1. reflexivity.
      + rewrite !stack_position_appstack. rewrite !stack_position_appstack in h2.
        cbn [stack_position app] in h2.
        apply positionR_poscat. exact h2.
  Qed.

  Lemma A_R_red Γ s' s t1 π1 t1' π1' t2 π2 t2' π2' f1 f2 h2 f1' f2' h2' :
    stateR s' s -> A_step Γ t1 π1 t1' π1' -> A_step Γ t2 π2 t2' π2' ->
    R Γ (mkpack Γ s' t1' π1' t2' π2' f1' f2' h2') (mkpack Γ s t1 π1 t2 π2 f1 f2 h2).
  Proof.
    intros hs s1 s2.
    destruct s1 as [[-> ->] | [hc | [hz hp]]].
    - destruct s2 as [[-> ->] | [hc | [hz hp]]].
      + apply R_stateR; [constructor; reflexivity | reflexivity | constructor; reflexivity
                        | reflexivity | exact hs].
      + apply R_cored2; [constructor; reflexivity | reflexivity | exact hc].
      + apply R_positionR2; [constructor; reflexivity | reflexivity | constructor; exact hz | exact hp].
    - apply R_cored. exact hc.
    - apply R_positionR; [constructor; exact hz | exact hp].
  Qed.

  Lemma A_side_virt_ok flags Γ t π args ρ t' args' hr :
    virt_ok t π = true -> (args, ρ) = decompose_stack π ->
    (t', args') = reduce_args_E flags X_type X (Γ ,,, focus_context π) t args hr ->
    virt_ok t' (appstack args' ρ) = true.
  Proof.
    intros hv e eq.
    have hρ : ρ = (decompose_stack π).2 by rewrite -e.
    rewrite hρ. apply (virt_ok_reduce t π); [exact hv|].
    destruct (A_side_cases flags Γ t π args ρ t' args' hr hv e eq) as [hna | (_ & -> & -> & _ & _)].
    - left. exact hna.
    - right. split; reflexivity.
  Qed.

  (* A virtual focus is a variable without body applied to the virtuals of its run: whnf. *)
  Lemma A_virtual_whnf (Σ : global_env_ext) Γ t π : virt_ok t π = true -> no_Eta_arg π = false ->
    whnf RedFlags.nodelta Σ (Γ ,,, stack_context_eta π) (zipp_eta t π).
  Proof.
    intros hv hna.
    destruct (virt_ok_virtual t π hv hna) as (k & u & a & σ & [-> hd hdr hk]).
    unfold zipp_eta. rewrite (decompose_stack_eta_eq π [] π hd). cbn [fst map app].
    rewrite eta_rename_rename. cbn [rename].
    rewrite (eta_ren_run π 0 k u a σ hdr (Nat.le_0_l k)).
    apply whnf_ne. apply whne_mkApps. apply whne_rel.
    destruct (stack_context_eta_drop_eta_run π) as (Δ & hl & hΔ).
    rewrite hΔ hdr.
    unfold app_context. rewrite -app_assoc.
    have hge : #|Δ| <= eta_run π + k by lia.
    rewrite (nth_error_app_ge _ _ _ hge) hl.
    replace (eta_run π + k - eta_run π) with k by lia.
    cbn [stack_context_eta stack_entry_context_eta app].
    destruct (decompose_stack σ) as [l θ] eqn:eσ. cbn [snd] in hk.
    rewrite (decompose_stack_eq _ _ _ eσ) stack_context_eta_appstack.
    destruct (stack_context_eta_run_vass θ k hk) as (decl & hn & hb).
    rewrite (nth_error_app_lt _ _ _ (nth_error_Some_length hn)) hn. cbn. rewrite hb. reflexivity.
  Qed.

  (* The Term state's [isred_full] (whnf of the η view) after reduction, under G2b. *)
  Lemma A_side_isred Γ t π args ρ t' args' hr :
    virt_ok t π = true -> (args, ρ) = decompose_stack π ->
    (t', args') = reduce_args_E RedFlags.nodelta X_type X (Γ ,,, focus_context π) t args hr ->
    eta_head_ok t' ρ = true ->
    isred_full Γ t' (appstack args' ρ).
  Proof.
    intros hv e eq hok. unfold isred_full.
    destruct (no_Eta_arg π) eqn:hna.
    - pose proof (reduce_args_E_isred RedFlags.nodelta X_type X _ t args hr eq_refl) as [hia _].
      rewrite <- eq in hia. cbn [fst] in hia.
      split; [exact hia|].
      intros Σ wfΣ.
      pose proof (reduce_args_E_whnf RedFlags.nodelta X_type X Σ wfΣ _ t args hr) as [w].
      rewrite <- eq in w. cbn [fst snd] in w.
      rewrite (A_focus_context_real π hna) in w.
      pose proof (decompose_stack_twice _ _ _ (eq_sym e)) as hρ.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e)) as eπ. subst π.
      rewrite no_Eta_arg_appstack in hna. rewrite stack_context_appstack in w.
      constructor.
      rewrite stack_context_eta_appstack (A_zipp_eta_appstack _ _ _ hρ).
      pose proof (eta_rename_whnf RedFlags.nodelta Σ Γ ρ _ hna w) as w'.
      rewrite eta_rename_mkApps in w'. rewrite eta_rename_mkApps.
      apply whnf_mkApps_eta_virtuals; [exact w' | rewrite eta_rename_isApp; exact hia | |].
      + intros k hk. destruct (stack_context_eta_run_vass ρ k hk) as (decl & hn & hb).
        unfold app_context. rewrite (nth_error_app_lt _ _ _ (nth_error_Some_length hn)) hn.
        cbn. rewrite hb. reflexivity.
      + revert hok. unfold eta_head_ok. rewrite eta_rename_rigid_head.
        destruct (eta_run ρ) as [|m]; [intros _; left; reflexivity|].
        cbn [Nat.eqb orb]. destruct (rigid_head t'); cbn; intros hok; [discriminate hok|right; reflexivity].
    - destruct (A_side_cases RedFlags.nodelta Γ t π args ρ t' args' hr hv e eq) as [hna' | (_ & -> & -> & _ & ->)].
      { rewrite hna in hna'. discriminate hna'. }
      destruct (virt_ok_virtual t π hv hna) as (k & u & a & σ & [-> _ _ _]).
      split; [reflexivity|].
      intros Σ wfΣ. constructor.
      change (appstack [] π) with π.
      exact (A_virtual_whnf Σ Γ (tRel k) π hv hna).
  Qed.

  (* A real side's reduction, read through the η view in the η context. [closed_red] is in
     Type, so the environment facts come as arguments, not through the squashes of heΣ/hΣ. *)
  Lemma A_red_eta_real Σ (hwf : wf_extE Σ) (cb : ClosedBodies Σ) Γ t π args ρ t' args' :
    no_Eta_arg π -> decompose_stack π = (args, ρ) ->
    welltypedE Σ Γ (zipc t π) -> is_closed_context (Γ ,,, stack_context_eta π) ->
    red Σ (Γ ,,, stack_context π) (mkApps t args) (mkApps t' args') ->
    Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta t π ⇝ zipp_eta t' (appstack args' ρ).
  Proof.
    intros hna e h hcl r.
    pose proof (wt_zipc_stack_context (wt := welltypedE) (wfP := wf_extE) Σ Γ t π ρ args hwf hna e h) as h'.
    pose proof (ref_closed_context (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf h') as hc.
    pose proof (ref_open_term (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf h') as ho.
    pose proof (ref_open_term (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf h) as hop.
    pose proof (decompose_stack_twice _ _ _ e) as hρ.
    apply into_closed_red; [|exact hcl|].
    - pose proof (decompose_stack_eq _ _ _ e) as eπ. subst π.
      rewrite no_Eta_arg_appstack in hna.
      rewrite stack_context_appstack in hc ho r.
      rewrite stack_context_eta_appstack (A_zipp_eta_appstack t args ρ hρ) (A_zipp_eta_appstack t' args' ρ hρ).
      apply red_mkApps_f.
      exact (eta_rename_red Σ Γ ρ _ _ cb hna hc ho r).
    - apply zipp_eta_open; [|exact hop|exact hcl].
      unfold virt_ok. rewrite hna. reflexivity.
  Qed.

  Lemma A_red_eta_head Σ (hwf : wf_extE Σ) (cb : ClosedBodies Σ) Γ t t' π :
    no_Eta_arg π -> welltypedE Σ Γ (zipc t π) -> is_closed_context (Γ ,,, stack_context_eta π) ->
    red Σ (Γ ,,, stack_context π) t t' ->
    Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta t π ⇝ zipp_eta t' π.
  Proof.
    intros hna h hcl r.
    destruct (decompose_stack π) as [args ρ] eqn:e.
    have r' : red Σ (Γ ,,, stack_context π) (mkApps t args) (mkApps t' args)
      by apply red_mkApps_f; exact r.
    pose proof (A_red_eta_real Σ hwf cb Γ t π args ρ t' args hna e h hcl r') as rr.
    rewrite -(decompose_stack_eq _ _ _ e) in rr. exact rr.
  Qed.

  Lemma A_side_red Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π args ρ t' args' hr :
    virt_ok t π = true -> (args, ρ) = decompose_stack π ->
    (t', args') = reduce_args_E RedFlags.nodelta X_type X (Γ ,,, focus_context π) t args hr ->
    welltypedE Σ Γ (zipc t π) -> is_closed_context (Γ ,,, stack_context_eta π) ->
    ∥ Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta t π ⇝ zipp_eta t' (appstack args' ρ) ∥.
  Proof.
    intros hv e eq h hcl.
    destruct (heΣ _ wfΣ) as [hwf]. destruct (hΣ _ wfΣ) as [cb].
    destruct (A_side_cases RedFlags.nodelta Γ t π args ρ t' args' hr hv e eq) as [hna | (_ & -> & -> & _ & ->)].
    - pose proof (reduce_args_E_sound RedFlags.nodelta X_type X Σ wfΣ _ t args hr) as [r].
      rewrite <- eq in r. cbn [fst snd] in r.
      rewrite (A_focus_context_real π hna) in r.
      constructor.
      exact (A_red_eta_real Σ hwf cb Γ t π args ρ t' args' hna (eq_sym e) h hcl (clrel_rel r)).
    - constructor.
      change (appstack [] π) with π.
      apply into_closed_red; [reflexivity|exact hcl|].
      apply zipp_eta_open; [exact hv| |exact hcl].
      exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf h).
  Qed.

  Lemma A_ws_red_l Σ (cb : ClosedBodies Σ) leq Δ z1 z1' z2 :
    Σ ;;; Δ ⊢ z1 ⇝ z1' -> ws_cumul_pbE leq Σ Δ z1' z2 -> ws_cumul_pbE leq Σ Δ z1 z2.
  Proof. intros r h. exact (red_ws_cumul_pbE_left (wfΣ := cb) r h). Qed.

  (* Side 2's reduction lives in side 2's η context; the state relates the two η contexts. *)
  Lemma A_ws_red_r Σ (cb : ClosedBodies Σ) leq Δ1 Δ2 z1 z2 z2' :
    ws_cumul_ctx_pbE Conv Σ Δ1 Δ2 -> Σ ;;; Δ2 ⊢ z2 ⇝ z2' ->
    ws_cumul_pbE leq Σ Δ1 z1 z2' -> ws_cumul_pbE leq Σ Δ1 z1 z2.
  Proof.
    intros hc r2 h.
    have h2 : ws_cumul_pbE Conv Σ Δ1 z2 z2' :=
      ws_cumul_pbE_ws_cumul_ctx (wfΣ := cb) (ws_cumul_ctx_pbE_sym (wfΣ := cb) hc)
        (red_ws_cumul_pbE (wfΣ := cb) r2).
    etransitivity; [exact h|].
    apply ws_cumul_eq_pbE. symmetry. exact h2.
  Qed.

  Lemma A_g2 t1' a1 r1 t2' a2 r2 :
    true = rebuilt_ok t1' a1 r1 && rebuilt_ok t2' a2 r2 ->
    eta_head_ok t1' r1 = true /\ eta_head_ok t2' r2 = true.
  Proof.
    intros g. symmetry in g. apply andb_prop in g as [g1 g2].
    unfold rebuilt_ok in g1, g2. apply andb_prop in g1 as [_ g1]. apply andb_prop in g2 as [_ g2].
    split; assumption.
  Qed.

  (* The fixpoint step of [unfold_one_fix] on a constructor argument. *)
  Lemma A_fix_red1 (Σ : global_env) Γ' mfix idx l fn ind n ui args' :
    Some (#|l|, fn) = unfold_fix mfix idx ->
    red1 Σ Γ' (tApp (mkApps (tFix mfix idx) l) (mkApps (tConstruct ind n ui) args'))
              (tApp (mkApps fn l) (mkApps (tConstruct ind n ui) args')).
  Proof.
    intros e.
    replace (tApp (mkApps (tFix mfix idx) l) (mkApps (tConstruct ind n ui) args'))
      with (mkApps (tFix mfix idx) (l ++ [mkApps (tConstruct ind n ui) args'])) by (rewrite mkApps_app; reflexivity).
    replace (tApp (mkApps fn l) (mkApps (tConstruct ind n ui) args'))
      with (mkApps fn (l ++ [mkApps (tConstruct ind n ui) args'])) by (rewrite mkApps_app; reflexivity).
    eapply red_fix; [symmetry; exact e|].
    unfold is_constructor. rewrite (nth_error_app_ge _ _ _ (le_n #|l|)) Nat.sub_diag. cbn [nth_error].
    unfold isConstruct_app. rewrite decompose_app_mkApps; reflexivity.
  Qed.

  (* The obligations of [_isconv_red], dispatched on the goal's shape. The arguments are the
     definition's own parameters; the hypotheses the [with] clauses add are found by type. *)
  Ltac A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx :=
    lazymatch goal with
    | |- welltypedE _ (_ ,,, focus_context _) _ =>
        match goal with w : abstract_env_ext_rel X _ |- _ =>
          first [ exact (A_focus_wt _ w _ _ _ _ _ hv1 e1 (h1 _ w) (hwf1 _ w))
                | exact (A_focus_wt _ w _ _ _ _ _ hv2 e2 (h2 _ w) (hwf2 _ w)) ] end
    | |- welltypedE _ _ _ =>
        match goal with w : abstract_env_ext_rel X _, q : (_, _) = reduce_args_E _ _ _ _ _ _ _ |- _ =>
          first [ exact (A_side_wt _ w _ _ _ _ _ _ _ _ _ hv1 e1 q (h1 _ w))
                | exact (A_side_wt _ w _ _ _ _ _ _ _ _ _ hv2 e2 q (h2 _ w)) ] end
    | |- R _ _ _ =>
        match goal with q1 : (_, _) = reduce_args_E _ _ _ _ _ _ _,
                        q2 : (_, _) = reduce_args_E _ _ _ _ _ _ _ |- _ =>
          apply A_R_red; [constructor | exact (A_side_step _ _ _ _ _ _ _ _ _ hv1 e1 q1)
                         | exact (A_side_step _ _ _ _ _ _ _ _ _ hv2 e2 q2)] end
    | |- squash (ws_cumul_ctx_pbE _ _ _ _) =>
        match goal with w : abstract_env_ext_rel X _ |- _ =>
          rewrite (A_sce_appstack _ _ _ _ e1) (A_sce_appstack _ _ _ _ e2); exact (hx _ w) end
    | |- virt_ok _ _ = true =>
        match goal with q : (_, _) = reduce_args_E _ _ _ _ _ _ _ |- _ =>
          first [ exact (A_side_virt_ok _ _ _ _ _ _ _ _ _ hv1 e1 q)
                | exact (A_side_virt_ok _ _ _ _ _ _ _ _ _ hv2 e2 q) ] end
    | |- squash (wf_localE _ _) =>
        match goal with w : abstract_env_ext_rel X _ |- _ =>
          first [ rewrite (A_sce_appstack _ _ _ _ e1); exact (hwf1 _ w)
                | rewrite (A_sce_appstack _ _ _ _ e2); exact (hwf2 _ w) ] end
    | |- isred_full _ _ _ =>
        match goal with q : (_, _) = reduce_args_E _ _ _ _ _ _ _,
                        g : true = rebuilt_ok _ _ _ && rebuilt_ok _ _ _ |- _ =>
          first [ exact (A_side_isred _ _ _ _ _ _ _ _ hv1 e1 q (proj1 (A_g2 _ _ _ _ _ _ g)))
                | exact (A_side_isred _ _ _ _ _ _ _ _ hv2 e2 q (proj2 (A_g2 _ _ _ _ _ _ g))) ] end
    | |- conv_cumE _ _ _ _ _ =>
        match goal with
        | w : abstract_env_ext_rel X _, q1 : (_, _) = reduce_args_E _ _ _ _ _ _ _,
          q2 : (_, _) = reduce_args_E _ _ _ _ _ _ _,
          hc : forall S, abstract_env_ext_rel X S -> conv_cumE _ S _ _ _ |- _ =>
          let cb := fresh "cb" in let hx' := fresh "hx'" in let hh := fresh "hh" in
          let hcl1 := fresh "hcl1" in let hcl2 := fresh "hcl2" in
          let r1 := fresh "r1" in let r2 := fresh "r2" in
          destruct (hΣ _ w) as [cb]; destruct (hx _ w) as [hx'];
          pose proof (ws_cumul_ctx_pbE_closed_left _ _ _ _ hx') as hcl1;
          pose proof (ws_cumul_ctx_pbE_closed_left _ _ _ _ (ws_cumul_ctx_pbE_sym (wfΣ := cb) hx')) as hcl2;
          destruct (hc _ w) as [hh];
          rewrite (A_sce_appstack _ _ _ _ e1) in hh;
          destruct (A_side_red _ w _ _ _ _ _ _ _ _ hv1 e1 q1 (h1 _ w) hcl1) as [r1];
          destruct (A_side_red _ w _ _ _ _ _ _ _ _ hv2 e2 q2 (h2 _ w) hcl2) as [r2];
          constructor;
          exact (A_ws_red_l _ cb _ _ _ _ _ r1 (A_ws_red_r _ cb _ _ _ _ _ _ hx' r2 hh))
        end
    end.

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
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.
  Next Obligation. A_red_solve hv1 hv2 e1 e2 h1 h2 hwf1 hwf2 hx. Qed.

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
    A_wfΣ. rewrite A_zip_appstack_nil. cbn [mkApps].
    pose proof (decompose_stack_at_eq _ _ _ _ _ (eq_sym eq2)) as eπ.
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (h _ wfΣ) as hh. rewrite eπ zipc_appstack in hh.
    pose proof hna as hna'. rewrite eπ no_Eta_arg_appstack in hna'.
    change (welltypedE Σ Γ (zipc c (App_r (mkApps (tFix mfix idx) l) :: θ))) in hh.
    exact (ctf_context Σ Γ c (App_r (mkApps (tFix mfix idx) l) :: θ) hwf (eq_sym hna') hh).
  Qed.
  Transparent reduce_args_E.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zipp :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; try discriminate.
    all: noconf eq.
    pose proof (decompose_stack_at_length _ _ _ _ _ (eq_sym eq2)) as hl.
    pose proof (decompose_stack_at_eq _ _ _ _ _ (eq_sym eq2)) as eπ. subst.
    match type of eq3 with
    | _ = reduce_args_E ?flags ?XT ?X ?Γ ?t ?args ?hh =>
      pose proof (reduce_args_E_sound flags XT X Σ wfΣ Γ t args hh) as [r1]
    end.
    rewrite <- eq3 in r1. cbn [fst snd mkApps] in r1.
    unfold zipp. rewrite !decompose_stack_appstack.
    cbn [decompose_stack fst snd].
    destruct (decompose_stack θ) as [l' s'] eqn:e'. cbn [fst snd].
    constructor.
    rewrite stack_context_appstack.
    rewrite 2!mkApps_app. cbn [mkApps]. eapply red_mkApps_f.
    eapply trans_red.
    - eapply red_app_r. exact (clrel_rel r1).
    - eapply A_fix_red1. eassumption.
  Qed.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; try discriminate.
    all: noconf eq.
    pose proof (decompose_stack_at_length _ _ _ _ _ (eq_sym eq2)) as hl.
    pose proof (decompose_stack_at_eq _ _ _ _ _ (eq_sym eq2)) as eπ. subst.
    match type of eq3 with
    | _ = reduce_args_E ?flags ?XT ?X ?Γ ?t ?args ?hh =>
      pose proof (reduce_args_E_sound flags XT X Σ wfΣ Γ t args hh) as [r1]
    end.
    rewrite <- eq3 in r1. cbn [fst snd mkApps] in r1.
    rewrite !zipc_appstack. cbn [zipc fill_hole].
    constructor. apply red_context_zip_eta.
    eapply trans_red.
    - eapply red_app_r. exact (clrel_rel r1).
    - eapply A_fix_red1. eassumption.
  Qed.

  Lemma unfold_one_fix_cored :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored (fst Σ) Γ (zipc fn ξ) (zipc (tFix mfix idx) π).
  Proof.
    intros Γ mfix idx π h fn ξ eq Σ wfΣ.
    revert eq.
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; try discriminate.
    all: noconf eq.
    pose proof (decompose_stack_at_length _ _ _ _ _ (eq_sym eq2)) as hl.
    pose proof (decompose_stack_at_eq _ _ _ _ _ (eq_sym eq2)) as eπ. subst.
    match type of eq3 with
    | _ = reduce_args_E ?flags ?XT ?X ?Γ ?t ?args ?hh =>
      pose proof (reduce_args_E_sound flags XT X Σ wfΣ Γ t args hh) as [r1]
    end.
    rewrite <- eq3 in r1. cbn [fst snd mkApps] in r1.
    rewrite !zipc_appstack. cbn [zipc fill_hole].
    pose proof hna as hna'. rewrite no_Eta_arg_appstack in hna'.
    apply cored_context_eta; [exact (eq_sym hna')|].
    eapply cored_red_trans.
    - eapply red_app_r. exact (clrel_rel r1).
    - eapply A_fix_red1. eassumption.
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
    A_wfΣ. rewrite A_zip_appstack_nil. destruct (heΣ _ wfΣ) as [hwf].
    exact (wt_zipc_stack_context (wt := welltypedE) (wfP := wf_extE) Σ Γ _ π ρ args hwf hna (eq_sym eqd) (h _ wfΣ)).
  Qed.
  Transparent reduce_args_E.

  (** The machine's facts on the [zipp]-form run: its result reduces from the
      application and is a weak-head normal form (reduce_args_E's facts). *)
  Ltac prim_step_facts Σ wfΣ eqr :=
    match type of eqr with
    | _ = reduce_args_E ?f ?XT ?X ?Γ ?t ?args ?hh =>
      let r := fresh "r" in let wh := fresh "wh" in
      pose proof (reduce_args_E_sound f XT X Σ wfΣ Γ t args hh) as [r];
      pose proof (reduce_args_E_whnf f XT X Σ wfΣ Γ t args hh) as [wh];
      rewrite <- eqr in r, wh; cbn in r, wh
    end.

  Lemma unfold_one_prim_shape Γ c u π hna h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π hna h ->
    ∑ args ρ l,
      [× decompose_stack π = (args, ρ), ξ = appstack l ρ,
         (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
            ∥ red Σ (Γ ,,, stack_context π) (mkApps (tConst c u) args) (mkApps t' l) ∥) &
         mkApps t' l <> mkApps (tConst c u) args].
  Proof.
    funelim (unfold_one_prim Γ c u π hna h); intros [=]; subst.
    exists args, ρ, args'. split.
    - now symmetry.
    - reflexivity.
    - intros Σ wfΣ. prim_step_facts Σ wfΣ eqr. constructor. exact (clrel_rel r).
    - intros heq.
      match goal with H : false = eqb _ _ |- _ => pose proof H as hne end.
      rewrite heq eqb_refl in hne. discriminate hne.
  Qed.

  (** What a successful step gives a re-entry: the stack keeps its context, the
      application reduces in [zipp] and in [zipc] form, and the step is strict. *)
  Lemma unfold_one_prim_facts Γ c u π hna h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π hna h ->
    (stack_context ξ = stack_context π) ×
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
       ∥ red Σ (Γ ,,, stack_context π) (zipp (tConst c u) π) (zipp t' ξ) ∥) ×
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
       ∥ red Σ Γ (zipc (tConst c u) π) (zipc t' ξ) ∥) ×
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
       cored Σ Γ (zipc t' ξ) (zipc (tConst c u) π)).
  Proof.
    intros e. pose proof hna as hna'.
    destruct (unfold_one_prim_shape _ _ _ _ _ _ _ _ e) as (args & ρ & l & [ed -> hr hne]).
    pose proof (decompose_stack_twice _ _ _ ed) as hρ.
    apply decompose_stack_eq in ed. rewrite ed no_Eta_arg_appstack in hna'.
    rewrite ed. rewrite ed in hr.
    assert (ezp : forall t L, zipp t (appstack L ρ) = mkApps t L).
    { intros t L. unfold zipp. rewrite decompose_stack_appstack. rewrite hρ. cbn. now rewrite app_nil_r. }
    rewrite !ezp. rewrite !stack_context_appstack. rewrite !stack_context_appstack in hr.
    split; [reflexivity|]. split; [exact hr|].
    assert (hrc : forall Σ (wfΣ : abstract_env_ext_rel X Σ),
               ∥ red Σ Γ (zipc (tConst c u) (appstack args ρ)) (zipc t' (appstack l ρ)) ∥).
    { intros Σ wfΣ. destruct (hr _ wfΣ) as [r]. constructor.
      rewrite !zipc_appstack. eapply red_context_zip_eta. exact r. }
    split; [exact hrc|].
    intros Σ wfΣ. destruct (hrc _ wfΣ) as [r].
    eapply red_neq_cored; [exact r|].
    rewrite !zipc_appstack. intros ez. apply hne. exact (eq_sym (zipc_inj _ _ ρ hna' ez)).
  Qed.

  (* Slice A helpers on a step of [unfold_one_prim] (EtaSliceA). *)
  Lemma A_prim_noeta Γ c u π hna h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π hna h -> no_Eta_arg ξ = true.
  Proof.
    intros e. pose proof hna as hna'.
    destruct (unfold_one_prim_shape _ _ _ _ _ _ _ _ e) as (args & ρ & l & [ed -> _ _]).
    apply decompose_stack_eq in ed. rewrite ed no_Eta_arg_appstack in hna'.
    rewrite no_Eta_arg_appstack. exact hna'.
  Qed.

  Lemma A_prim_sce Γ c u π hna h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π hna h -> stack_context_eta ξ = stack_context_eta π.
  Proof.
    intros e. destruct (unfold_one_prim_shape _ _ _ _ _ _ _ _ e) as (args & ρ & l & [ed -> _ _]).
    apply decompose_stack_eq in ed. rewrite ed !stack_context_eta_appstack. reflexivity.
  Qed.

  Lemma A_prim_red Σ (wfΣ : abstract_env_ext_rel X Σ) Γ c u π hna h t' ξ :
    Some (t', ξ) = unfold_one_prim Γ c u π hna h -> is_closed_context (Γ ,,, stack_context_eta π) ->
    ∥ Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta (tConst c u) π ⇝ zipp_eta t' ξ ∥.
  Proof.
    intros e hcl. destruct (unfold_one_prim_shape _ _ _ _ _ _ _ _ e) as (args & ρ & l & [ed -> hr _]).
    destruct (hr _ wfΣ) as [r]. destruct (heΣ _ wfΣ) as [hwf]. destruct (hΣ _ wfΣ) as [cb].
    constructor. exact (A_red_eta_real Σ hwf cb Γ (tConst c u) π args ρ t' l hna ed (h _ wfΣ) hcl r).
  Qed.

  (* The obligations of [unfold_prims] and [unfold_prims_args], dispatched on the goal's shape;
     the arguments are the definition's own parameters ([hg] is the T1 equation of both
     stacks); the step equation and the recursive result are found by type. *)
  Ltac A_prims_solve hx hg hwf1 hwf2 :=
    lazymatch goal with
    | |- is_true (wf_stack _) =>
        match goal with e : Some _ = unfold_one_prim _ _ _ _ _ _ |- _ =>
          apply wf_stack_no_Eta_arg; exact (A_prim_noeta _ _ _ _ _ _ _ _ e) end
    | |- no_Eta_arg _ = true => first [ exact (proj2 (andb_prop _ _ hg)) | exact (proj1 (andb_prop _ _ hg)) ]
    | |- virt_ok _ _ = true =>
        unfold virt_ok;
        first [ rewrite (proj1 (andb_prop _ _ hg)); reflexivity
              | rewrite (proj2 (andb_prop _ _ hg)); reflexivity
              | match goal with e : Some _ = unfold_one_prim _ _ _ _ _ _ |- _ =>
                  rewrite (A_prim_noeta _ _ _ _ _ _ _ _ e); reflexivity end ]
    | |- welltypedE _ _ _ =>
        match goal with w : abstract_env_ext_rel X _, e : Some _ = unfold_one_prim _ _ _ _ _ ?hh |- _ =>
          let hrc := fresh "hrc" in let r := fresh "r" in let hwf := fresh "hwf" in
          destruct (unfold_one_prim_facts _ _ _ _ _ _ _ _ e) as (_ & _ & hrc & _);
          destruct (hrc _ w) as [r]; destruct (heΣ _ w) as [hwf];
          exact (wt_red _ _ _ _ hwf (hh _ w) r) end
    | |- R _ _ _ =>
        match goal with e : Some _ = unfold_one_prim _ _ _ _ _ _ |- _ =>
          let ΣA := fresh "ΣA" in let wA := fresh "wfΣA" in
          first [ apply R_cored; intros ΣA wA;
                  exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ _ e))) ΣA wA)
                | apply R_cored2; [constructor; reflexivity | reflexivity |
                    intros ΣA wA; exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ _ e))) ΣA wA)] ] end
    | |- squash (ws_cumul_ctx_pbE _ _ _ _) =>
        match goal with w : abstract_env_ext_rel X _, e : Some _ = unfold_one_prim _ _ _ _ _ _ |- _ =>
          rewrite (A_prim_sce _ _ _ _ _ _ _ _ e); exact (hx _ w) end
    | |- squash (wf_localE _ _) =>
        match goal with w : abstract_env_ext_rel X _, e : Some _ = unfold_one_prim _ _ _ _ _ _ |- _ =>
          rewrite (A_prim_sce _ _ _ _ _ _ _ _ e); first [exact (hwf1 _ w) | exact (hwf2 _ w)] end
    | |- conv_cumE _ _ _ _ _ =>
        match goal with
        | w : abstract_env_ext_rel X _, e : Some _ = unfold_one_prim _ _ _ _ _ _,
          hc : forall S, abstract_env_ext_rel X S -> conv_cumE _ S _ _ _ |- _ =>
          let cb := fresh "cb" in let hx' := fresh "hx'" in let hh := fresh "hh" in
          let r := fresh "r" in
          destruct (hΣ _ w) as [cb]; destruct (hx _ w) as [hx']; destruct (hc _ w) as [hh];
          first [ rewrite (A_prim_sce _ _ _ _ _ _ _ _ e) in hh;
                  destruct (A_prim_red _ w _ _ _ _ _ _ _ _ e (ws_cumul_ctx_pbE_closed_left _ _ _ _ hx')) as [r];
                  constructor; exact (A_ws_red_l _ cb _ _ _ _ _ r hh)
                | destruct (A_prim_red _ w _ _ _ _ _ _ _ _ e
                              (ws_cumul_ctx_pbE_closed_left _ _ _ _ (ws_cumul_ctx_pbE_sym (wfΣ := cb) hx'))) as [r];
                  constructor; exact (A_ws_red_r _ cb _ _ _ _ _ _ hx' r hh) ]
        end
    end.

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

  (* E forms (base: [conv_cum] through [red_ws_cumul_pb], which needs base [wf Σ]; the E
     environment gives [ClosedBodies Σ], all that [red_ws_cumul_pbE] needs). *)
  Lemma red_conv_cum_l {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cumE leq Σ Γ u v.
  Proof.
    intros r. destruct (hΣ _ wfΣ) as [cb]. constructor. exact (red_ws_cumul_pbE (wfΣ := cb) r).
  Qed.

  Lemma red_conv_cum_r {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cumE leq Σ Γ v u.
  Proof.
    intros r. destruct (hΣ _ wfΣ) as [cb]. constructor. exact (red_ws_cumul_pbE_inv (wfΣ := cb) r).
  Qed.

  Lemma closed_red_zipp {Σ Γ t u π} :
    is_open_term Γ (zipp t π) ->
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ zipp t π ⇝ zipp u π.
  Proof using Type.
    intros cltπ [clΓ clt r].
    eapply into_closed_red; tea.
    unfold zipp. destruct (decompose_stack π). now apply red_mkApps_f.
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
  (* the left side took a step (wf_stack, typed, smaller, same η context, virt_ok, hwf, spec),
     then the right side's T1 premise and step: all through [A_prims_solve] *)
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.

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
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.
  Next Obligation. A_prims_solve hx hg hwf1 hwf2. Qed.

  (* Slice A helpers on a δ step (EtaSliceA). *)
  Lemma A_const_red Σ (wfΣ : abstract_env_ext_rel X Σ) Γ' k u d b :
    Some (ConstantDecl d) = abstract_env_lookup X k -> cst_body d = Some b ->
    red Σ Γ' (tConst k u) b@[u].
  Proof.
    intros e hb. destruct d as [ty bo univs rel]. cbn in hb. subst bo.
    eapply red_const. rewrite (abstract_env_lookup_correct' X k wfΣ). exact e.
  Qed.

  Lemma A_const_cored Σ (wfΣ : abstract_env_ext_rel X Σ) Γ' k u d b :
    Some (ConstantDecl d) = abstract_env_lookup X k -> cst_body d = Some b ->
    cored Σ Γ' b@[u] (tConst k u).
  Proof.
    intros e hb. destruct d as [ty bo univs rel]. cbn in hb. subst bo.
    eapply cored_const. rewrite (abstract_env_lookup_correct' X k wfΣ). exact e.
  Qed.

  (* The obligations of [unfold_constants]: one side takes a δ step, the other is unchanged;
     the arguments are the definition's own parameters ([hg] is the T1 equation of both
     stacks); the lookup equations and the recursive result are found by type. *)
  Ltac A_const_solve h1 h2 hx hg :=
    let hg1 := fresh "hg1" in let hg2 := fresh "hg2" in
    pose proof (andb_prop _ _ hg) as [hg1 hg2];
    lazymatch goal with
    | |- welltypedE _ _ _ =>
        match goal with w : abstract_env_ext_rel X _ |- _ =>
          let hwf := fresh "hwf" in destruct (heΣ _ w) as [hwf];
          first [ eapply (wt_red _ _ _ _ hwf (h2 _ w)); apply red_context_zip_eta;
                  eapply (A_const_red _ w); [eassumption | reflexivity]
                | eapply (wt_red _ _ _ _ hwf (h1 _ w)); apply red_context_zip_eta;
                  eapply (A_const_red _ w); [eassumption | reflexivity] ] end
    | |- R _ _ _ =>
        let ΣA := fresh "ΣA" in let wA := fresh "wfΣA" in
        first [ apply R_cored; intros ΣA wA; apply cored_context_eta;
                [exact hg1 | eapply (A_const_cored _ wA); [eassumption | reflexivity]]
              | apply R_cored2; [constructor; reflexivity | reflexivity |
                  intros ΣA wA; apply cored_context_eta;
                  [exact hg2 | eapply (A_const_cored _ wA); [eassumption | reflexivity]]] ]
    | |- conv_cumE _ _ _ _ _ =>
        match goal with
        | w : abstract_env_ext_rel X _, hc : forall S, abstract_env_ext_rel X S -> conv_cumE _ S _ _ _ |- _ =>
          let cb := fresh "cb" in let hwf := fresh "hwf" in let hx' := fresh "hx'" in
          let hh := fresh "hh" in
          destruct (hΣ _ w) as [cb]; destruct (heΣ _ w) as [hwf];
          destruct (hx _ w) as [hx']; destruct (hc _ w) as [hh];
          constructor;
          first [ refine (A_ws_red_l _ cb _ _ _ _ _ _ hh);
                  eapply (A_red_eta_head _ hwf cb);
                  [ exact hg1 | exact (h1 _ w) | exact (ws_cumul_ctx_pbE_closed_left _ _ _ _ hx')
                  | eapply (A_const_red _ w); [eassumption | reflexivity] ]
                | refine (A_ws_red_r _ cb _ _ _ _ _ _ hx' _ hh);
                  eapply (A_red_eta_head _ hwf cb);
                  [ exact hg2 | exact (h2 _ w)
                  | exact (ws_cumul_ctx_pbE_closed_left _ _ _ _ (ws_cumul_ctx_pbE_sym (wfΣ := cb) hx'))
                  | eapply (A_const_red _ w); [eassumption | reflexivity] ] ]
        end
    end.

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
  (* The right side's δ step, then the left side's (one copy per non-body case of the right
     side's lookup): typed, smaller, spec. *)
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.
  Next Obligation. A_const_solve h1 h2 hx hg. Qed.

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

  (* The E specifications of the helper families: E relations between side 1's components
     renamed by its stack ([eta_rename π 0], as [eta_rename_tCase]/[eta_rename_tFix] give the
     η view of the whole term) and side 2's renamed by its own stack, in side 1's η context.
     They are exactly the premises of [ws_cumul_pbE_Case]/[_Fix]/[_Prim]
     (PCUICConversionEtaCongr) for the renamed terms. *)

  (* ---- Slice B helpers (EtaSliceB). ---- *)

  (* An assumption context of closed sorts, of any length: the substitution target of the
     parameters in [inst_case_ws_cumul_ctx_pbE] (base uses the smashed parameters of a declared
     inductive; any assumption context of the right length does, and needs no typing). *)
  Lemma B_sort_ctx (Γ : context) n :
    let Δ := repeat (vass (mkBindAnn nAnon Relevant) (tSort sProp)) n in
    [× assumption_context Δ, context_assumptions Δ = n, #|Δ| = n &
       is_closed_context Γ -> is_closed_context (Γ ,,, Δ)].
  Proof using Type.
    cbn zeta. induction n as [|n [ha hc hl hcl]]; cbn [repeat context_assumptions List.length].
    - split; [constructor|reflexivity|reflexivity|now intros].
    - split.
      + constructor. exact ha.
      + now rewrite hc.
      + now rewrite hl.
      + intros h. specialize (hcl h).
        change (is_closed_context ((Γ ,,, repeat (vass (mkBindAnn nAnon Relevant) (tSort sProp)) n) ,,
                  vass (mkBindAnn nAnon Relevant) (tSort sProp))).
        now rewrite on_free_vars_ctx_snoc hcl.
  Qed.

  (* The E copy of base [PCUICConvCumInversion.inst_case_ws_cumul_ctx_pb], untyped and under
     [ClosedBodies Σ] (base: [wf Σ]); the two prefixes may differ ([Γ] vs [Γ'], related by
     [ws_cumul_ctx_pbE]), and no declared inductive is needed. The proof follows base
     (PCUICConvCumInversion.v:93-149) with the E twins of [PCUICWsCumulEtaCtx]. The obligations
     [conv_stack_ctx] of the Case_branch and the Case_pred (return) frames use it. *)
  Lemma inst_case_ws_cumul_ctx_pbE (Σ : global_env_ext) (cb : ClosedBodies Σ)
    (Γ Γ' : context) (pars pars' : list term) (puinst puinst' : Instance.t) (ctx ctx' : context) :
    on_free_vars_ctx (closedP #|pars| xpredT) ctx ->
    on_free_vars_ctx (closedP #|pars'| xpredT) ctx' ->
    ws_cumul_ctx_pbE Conv Σ Γ Γ' ->
    ws_cumul_pbE_terms Σ Γ pars pars' ->
    cmp_universe_instance (compare_universe Σ Conv) puinst puinst' ->
    eq_context_upto_names ctx ctx' ->
    ws_cumul_ctx_pbE Conv Σ (Γ ,,, inst_case_context pars puinst ctx)
      (Γ' ,,, inst_case_context pars' puinst' ctx').
  Proof using Type.
    intros onp onp' hc eqpars equ eqctx.
    have hl : #|pars| = #|pars'| := All2_length eqpars.
    rewrite -hl in onp'.
    have clΓ : is_closed_context Γ := ws_cumul_ctx_pbE_closed_left _ _ _ _ hc.
    destruct (B_sort_ctx Γ #|pars|) as [ass lenass lenΔ clΔ].
    set (Δp := repeat (vass (mkBindAnn nAnon Relevant) (tSort sProp)) #|pars|) in *.
    have clΓΔ := clΔ clΓ.
    (* the instantiated contexts are closed over [Γ ,,, Δp] *)
    have clctx : forall c, on_free_vars_ctx (closedP #|pars| xpredT) c -> is_closed_context (Γ ,,, Δp ,,, c).
    { intros c hcl. rewrite on_free_vars_ctx_app clΓΔ andb_true_l.
      eapply on_free_vars_ctx_impl; [|exact hcl]. intros i.
      rewrite /closedP /shiftnP. case: (Nat.ltb_spec i #|pars|) => // hlt _.
      apply/orP; left. apply/Nat.ltb_lt. rewrite app_context_length lenΔ. lia. }
    have clctxu : forall u c, on_free_vars_ctx (closedP #|pars| xpredT) c ->
        is_closed_context (Γ ,,, Δp ,,, subst_instance u c).
    { intros u c hcl. rewrite on_free_vars_ctx_app on_free_vars_ctx_subst_instance -on_free_vars_ctx_app.
      exact (clctx c hcl). }
    (* move the right instance from [Γ] to [Γ'] *)
    have clR : is_closed_context (Γ ,,, inst_case_context pars' puinst' ctx').
    { apply PCUICConversion.on_free_vars_ctx_inst_case_context_xpred0;
        [exact (WT_open_right eqpars)|rewrite -hl; exact onp'|exact clΓ]. }
    eapply (@CRelationClasses.transitivity _ (ws_cumul_ctx_pbE Conv Σ)
              (PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_trans (Σ := Σ) (wfΣ := cb) Conv) _
              (Γ ,,, inst_case_context pars' puinst' ctx')).
    2:{ exact (PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_app_same clR hc). }
    apply (fst PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_rel_app).
    rewrite /inst_case_context.
    eapply (PCUICWsCumulEtaCtx.substitution_ws_cumul_ctx_pbE_subst_conv (Σ := Σ) (wfΣ := cb)
              (Γ := Γ) (Γ'' := []) (Γ' := Δp) (Γ'0 := Δp) (pb := Conv)
              (s := List.rev pars) (s' := List.rev pars')
              (Δ := subst_instance puinst ctx) (Δ' := subst_instance puinst' ctx')).
    - apply (snd PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_rel_app).
      eapply (@CRelationClasses.transitivity _ (ws_cumul_ctx_pbE Conv Σ)
                (PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_trans (Σ := Σ) (wfΣ := cb) Conv) _
                ((Γ ,,, Δp) ,,, subst_instance puinst ctx')).
      + apply (PCUICWsCumulEtaCtx.into_ws_cumul_ctx_pbE (Σ := Σ)).
        * exact (clctxu puinst ctx onp).
        * exact (clctxu puinst ctx' onp').
        * apply (PCUICWsCumulEtaCtx.eq_context_upto_names_conv_contextE Σ).
          rewrite /app_context. apply All2_app; [|reflexivity].
          apply PCUICConfluence.eq_context_upto_names_univ_subst_preserved. exact eqctx.
      + apply (fst PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_rel_app).
        exact (PCUICWsCumulEtaCtx.subst_instance_ws_cumul_ctx_pbE_rel (Σ := Σ) (wfΣ := cb)
                 (clctx ctx' onp') equ).
    - now apply All2_rev.
    - apply (untyped_subslet_ass ass). now rewrite List.length_rev lenass.
    - apply (untyped_subslet_ass ass). now rewrite List.length_rev lenass hl.
    - exact clΓΔ.
  Qed.

  Ltac B_rel wfR := match goal with H : abstract_env_ext_rel X _ |- _ => pose proof H as wfR end.

  (* The binder contexts of a typed case (typingE inversion: only [typeE_Case] and
     [typeE_Cumul] type a [tCase]). *)
  Lemma B_typingE_case_ctxs {Σ Γ ci p c brs T} :
    Σ ;;; Γ |-E tCase ci p c brs : T ->
    ∑ mdecl idecl, declared_inductive Σ ci.(ci_ind) mdecl idecl ×
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ×
      All2i (fun i cdecl br => eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl))
        0 idecl.(ind_ctors) brs.
  Proof using Type.
    intros h. remember (tCase ci p c brs) as t eqn:e.
    induction h; try discriminate e.
    - injection e as -> -> -> ->.
      exists mdecl, idecl.
      match goal with H : case_side_conditions _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H end.
      match goal with H : case_branch_typing _ _ _ _ _ _ _ _ _ _ |- _ => destruct H end.
      split; [assumption|]. split; [assumption|].
      eapply All2i_impl; [eassumption|]. intros i cdecl br [hb _]. exact hb.
    - exact (IHh1 e).
  Qed.

  Lemma B_declared_inductive_uniq {Σ : global_env_ext} (hwf : wf_extE Σ) {ind mdecl idecl mdecl' idecl'} :
    declared_inductive Σ ind mdecl idecl -> declared_inductive Σ ind mdecl' idecl' ->
    mdecl = mdecl' /\ idecl = idecl'.
  Proof using Type.
    intros d d'.
    have hwfE : wfE Σ := wf_extE_wfE Σ hwf.
    have g := declared_inductive_to_gen (wfΣ := hwfE) d.
    have g' := declared_inductive_to_gen (wfΣ := hwfE) d'.
    exact (declared_inductive_inj g' g).
  Qed.

  Lemma B_wt_case_ctxs Σ (wfΣ : abstract_env_ext_rel X Σ) Γ π ci p c brs :
    no_Eta_arg π -> welltypedE Σ Γ (zipc (tCase ci p c brs) π) ->
    ∥ ∑ mdecl idecl, declared_inductive Σ ci.(ci_ind) mdecl idecl ×
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ×
      All2i (fun i cdecl br => eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl))
        0 idecl.(ind_ctors) brs ∥.
  Proof using conv_factsE.
    intros hna h. destruct (heΣ _ wfΣ) as [hwf].
    destruct (ctf_context Σ Γ _ π hwf hna h) as [T hT].
    constructor. exact (B_typingE_case_ctxs hT).
  Qed.

  Lemma B_wt_case_open Σ (wfΣ : abstract_env_ext_rel X Σ) Γ π ci p c brs :
    no_Eta_arg π -> welltypedE Σ Γ (zipc (tCase ci p c brs) π) ->
    is_open_term (Γ ,,, stack_context π) (tCase ci p c brs).
  Proof using conv_factsE.
    intros hna h. destruct (heΣ _ wfΣ) as [hwf].
    exact (ref_open_term Σ _ _ hwf (ctf_context Σ Γ _ π hwf hna h)).
  Qed.

  (* The two cases of a Case view have as many branches (the impossible branches). *)
  Lemma B_case_brs_length Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs π p' c' brs' π' :
    no_Eta_arg π -> no_Eta_arg π' ->
    welltypedE Σ Γ (zipc (tCase ci p c brs) π) ->
    welltypedE Σ Γ (zipc (tCase ci p' c' brs') π') -> #|brs| = #|brs'|.
  Proof using conv_factsE.
    intros hna hna' h h'. destruct (heΣ _ wfΣ) as [hwf].
    destruct (B_wt_case_ctxs Σ wfΣ Γ π ci p c _ hna h) as [(mdecl & idecl & d & _ & hb)].
    destruct (B_wt_case_ctxs Σ wfΣ Γ π' ci p' c' _ hna' h') as [(mdecl' & idecl' & d' & _ & hb')].
    destruct (B_declared_inductive_uniq hwf d d') as [-> ->].
    apply All2i_length in hb. apply All2i_length in hb'. congruence.
  Qed.

  (* The branch at the same index of the two cases: equal binder names (typing), and both
     contexts closed over the parameters (scoping). *)
  Lemma B_case_brs_ctx Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs1 b brs2 π p' c' brs1' b' brs2' π' :
    no_Eta_arg π -> no_Eta_arg π' -> #|brs1| = #|brs1'| ->
    welltypedE Σ Γ (zipc (tCase ci p c (brs1 ++ b :: brs2)) π) ->
    welltypedE Σ Γ (zipc (tCase ci p' c' (brs1' ++ b' :: brs2')) π') ->
    ∥ eq_context_upto_names (bcontext b) (bcontext b') ∥ /\
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| (bcontext b) /\
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p'| (bcontext b').
  Proof using conv_factsE.
    intros hna hna' hl h h'.
    destruct (heΣ _ wfΣ) as [hwf].
    have ho := B_wt_case_open Σ wfΣ Γ π ci p c _ hna h.
    have ho' := B_wt_case_open Σ wfΣ Γ π' ci p' c' _ hna' h'.
    cbn [on_free_vars] in ho, ho'.
    move/and5P: ho => [_ _ _ _ hb]. move/and5P: ho' => [_ _ _ _ hb'].
    rewrite forallb_app /= in hb. rewrite forallb_app /= in hb'.
    move/andP: hb => [_ /andP [/andP [hb _] _]]. move/andP: hb' => [_ /andP [/andP [hb' _] _]].
    split; [|split; [exact hb|exact hb']].
    destruct (B_wt_case_ctxs Σ wfΣ Γ π ci p c _ hna h) as [(mdecl & idecl & d & _ & hi)].
    destruct (B_wt_case_ctxs Σ wfΣ Γ π' ci p' c' _ hna' h') as [(mdecl' & idecl' & d' & _ & hi')].
    destruct (B_declared_inductive_uniq hwf d d') as [-> ->].
    have e1 : nth_error (brs1 ++ b :: brs2) #|brs1| = Some b.
    { rewrite (nth_error_app_ge brs1 (b :: brs2) #|brs1| (le_n _)) Nat.sub_diag. reflexivity. }
    have e2 : nth_error (brs1' ++ b' :: brs2') #|brs1| = Some b'.
    { rewrite hl (nth_error_app_ge brs1' (b' :: brs2') #|brs1'| (le_n _)) Nat.sub_diag. reflexivity. }
    destruct (All2i_nth_error_r _ _ _ _ _ _ hi e1) as [cdecl [ec hc]].
    destruct (All2i_nth_error_r _ _ _ _ _ _ hi' e2) as [cdecl' [ec' hc']].
    rewrite ec in ec'. noconf ec'.
    constructor. etransitivity; [exact hc|]. symmetry. exact hc'.
  Qed.

  (* The predicates of the two cases: equal binder names (typing), closed contexts (scoping),
     well-formed universe instances (named field [ctf_wf_universes]). *)
  Lemma B_case_pred_ctx Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs π p' c' brs' π' :
    no_Eta_arg π -> no_Eta_arg π' ->
    welltypedE Σ Γ (zipc (tCase ci p c brs) π) ->
    welltypedE Σ Γ (zipc (tCase ci p' c' brs') π') ->
    ∥ eq_context_upto_names (pcontext p) (pcontext p') ∥ /\
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| (pcontext p) /\
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p'| (pcontext p') /\
    forallb (wf_universeb Σ) (map Universe.make' (puinst p)) /\
    forallb (wf_universeb Σ) (map Universe.make' (puinst p')).
  Proof using conv_factsE.
    intros hna hna' h h'.
    destruct (heΣ _ wfΣ) as [hwf].
    have ho := B_wt_case_open Σ wfΣ Γ π ci p c brs hna h.
    have ho' := B_wt_case_open Σ wfΣ Γ π' ci p' c' brs' hna' h'.
    pose proof (ctf_wf_universes Σ (Γ ,,, stack_context π) (tCase ci p c brs) hwf
                  (ctf_context Σ Γ (tCase ci p c brs) π hwf hna h)) as hu.
    pose proof (ctf_wf_universes Σ (Γ ,,, stack_context π') (tCase ci p' c' brs') hwf
                  (ctf_context Σ Γ (tCase ci p' c' brs') π' hwf hna' h')) as hu'.
    cbn [on_free_vars] in ho, ho'.
    move/and5P: ho => [_ _ hc _ _]. move/and5P: ho' => [_ _ hc' _ _].
    unfold wf_universes in hu, hu'. cbn [on_universes] in hu, hu'.
    apply andb_prop in hu as [hu _]. apply andb_prop in hu' as [hu' _].
    split; [|split; [exact hc|split; [exact hc'|split; [exact hu|exact hu']]]].
    destruct (B_wt_case_ctxs Σ wfΣ Γ π ci p c brs hna h) as [(mdecl & idecl & d & hp & _)].
    destruct (B_wt_case_ctxs Σ wfΣ Γ π' ci p' c' brs' hna' h') as [(mdecl' & idecl' & d' & hp' & _)].
    destruct (B_declared_inductive_uniq hwf d d') as [-> ->].
    constructor. etransitivity; [exact hp|]. symmetry. exact hp'.
  Qed.

  (* A real frame's binders in the η context, for a context closed over the parameters. *)
  Lemma B_ctx_inst_case π ps u m :
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|ps| m ->
    fold_context_k (fun k => eta_rename π k) (inst_case_context ps u m) =
    inst_case_context (map (eta_rename π 0) ps) u m.
  Proof using Type.
    intros hm.
    change (fold_context_k (fun k => eta_rename π k) (inst_case_context ps u m))
      with (fold_context_k (fun k => eta_rename π (0 + k)) (inst_case_context ps u m)).
    rewrite eta_rename_fold_context (PCUICRenameConv.rename_inst_case_context_wf _ _ _ _ hm).
    f_equal. apply map_ext => t. symmetry. apply eta_rename_rename.
  Qed.

  Lemma B_ctx_Case_branch Γ ci p c brs1 m brs2 π :
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| m ->
    Γ ,,, stack_context_eta (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π) =
    Γ ,,, stack_context_eta π ,,, inst_case_context (map (eta_rename π 0) (pparams p)) (puinst p) m.
  Proof using Type.
    intros hm.
    cbn [stack_context_eta stack_entry_context_eta stack_entry_context branches_hole_context].
    rewrite (B_ctx_inst_case π _ _ _ hm). now rewrite /app_context app_assoc.
  Qed.

  Lemma B_ctx_Case_pred_return Γ ci pars u pctx c brs π :
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pars| pctx ->
    Γ ,,, stack_context_eta (Case_pred ci (pred_hole_return pars u pctx) c brs :: π) =
    Γ ,,, stack_context_eta π ,,, inst_case_context (map (eta_rename π 0) pars) u pctx.
  Proof using Type.
    intros hm.
    cbn [stack_context_eta stack_entry_context_eta stack_entry_context predicate_hole_context].
    rewrite (B_ctx_inst_case π _ _ _ hm). now rewrite /app_context app_assoc.
  Qed.

  (* The η view of the focus under a real frame that is not an application. *)
  Lemma B_zipp_eta_real t se π :
    is_eta_frame se = false -> match se with App_l _ => false | _ => true end = true ->
    zipp_eta t (se :: π) = eta_rename π (#|stack_entry_context se| + 0) t.
  Proof using Type. intros he ha. destruct se; try discriminate; reflexivity. Qed.

  Lemma B_zipp_eta_Case_branch t ci p c brs1 m brs2 π :
    zipp_eta t (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π) = eta_rename π (#|m| + 0) t.
  Proof using Type.
    rewrite (B_zipp_eta_real t (Case_branch ci p c (brs1, branch_hole_body m, brs2)) π eq_refl eq_refl).
    cbn [stack_entry_context branches_hole_context]. now rewrite inst_case_context_length.
  Qed.

  Lemma B_zipp_eta_Case_pred_return t ci pars u pctx c brs π :
    zipp_eta t (Case_pred ci (pred_hole_return pars u pctx) c brs :: π) = eta_rename π (#|pctx| + 0) t.
  Proof using Type.
    rewrite (B_zipp_eta_real t (Case_pred ci (pred_hole_return pars u pctx) c brs) π eq_refl eq_refl).
    cbn [stack_entry_context predicate_hole_context]. now rewrite inst_case_context_length.
  Qed.

  (* A real frame strictly deepens the position (the R descents). *)
  Lemma B_positionR_frame se π : is_eta_frame se = false ->
    positionR (stack_position (se :: π)) (stack_position π).
  Proof using Type.
    intros he. destruct se; try discriminate; cbn [stack_position];
      rewrite -{2}(app_nil_r (stack_position π)); apply positionR_poscat; constructor.
  Qed.

  (* The fixpoint context of two lists of definitions with convertible types. *)
  Lemma B_ctx_fix_context_gen Σ (cb : ClosedBodies Σ) ΓL ΓR (M M' : mfixpoint term) n Ξ Ξ' :
    #|Ξ| = n ->
    ws_cumul_ctx_pbE Conv Σ (ΓL ,,, Ξ) (ΓR ,,, Ξ') ->
    All2 (fun d d' => ws_cumul_pbE Conv Σ ΓL (dtype d) (dtype d') × eq_binder_annot (dname d) (dname d')) M M' ->
    ws_cumul_ctx_pbE Conv Σ
      (ΓL ,,, Ξ ,,, List.rev (mapi_rec (fun i d => vass (dname d) (lift0 i (dtype d))) M n))
      (ΓR ,,, Ξ' ,,, List.rev (mapi_rec (fun i d => vass (dname d) (lift0 i (dtype d))) M' n)).
  Proof using Type.
    intros hn hc hM.
    induction hM as [|d d' M M' [hd hna] hM IH] in n, Ξ, Ξ', hn, hc |- *; cbn [mapi_rec List.rev].
    - exact hc.
    - have hc' : ws_cumul_ctx_pbE Conv Σ (ΓL ,,, (Ξ ,, vass (dname d) (lift0 n (dtype d))))
                   (ΓR ,,, (Ξ' ,, vass (dname d') (lift0 n (dtype d')))).
      { constructor; [exact hc|]. constructor; [exact hna|].
        have hcl := ws_cumul_ctx_pbE_closed_left _ _ _ _ hc.
        subst n.
        exact (PCUICWsCumulEtaSubst.weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := cb) (pb := Conv)
                 (Γ := ΓL) (Γ' := []) (Γ'' := Ξ) hd hcl). }
      pose proof (IH (S n) (Ξ ,, vass (dname d) (lift0 n (dtype d))) (Ξ' ,, vass (dname d') (lift0 n (dtype d')))
                    ltac:(cbn; lia) hc') as IH'.
      rewrite /app_context -!app_assoc. exact IH'.
  Qed.

  Lemma B_ctx_fix_context Σ (cb : ClosedBodies Σ) ΓL ΓR (M M' : mfixpoint term) :
    ws_cumul_ctx_pbE Conv Σ ΓL ΓR ->
    All2 (fun d d' => ws_cumul_pbE Conv Σ ΓL (dtype d) (dtype d') × eq_binder_annot (dname d) (dname d')) M M' ->
    ws_cumul_ctx_pbE Conv Σ (ΓL ,,, fix_context M) (ΓR ,,, fix_context M').
  Proof using Type.
    intros hc hM. exact (B_ctx_fix_context_gen Σ cb ΓL ΓR M M' 0 [] [] eq_refl hc hM).
  Qed.

  (* A fixpoint body frame's binders in the η context. *)
  Lemma B_fix_ctx_eta π (M : mfixpoint term) :
    fold_context_k (fun k => eta_rename π k) (fix_context_alt (map def_sig M)) =
    fix_context (map (map_def (rename (eta_ren π 0)) (rename (shiftn #|M| (eta_ren π 0)))) M).
  Proof using Type.
    rewrite -fix_context_fix_context_alt.
    change (fold_context_k (fun k => eta_rename π k) (fix_context M))
      with (fold_context_k (fun k => eta_rename π (0 + k)) (fix_context M)).
    rewrite eta_rename_fold_context. symmetry. exact (eta_rename_fix_context π 0 M).
  Qed.

  Definition eta_rename_pred (π : stack) (p : predicate term) : predicate term :=
    {| pparams := map (eta_rename π 0) p.(pparams); puinst := p.(puinst);
       pcontext := p.(pcontext); preturn := eta_rename π (#|p.(pcontext)| + 0) p.(preturn) |}.

  Definition eta_rename_br (π : stack) (br : branch term) : branch term :=
    {| bcontext := br.(bcontext); bbody := eta_rename π (#|br.(bcontext)| + 0) br.(bbody) |}.

  Definition ws_cumul_pbE_brs Σ Γ (π π' : stack) (p : predicate term) (brs brs' : list (branch term)) :=
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
      ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,,
                           inst_case_branch_context (eta_rename_pred π p) (eta_rename_br π br))
        (bbody (eta_rename_br π br)) (bbody (eta_rename_br π' br'))) brs brs'.

  Definition ws_cumul_pbE_predicate Σ Γ (π π' : stack) (p p' : predicate term) :=
    [× ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π)
         (pparams (eta_rename_pred π p)) (pparams (eta_rename_pred π' p')),
       cmp_universe_instance (compare_universe Σ Conv) (puinst p) (puinst p'),
       eq_context_upto_names (pcontext p) (pcontext p') &
       ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,, inst_case_predicate_context (eta_rename_pred π p))
         (preturn (eta_rename_pred π p)) (preturn (eta_rename_pred π' p'))].

  (* One branch of the E branch relation from the Reduction result on the branch bodies. *)
  Lemma B_brs_elem Σ Γ ci p c brs1 m br brs2 π p' c' brs1' m' br' brs2' π' :
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| m ->
    eq_context_upto_names m m' ->
    conv_cumE Conv Σ (Γ ,,, stack_context_eta (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π))
      (zipp_eta br (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π))
      (zipp_eta br' (Case_branch ci p' c' (brs1', branch_hole_body m', brs2') :: π')) ->
    ∥ eq_context_upto_names (bcontext {| bcontext := m; bbody := br |}) (bcontext {| bcontext := m'; bbody := br' |}) ×
      ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,,
          inst_case_branch_context (eta_rename_pred π p) (eta_rename_br π {| bcontext := m; bbody := br |}))
        (bbody (eta_rename_br π {| bcontext := m; bbody := br |}))
        (bbody (eta_rename_br π' {| bcontext := m'; bbody := br' |})) ∥.
  Proof using Type.
    intros hm hmm' [h]. constructor. split; [exact hmm'|].
    rewrite (B_ctx_Case_branch _ _ _ _ _ _ _ _ hm) !B_zipp_eta_Case_branch in h. exact h.
  Qed.

  (* The return-predicate part of the E predicate relation from the Reduction result. *)
  Lemma B_pred_ret Σ Γ ci p c brs π ci' p' c' brs' π' :
    test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| (pcontext p) ->
    conv_cumE Conv Σ (Γ ,,, stack_context_eta (Case_pred ci (pred_hole_return (pparams p) (puinst p) (pcontext p)) c brs :: π))
      (zipp_eta (preturn p) (Case_pred ci (pred_hole_return (pparams p) (puinst p) (pcontext p)) c brs :: π))
      (zipp_eta (preturn p') (Case_pred ci' (pred_hole_return (pparams p') (puinst p') (pcontext p')) c' brs' :: π')) ->
    ∥ ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,, inst_case_predicate_context (eta_rename_pred π p))
        (preturn (eta_rename_pred π p)) (preturn (eta_rename_pred π' p')) ∥.
  Proof using Type.
    intros hc [h]. constructor.
    rewrite (B_ctx_Case_pred_return _ _ _ _ _ _ _ _ hc) !B_zipp_eta_Case_pred_return in h. exact h.
  Qed.

  (* Every helper below is called from a T1-guarded view of [_isconv_prog], whose equation
     [hg] it receives; it pushes only real frames, so [virt_ok] holds by [no_Eta_arg]. *)
  Equations isconv_branches (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs1 brs2 : list (branch term))
    (π : stack) (f : wf_stack π) (h : wtp Γ (tCase ci p c (brs1 ++ brs2)) π)
    (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
    (π' : stack) (f' : wf_stack π') (h' : wtp Γ (tCase ci p' c' (brs1' ++ brs2')) π')
    (hx : conv_stack_ctx Γ π π')
    (hg : no_Eta_arg π && no_Eta_arg π' = true)
    (hwf : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥)
    (hwf' : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π') ∥)
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pbE_predicate Σ Γ π π' p p' ∥)
    (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pbE_brs Σ Γ π π' p brs1 brs1' ∥)
    (aux : Aux Term Γ (tCase ci p c (brs1 ++ brs2)) π (tCase ci p' c' (brs1' ++ brs2')) π' f f' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pbE_brs Σ Γ π π' p brs2 brs2' ∥)
    by struct brs2 :=

    isconv_branches Γ ci
      p c brs1 ({| bcontext := m; bbody := br |} :: brs2) π f h
      p' c' brs1' ({| bcontext := m'; bbody := br' |} :: brs2') π' f' h' hx hg hwf hwf' hp h1 aux
     with isconv_red_raw Conv
              br (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π)
              br' (Case_branch ci p' c' (brs1', branch_hole_body m', brs2') :: π') aux := {
      | Success h2
        with isconv_branches Γ ci
              p c (brs1 ++ [{|bcontext := m; bbody := br|}]) brs2 π f _
              p' c' (brs1' ++ [{| bcontext := m'; bbody := br'|}]) brs2' π' f' _ hx hg hwf hwf' hp _ (expand aux) := {
        | Success h3 := yes ;
        | Error e := no e
        } ;
      | Error e := no e
    } ;

    isconv_branches Γ ci
      p c brs1 [] π f h
      p' c' brs1' [] π' f' h' hx hg hwf hwf' hp h1 aux := yes ;

    isconv_branches Γ ci
      p c brs1 brs2 π f h
      p' c' brs1' brs2' π' f' h' hx hg hwf hwf' hp h1 aux := False_rect _ _.
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    have [hna hna'] := andb_prop _ _ hg.
    have e := B_case_brs_length Σ wfΣ Γ ci p c _ π p' c' _ π' hna hna' (h Σ wfΣ) (h' Σ wfΣ).
    destruct (h1 Σ wfΣ) as [hb]. apply All2_length in hb.
    rewrite !length_app /= in e. lia.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    have [hna hna'] := andb_prop _ _ hg.
    have e := B_case_brs_length Σ wfΣ Γ ci p c _ π p' c' _ π' hna hna' (h Σ wfΣ) (h' Σ wfΣ).
    destruct (h1 Σ wfΣ) as [hb]. apply All2_length in hb.
    rewrite !length_app /= in e. lia.
  Qed.
  Next Obligation.
    eapply R_positionR; cbn -[stack_position].
    - constructor. reflexivity.
    - apply B_positionR_frame. reflexivity.
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna hna'] := andb_prop _ _ hg.
    destruct (hΣ _ wfR) as [cb]. destruct (hx _ wfR) as [hx']. destruct (hp _ wfR) as [[hpars hu _ _]].
    destruct (h1 _ wfR) as [hb]. apply All2_length in hb.
    destruct (B_case_brs_ctx Σ wfR Γ ci p c brs1 _ brs2 π p' c' brs1' _ brs2' π' hna hna' hb (h _ wfR) (h' _ wfR))
      as [[hmm'] [hm hm']].
    cbn [bcontext] in hmm', hm, hm'.
    constructor.
    rewrite (B_ctx_Case_branch _ _ _ _ _ _ _ _ hm) (B_ctx_Case_branch _ _ _ _ _ _ _ _ hm').
    eapply inst_case_ws_cumul_ctx_pbE; tea.
    - rewrite length_map -test_context_k_closed_on_free_vars_ctx. exact hm.
    - rewrite length_map -test_context_k_closed_on_free_vars_ctx. exact hm'.
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna _] := andb_prop _ _ hg.
    destruct (heΣ _ wfR) as [hwfe]. destruct (hwf _ wfR) as [hw].
    exact (wf_localE_push_real welltypedE_context Σ (wfΣ := wf_extE_wfE _ hwfe) Γ br
             (Case_branch ci p c (brs1, branch_hole_body m, brs2)) π eq_refl hna (h _ wfR) hw).
  Qed.
  Next Obligation.
    B_rel wfR.
    have [_ hna'] := andb_prop _ _ hg.
    destruct (heΣ _ wfR) as [hwfe]. destruct (hwf' _ wfR) as [hw].
    exact (wf_localE_push_real welltypedE_context Σ (wfΣ := wf_extE_wfE _ hwfe) Γ br'
             (Case_branch ci p' c' (brs1', branch_hole_body m', brs2')) π' eq_refl hna' (h' _ wfR) hw).
  Qed.
  Next Obligation.
    B_rel wfR. rewrite <- app_assoc. exact (h _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. rewrite <- app_assoc. exact (h' _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna hna'] := andb_prop _ _ hg.
    destruct (h1 _ wfR) as [hb1]. have hl := All2_length hb1.
    destruct (B_case_brs_ctx Σ wfR Γ ci p c brs1 _ brs2 π p' c' brs1' _ brs2' π' hna hna' hl (h _ wfR) (h' _ wfR))
      as [[hmm'] [hm _]].
    destruct (B_brs_elem Σ Γ ci p c brs1 m br brs2 π p' c' brs1' m' br' brs2' π' hm hmm' (h2 _ wfR)) as [he].
    constructor. apply All2_app; [exact hb1|]. constructor; [exact he|constructor].
  Qed.
  Next Obligation.
    eapply R_irrelevance; [|eassumption]. cbn. now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna hna'] := andb_prop _ _ hg.
    destruct (h1 _ wfR) as [hb1]. have hl := All2_length hb1.
    destruct (B_case_brs_ctx Σ wfR Γ ci p c brs1 _ brs2 π p' c' brs1' _ brs2' π' hna hna' hl (h _ wfR) (h' _ wfR))
      as [[hmm'] [hm _]].
    destruct (B_brs_elem Σ Γ ci p c brs1 m br brs2 π p' c' brs1' m' br' brs2' π' hm hmm' (h2 _ wfR)) as [he].
    destruct (h3 _ wfR) as [hb3].
    constructor. constructor; [exact he|exact hb3].
  Qed.

  Equations isconv_branches' (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs : list (branch term))
    (π : stack) (f : wf_stack π) (h : wtp Γ (tCase ci p c brs) π)
    (ci' : case_info)
    (p' : predicate term) (c' : term) (brs' : list (branch term))
    (π' : stack) (f' : wf_stack π') (h' : wtp Γ (tCase ci' p' c' brs') π')
    (hx : conv_stack_ctx Γ π π')
    (hg : no_Eta_arg π && no_Eta_arg π' = true)
    (hwf : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥)
    (hwf' : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π') ∥)
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pbE_predicate Σ Γ π π' p p' ∥)
    (ei : ci = ci')
    (aux : Aux Term Γ (tCase ci p c brs) π (tCase ci' p' c' brs') π' f f' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pbE_brs Σ Γ π π' p brs brs' ∥) :=

    isconv_branches' Γ ci p c brs π f h ci' p' c' brs' π' f' h' hx hg hwf hwf' hp eci aux :=
      isconv_branches Γ ci p c [] brs π f _ p' c' [] brs' π' f' _ hx hg hwf hwf' hp _ (expand aux).
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

  (* Slice B helpers for the fixpoint body frame. *)
  Lemma B_ctx_Fix_body_fold Γ fk mfix1 na ty ra mfix2 idx π :
    Γ ,,, stack_context_eta (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx :: π) =
    Γ ,,, stack_context_eta π ,,,
      fold_context_k (fun k => eta_rename π k) (fix_context_alt (map def_sig mfix1 ++ (na, ty) :: map def_sig mfix2)).
  Proof using Type.
    destruct fk; cbn [mFix_mfix stack_context_eta stack_entry_context_eta stack_entry_context mfix_hole_context];
      now rewrite /app_context app_assoc.
  Qed.

  Lemma B_ctx_Fix_body Γ fk mfix1 u mfix2 idx π :
    Γ ,,, stack_context_eta (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π) =
    Γ ,,, stack_context_eta π ,,,
      fix_context (map (map_def (rename (eta_ren π 0)) (rename (shiftn #|mfix1 ++ u :: mfix2| (eta_ren π 0))))
        (mfix1 ++ u :: mfix2)).
  Proof using Type.
    rewrite -B_fix_ctx_eta map_app B_ctx_Fix_body_fold. reflexivity.
  Qed.

  Lemma B_zipp_eta_Fix_body fk t mfix1 na ty ra mfix2 idx π (d : def term) :
    zipp_eta t (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx :: π) =
    eta_rename π (#|mfix1 ++ d :: mfix2| + 0) t.
  Proof using Type.
    have e : #|fix_context_alt (map def_sig mfix1 ++ (na, ty) :: map def_sig mfix2)| = #|mfix1 ++ d :: mfix2|.
    { rewrite /fix_context_alt List.length_rev mapi_length !length_app /= !length_map. reflexivity. }
    destruct fk; cbn [mFix_mfix].
    - rewrite (B_zipp_eta_real t (Fix (mfix1, def_hole_body na ty ra, mfix2) idx) π eq_refl eq_refl).
      cbn [stack_entry_context mfix_hole_context]. now rewrite e.
    - rewrite (B_zipp_eta_real t (CoFix (mfix1, def_hole_body na ty ra, mfix2) idx) π eq_refl eq_refl).
      cbn [stack_entry_context mfix_hole_context]. now rewrite e.
  Qed.

  (* One body of the E fixpoint-bodies relation from the Reduction result on the bodies. *)
  Lemma B_fix_body_elem Σ Γ fk mfix1 u mfix2 idx π mfix1' v mfix2' π' :
    conv_cumE Conv Σ (Γ ,,, stack_context_eta (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π))
      (zipp_eta u.(dbody) (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π))
      (zipp_eta v.(dbody) (mFix_mfix fk (mfix1', def_hole_body v.(dname) v.(dtype) v.(rarg), mfix2') idx :: π')) ->
    ∥ ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,,
          fold_context_k (fun k => eta_rename π k) (fix_context_alt (map def_sig mfix1 ++ def_sig u :: map def_sig mfix2)))
        (eta_rename π (#|mfix1 ++ u :: mfix2| + 0) u.(dbody))
        (eta_rename π' (#|mfix1' ++ v :: mfix2'| + 0) v.(dbody)) ∥.
  Proof using Type.
    intros [h]. constructor.
    rewrite B_ctx_Fix_body_fold (B_zipp_eta_Fix_body _ _ _ _ _ _ _ _ _ u)
      (B_zipp_eta_Fix_body _ _ _ _ _ _ _ _ _ v) in h.
    exact h.
  Qed.

  Equations isws_cumul_pb_fix_types (fk : fix_kind) (Γ : context)
    (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack) (f : wf_stack π)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack) (f' : wf_stack π')
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (hg : no_Eta_arg π && no_Eta_arg π' = true)
    (hwf : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥)
    (hwf' : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π') ∥)
    (h1 : ∥ All2 (fun u v =>
                   (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
                      ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π)
                        (eta_rename π 0 u.(dtype)) (eta_rename π' 0 v.(dtype))) ×
                   (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
            ) mfix1 mfix1' ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' f f' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
             ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π)
               (eta_rename π 0 u.(dtype)) (eta_rename π' 0 v.(dtype))) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix2 mfix2' ∥)
    by struct mfix2 :=

    isws_cumul_pb_fix_types
      fk Γ idx mfix1 (u :: mfix2) π f h mfix1' (v :: mfix2') π' f' h' hx hg hwf hwf' h1 aux
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
            (mfix1 ++ [u]) mfix2 π f _
            (mfix1' ++ [v]) mfix2' π' f' _
            hx hg hwf hwf' _ (expand aux)
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

    isws_cumul_pb_fix_types fk Γ idx mfix1 [] π f h mfix1' [] π' f' h' hx hg hwf hwf' h1 aux := yes ;

    (* TODO It might be more efficient to check the lengths first
       and then conclude this case is not possible.
    *)
    isws_cumul_pb_fix_types fk Γ idx mfix1 mfix2 π f h mfix1' mfix2' π' f' h' hx hg hwf hwf' h1 aux :=
      no (
        mFixMfixMismatch fk idx
          (Γ ,,, stack_context π) (mfix1 ++ mfix2)
          (Γ ,,, stack_context π') (mfix1' ++ mfix2')
      ).

  Next Obligation.
    have [hna _] := andb_prop _ _ hg. destruct fk; exact hna.
  Qed.
  Next Obligation.
    have [_ hna'] := andb_prop _ _ hg. destruct fk; exact hna'.
  Qed.
  Next Obligation.
    B_rel wfR. destruct u. destruct fk; exact (h _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. destruct v. destruct fk; exact (h' _ wfR).
  Qed.
  Next Obligation.
    eapply R_positionR; cbn -[stack_position].
    - constructor. destruct u, fk; reflexivity.
    - apply B_positionR_frame. destruct fk; reflexivity.
  Qed.
  Next Obligation.
    B_rel wfR. destruct fk; exact (hx _ wfR).
  Qed.
  Next Obligation.
    have [hna _] := andb_prop _ _ hg.
    destruct fk; unfold virt_ok; cbn [no_Eta_arg is_Eta_arg negb andb mFix_mfix]; rewrite hna; reflexivity.
  Qed.
  Next Obligation.
    have [_ hna'] := andb_prop _ _ hg.
    destruct fk; unfold virt_ok; cbn [no_Eta_arg is_Eta_arg negb andb mFix_mfix]; rewrite hna'; reflexivity.
  Qed.
  Next Obligation.
    B_rel wfR. destruct fk; exact (hwf _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. destruct fk; exact (hwf' _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. rewrite <- app_assoc. exact (h _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. rewrite <- app_assoc. exact (h' _ wfR).
  Qed.
  Next Obligation.
    destruct h1 as [hb1].
    destruct (abstract_env_ext_exists X) as [[Σ0 wfΣ0]].
    destruct (h2 _ wfΣ0) as [h2'].
    change (true = eqb (rarg u) (rarg v)) in eq1.
    destruct (eqb_specT (rarg u) (rarg v)) as [er|]; [|discriminate].
    symmetry in eqann. apply eqb_binder_annot_spec in eqann.
    constructor. apply All2_app; [exact hb1|]. constructor; [|constructor].
    split; [|split; assumption].
    intros Σ' wfΣ'. rewrite (abstract_env_ext_irr _ wfΣ' wfΣ0). destruct fk; exact h2'.
  Qed.
  Next Obligation.
    eapply R_irrelevance; [|eassumption]. cbn. now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    destruct h3 as [hb3].
    destruct (abstract_env_ext_exists X) as [[Σ0 wfΣ0]].
    destruct (h2 _ wfΣ0) as [h2'].
    change (true = eqb (rarg u) (rarg v)) in eq1.
    destruct (eqb_specT (rarg u) (rarg v)) as [er|]; [|discriminate].
    symmetry in eqann. apply eqb_binder_annot_spec in eqann.
    constructor. constructor; [|exact hb3].
    split; [|split; assumption].
    intros Σ' wfΣ'. rewrite (abstract_env_ext_irr _ wfΣ' wfΣ0). destruct fk; exact h2'.
  Qed.

  Equations isws_cumul_pb_fix_bodies (fk : fix_kind) (Γ : context) (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack) (f : wf_stack π)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack) (f' : wf_stack π')
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (hg : no_Eta_arg π && no_Eta_arg π' = true)
    (hwf : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥)
    (hwf' : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π') ∥)
    (h1 : ∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ),
              ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,,
                fold_context_k (fun k => eta_rename π k) (fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2)))
                (eta_rename π (#|mfix1 ++ mfix2| + 0) u.(dbody))
                (eta_rename π' (#|mfix1' ++ mfix2'| + 0) v.(dbody))) mfix1 mfix1' ∥)
    (ha : ∥ All2 (fun u v =>
                    (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
                       ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π)
                         (eta_rename π 0 u.(dtype)) (eta_rename π' 0 v.(dtype))) ×
                    (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
           ) (mfix1 ++ mfix2) (mfix1' ++ mfix2') ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' f f' h')
    : ConversionResult (∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ),
              ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,,
                fold_context_k (fun k => eta_rename π k) (fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2)))
                (eta_rename π (#|mfix1 ++ mfix2| + 0) u.(dbody))
                (eta_rename π' (#|mfix1' ++ mfix2'| + 0) v.(dbody))) mfix2 mfix2' ∥)
    by struct mfix2 :=

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 (u :: mfix2) π f h mfix1' (v :: mfix2') π' f' h' hx hg hwf hwf' h1 ha aux
  with isconv_red_raw Conv
        u.(dbody)
        (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π)
        v.(dbody)
        (mFix_mfix fk (mfix1', def_hole_body v.(dname) v.(dtype) v.(rarg), mfix2') idx :: π')
        aux
  := {
  | Success h2
    with isws_cumul_pb_fix_bodies fk Γ idx
           (mfix1 ++ [u]) mfix2 π f _
           (mfix1' ++ [v]) mfix2' π' f' _
           hx hg hwf hwf' _ _ (expand aux)
    := {
    | Success h3 := yes ;
    | Error e := no e
    } ;
  | Error e := no e
  } ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 [] π f h mfix1' [] π' f' h' hx hg hwf hwf' h1 ha aux := yes ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 mfix2 π f h mfix1' mfix2' π' f' h' hx hg hwf hwf' h1 ha aux :=
    False_rect _ _.

  Next Obligation.
    destruct h1 as [hb1], ha as [hba].
    apply All2_length in hb1. apply All2_length in hba.
    rewrite !length_app /= in hba. lia.
  Qed.
  Next Obligation.
    destruct h1 as [hb1], ha as [hba].
    apply All2_length in hb1. apply All2_length in hba.
    rewrite !length_app /= in hba. lia.
  Qed.
  Next Obligation.
    have [hna _] := andb_prop _ _ hg. destruct fk; exact hna.
  Qed.
  Next Obligation.
    have [_ hna'] := andb_prop _ _ hg. destruct fk; exact hna'.
  Qed.
  Next Obligation.
    B_rel wfR. destruct u. destruct fk; exact (h _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. destruct v. destruct fk; exact (h' _ wfR).
  Qed.
  Next Obligation.
    eapply R_positionR; cbn -[stack_position].
    - constructor. destruct u, fk; reflexivity.
    - apply B_positionR_frame. destruct fk; reflexivity.
  Qed.
  Next Obligation.
    B_rel wfR.
    destruct (hΣ _ wfR) as [cb]. destruct (hx _ wfR) as [hx']. destruct ha as [hba].
    constructor. rewrite !B_ctx_Fix_body.
    apply B_ctx_fix_context; [exact cb|exact hx'|].
    apply All2_map. eapply All2_impl; [exact hba|].
    intros d d' [hd [_ hn]]. cbn [dtype dname map_def]. split; [|exact hn].
    rewrite -!eta_rename_rename. exact (hd _ wfR).
  Qed.
  Next Obligation.
    have [hna _] := andb_prop _ _ hg.
    destruct fk; unfold virt_ok; cbn [no_Eta_arg is_Eta_arg negb andb mFix_mfix]; rewrite hna; reflexivity.
  Qed.
  Next Obligation.
    have [_ hna'] := andb_prop _ _ hg.
    destruct fk; unfold virt_ok; cbn [no_Eta_arg is_Eta_arg negb andb mFix_mfix]; rewrite hna'; reflexivity.
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna _] := andb_prop _ _ hg.
    destruct (heΣ _ wfR) as [hwfe]. destruct (hwf _ wfR) as [hw].
    destruct u as [na ty bo ra].
    have hse : is_eta_frame (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx) = false
      by destruct fk; reflexivity.
    have hz : welltypedE Σ Γ (zipc bo (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx :: π))
      by destruct fk; exact (h _ wfR).
    exact (wf_localE_push_real welltypedE_context Σ (wfΣ := wf_extE_wfE _ hwfe) Γ bo
             (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx) π hse hna hz hw).
  Qed.
  Next Obligation.
    B_rel wfR.
    have [_ hna'] := andb_prop _ _ hg.
    destruct (heΣ _ wfR) as [hwfe]. destruct (hwf' _ wfR) as [hw].
    destruct v as [na ty bo ra].
    have hse : is_eta_frame (mFix_mfix fk (mfix1', def_hole_body na ty ra, mfix2') idx) = false
      by destruct fk; reflexivity.
    have hz : welltypedE Σ Γ (zipc bo (mFix_mfix fk (mfix1', def_hole_body na ty ra, mfix2') idx :: π'))
      by destruct fk; exact (h' _ wfR).
    exact (wf_localE_push_real welltypedE_context Σ (wfΣ := wf_extE_wfE _ hwfe) Γ bo
             (mFix_mfix fk (mfix1', def_hole_body na ty ra, mfix2') idx) π' hse hna' hz hw).
  Qed.
  Next Obligation.
    B_rel wfR. rewrite <- app_assoc. exact (h _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. rewrite <- app_assoc. exact (h' _ wfR).
  Qed.
  Next Obligation.
    destruct h1 as [hb1].
    destruct (abstract_env_ext_exists X) as [[Σ0 wfΣ0]].
    destruct (B_fix_body_elem Σ0 Γ fk mfix1 u mfix2 idx π mfix1' v mfix2' π' (h2 _ wfΣ0)) as [e].
    constructor.
    rewrite map_app. cbn [map]. rewrite <- !app_assoc. cbn [app].
    apply All2_app.
    - eapply All2_impl; [exact hb1|]. intros d d' hd Σ' wfΣ'. exact (hd Σ' wfΣ').
    - constructor; [|constructor].
      intros Σ' wfΣ'. rewrite (abstract_env_ext_irr _ wfΣ' wfΣ0). exact e.
  Qed.
  Next Obligation.
    destruct ha as [hba]. constructor. rewrite <- !app_assoc. exact hba.
  Qed.
  Next Obligation.
    eapply R_irrelevance; [|eassumption]. cbn. now rewrite <- !app_assoc.
  Qed.
  Next Obligation.
    destruct h3 as [hb3].
    destruct (abstract_env_ext_exists X) as [[Σ0 wfΣ0]].
    destruct (B_fix_body_elem Σ0 Γ fk mfix1 u mfix2 idx π mfix1' v mfix2' π' (h2 _ wfΣ0)) as [e].
    rewrite map_app in hb3. cbn [map] in hb3. rewrite <- !app_assoc in hb3. cbn [app] in hb3.
    constructor. constructor.
    - intros Σ' wfΣ'. rewrite (abstract_env_ext_irr _ wfΣ' wfΣ0). exact e.
    - exact hb3.
  Qed.

  Equations isws_cumul_pb_Fix (fk : fix_kind) (Γ : context)
    (mfix : mfixpoint term) (idx : nat) (π : stack) (f : wf_stack π)
    (h : wtp Γ (mFix fk mfix idx) π)
    (mfix' : mfixpoint term) (idx' : nat) (π' : stack) (f' : wf_stack π')
    (h' : wtp Γ (mFix fk mfix' idx') π')
    (hx : conv_stack_ctx Γ π π')
    (hg : no_Eta_arg π && no_Eta_arg π' = true)
    (hwf : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥)
    (hwf' : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π') ∥)
    (ei : idx = idx')
    (aux : Aux Term Γ (mFix fk mfix idx) π (mFix fk mfix' idx') π' f f' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
             ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π)
               (eta_rename π 0 u.(dtype)) (eta_rename π' 0 v.(dtype))) ×
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
             ws_cumul_pbE Conv Σ (Γ ,,, stack_context_eta π ,,,
               fold_context_k (fun k => eta_rename π k) (fix_context mfix))
               (eta_rename π (#|mfix| + 0) u.(dbody)) (eta_rename π' (#|mfix'| + 0) v.(dbody))) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ∥) :=

      isws_cumul_pb_Fix fk Γ mfix idx π f h mfix' idx' π' f' h' hx hg hwf hwf' ei aux
    with
      isws_cumul_pb_fix_types fk Γ idx
        [] mfix π f _
        [] mfix' π' f' _
        hx hg hwf hwf' _ (expand aux)
    := {
    | Success h1
      with
        isws_cumul_pb_fix_bodies fk Γ idx
          [] mfix π f _
          [] mfix' π' f' _
          hx hg hwf hwf' _ _ (expand aux)
      := {
      | Success h2 := yes ;
      | Error e := no e
      } ;
    | Error e := no e
    }.

  Next Obligation.
    destruct h1 as [hb1], h2 as [hb2].
    constructor.
    rewrite fix_context_fix_context_alt.
    pose proof (All2_mix hb1 hb2) as h3.
    eapply All2_impl; [exact h3|].
    intros d d' [[ht [hr hn]] hb]. split; [exact ht|]. split; [exact hb|]. split; assumption.
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
            (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 f1 f2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : p1.(pparams) = pre1 ++ post1)
            (eq2 : p2.(pparams) = pre2 ++ post2) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
      ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π1)
          (map (eta_rename π1 0) post1) (map (eta_rename π2 0) post2) ∥) :=
    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2
      hx hg hwf1 hwf2 aux pre1 pre2 [] [] eq1 eq2 => yes;

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2
      hx hg hwf1 hwf2 aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
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
               Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2 hx hg hwf1 hwf2 aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {

        | Error ce => no ce;

        | Success conv_rest => yes
        }
      };

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2 hx hg hwf1 hwf2 aux
      pre1 pre2 post1 post2 eq eq2 => no (CasePredParamsUnequalLength
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2).
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    B_rel wfR. destruct p1. exact (h1 _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. destruct p2. exact (h2 _ wfR).
  Qed.
  Next Obligation.
    eapply R_positionR; cbn -[stack_position].
    - constructor. destruct p1 as [pp pu pc pr]. cbn in eq1. subst pp. reflexivity.
    - apply B_positionR_frame. reflexivity.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. exact eq1.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. exact eq2.
  Qed.
  Next Obligation.
    B_rel wfR.
    destruct (conv_tm _ wfR) as [hc]. destruct (conv_rest _ wfR) as [hr].
    constructor. constructor; [exact hc|exact hr].
  Qed.

  Definition isconv_predicate_params
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 f1 f2 h2) :=
    isconv_predicate_params_aux Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2 hx hg hwf1 hwf2 aux [] []
                                p1.(pparams) p2.(pparams) eq_refl eq_refl.

  (* The E predicate relation includes [eq_context_upto_names] of the two return contexts,
     which the checker does not test: as in base, the yes obligation gets it from the typing
     of the two cases (T6). *)
  Equations (noeqns) isconv_predicate
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (eqci : ci1 = ci2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 f1 f2 h2)
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
        ∥ ws_cumul_pbE_predicate Σ Γ π1 π2 p1 p2 ∥) :=

    isconv_predicate Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2 hx hg hwf1 hwf2 eqci aux
      with isconv_predicate_params
           Γ ci1 p1 c1 brs1 π1 f1 h1 ci2 p2 c2 brs2 π2 f2 h2 hx hg hwf1 hwf2 aux := {

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
    B_rel wfR. destruct p1. exact (h1 _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. destruct p2. exact (h2 _ wfR).
  Qed.
  Next Obligation.
    eapply R_positionR; cbn -[stack_position].
    - constructor. destruct p1; reflexivity.
    - apply B_positionR_frame. reflexivity.
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna hna'] := andb_prop _ _ hg.
    destruct (hΣ _ wfR) as [cb]. destruct (hx _ wfR) as [hx']. destruct (conv_params _ wfR) as [hpars].
    destruct (B_case_pred_ctx Σ wfR Γ ci2 p1 c1 brs1 π1 p2 c2 brs2 π2 hna hna' (h1 _ wfR) (h2 _ wfR))
      as [[hctx] [hc1 [hc2 [hu1 hu2]]]].
    have hu := eqb_universe_instance_spec _ _ Σ wfR hu1 hu2 (eq_sym eq_insts).
    constructor.
    rewrite (B_ctx_Case_pred_return _ _ _ _ _ _ _ _ hc1) (B_ctx_Case_pred_return _ _ _ _ _ _ _ _ hc2).
    eapply inst_case_ws_cumul_ctx_pbE; tea.
    - rewrite length_map -test_context_k_closed_on_free_vars_ctx. exact hc1.
    - rewrite length_map -test_context_k_closed_on_free_vars_ctx. exact hc2.
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna _] := andb_prop _ _ hg.
    destruct (heΣ _ wfR) as [hwfe]. destruct (hwf1 _ wfR) as [hw].
    destruct p1 as [pp pu pc pr].
    exact (wf_localE_push_real welltypedE_context Σ (wfΣ := wf_extE_wfE _ hwfe) Γ pr
             (Case_pred ci2 (pred_hole_return pp pu pc) c1 brs1) π1 eq_refl hna (h1 _ wfR) hw).
  Qed.
  Next Obligation.
    B_rel wfR.
    have [_ hna'] := andb_prop _ _ hg.
    destruct (heΣ _ wfR) as [hwfe]. destruct (hwf2 _ wfR) as [hw].
    destruct p2 as [pp pu pc pr].
    exact (wf_localE_push_real welltypedE_context Σ (wfΣ := wf_extE_wfE _ hwfe) Γ pr
             (Case_pred ci2 (pred_hole_return pp pu pc) c2 brs2) π2 eq_refl hna' (h2 _ wfR) hw).
  Qed.
  Next Obligation.
    B_rel wfR.
    have [hna hna'] := andb_prop _ _ hg.
    destruct (conv_params _ wfR) as [hpars].
    destruct (B_case_pred_ctx Σ wfR Γ ci2 p1 c1 brs1 π1 p2 c2 brs2 π2 hna hna' (h1 _ wfR) (h2 _ wfR))
      as [[hctx] [hc1 [_ [hu1 hu2]]]].
    have hu := eqb_universe_instance_spec _ _ Σ wfR hu1 hu2 (eq_sym eq_insts).
    destruct (B_pred_ret Σ Γ ci2 p1 c1 brs1 π1 ci2 p2 c2 brs2 π2 hc1 (conv_ret _ wfR)) as [hr].
    constructor. split; [exact hpars|exact hu|exact hctx|exact hr].
  Qed.

Notation tPrimArray a := (tPrim (primArray; primArrayModel a)).

Equations (noeqns) isconv_array_values_aux
            (Γ : context)
            (a1 : array_model term)
            (π1 : stack) (f1 : wf_stack π1)
            (h1 : wtp Γ (tPrimArray a1) π1)
            (a2 : array_model term)
            (π2 : stack) (f2 : wf_stack π2)
            (h2 : wtp Γ (tPrimArray a2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
            (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
            (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
            (aux : Aux Term Γ (tPrimArray a1) π1 (tPrimArray a2) π2 f1 f2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : a1.(array_value) = pre1 ++ post1)
            (eq2 : a2.(array_value) = pre2 ++ post2) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
      ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π1)
          (map (eta_rename π1 0) post1) (map (eta_rename π2 0) post2) ∥) :=
    isconv_array_values_aux
      Γ a1 π1 f1 h1 a2 π2 f2 h2
      hx hg hwf1 hwf2 aux pre1 pre2 [] [] eq1 eq2 => yes;

    isconv_array_values_aux
      Γ a1 π1 f1 h1 a2 π2 f2 h2
      hx hg hwf1 hwf2 aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
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
               Γ a1 π1 f1 h1 a2 π2 f2 h2 hx hg hwf1 hwf2 aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {

        | Error ce => no ce;

        | Success conv_rest => yes
        }
      };

    isconv_array_values_aux
      Γ a1 π1 f1 h1 a2 π2 f2 h2 hx hg hwf1 hwf2 aux
      pre1 pre2 post1 post2 eq eq2 => no (ArrayValuesNotSameLength
                                            (Γ,,, stack_context π1) a1
                                            (Γ,,, stack_context π2) a2).
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    B_rel wfR. destruct a1. exact (h1 _ wfR).
  Qed.
  Next Obligation.
    B_rel wfR. destruct a2. exact (h2 _ wfR).
  Qed.
  Next Obligation.
    eapply R_positionR; cbn -[stack_position].
    - constructor. destruct a1 as [al aty adf av]. cbn in eq1. subst av. reflexivity.
    - apply B_positionR_frame. reflexivity.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. exact eq1.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. exact eq2.
  Qed.
  Next Obligation.
    B_rel wfR.
    destruct (conv_tm _ wfR) as [hc]. destruct (conv_rest _ wfR) as [hr].
    constructor. constructor; [exact hc|exact hr].
  Qed.

  Definition isconv_array_values
    (Γ : context)
    (a1 : array_model term)
    (π1 : stack) (f1 : wf_stack π1)
    (h1 : wtp Γ (tPrimArray a1) π1)
    (a2 : array_model term)
    (π2 : stack) (f2 : wf_stack π2)
    (h2 : wtp Γ (tPrimArray a2) π2)
    (hx : conv_stack_ctx Γ π1 π2)
    (hg : no_Eta_arg π1 && no_Eta_arg π2 = true)
    (hwf1 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥)
    (hwf2 : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥)
    (aux : Aux Term Γ (tPrimArray a1) π1 (tPrimArray a2) π2 f1 f2 h2) :=
    isconv_array_values_aux Γ a1 π1 f1 h1 a2 π2 f2 h2 hx hg hwf1 hwf2 aux [] []
      a1.(array_value) a2.(array_value) eq_refl eq_refl.

  (* ===================== EtaSliceC helper lemmas for [_isconv_prog] =====================
     Slice C of K3 (EtaSliceC). Untyped facts on the η stack and the η views, and the E steps
     the obligations of [_isconv_prog] take: openness and closedness from [welltypedE] and the
     η context's [wf_localE], a structural reduction read through the η view, the
     discriminant reduction [reduce_termE], and whnf after [reduce_args_E]. The helpers and
     the obligations use only the section's hypotheses: [ConvTypedFacts] ([ctf_context],
     [ctf_wf_universes]), [ReduceTypedFacts] (through [red_wt]) and EtaPosK4's
     [welltypedE_context] (through [wf_localE_push_real], which uses the proved
     [typingE_rename_P]); no new hypothesis. *)

  (* A real frame strictly deepens the position. *)
  Lemma sliceC_positionR_cons se π : is_eta_frame se = false ->
    positionR (stack_position (se :: π)) (stack_position π).
  Proof.
    intros he. destruct se; try discriminate he;
      cbn [stack_position]; apply positionR_poscat_nonil; discriminate.
  Qed.

  Lemma sliceC_stack_context_decompose π :
    stack_context (decompose_stack π).2 = stack_context π.
  Proof.
    destruct (decompose_stack π) as [l ρ] eqn:e. apply decompose_stack_eq in e. subst π.
    cbn [snd]. now rewrite stack_context_appstack.
  Qed.

  Lemma sliceC_stack_context_eta_decompose π :
    stack_context_eta (decompose_stack π).2 = stack_context_eta π.
  Proof.
    destruct (decompose_stack π) as [l ρ] eqn:e. apply decompose_stack_eq in e. subst π.
    cbn [snd]. now rewrite stack_context_eta_appstack.
  Qed.

  Lemma sliceC_no_Eta_arg_decompose π : no_Eta_arg π -> no_Eta_arg (decompose_stack π).2.
  Proof.
    destruct (decompose_stack π) as [l ρ] eqn:e. apply decompose_stack_eq in e. subst π.
    cbn [snd]. now rewrite no_Eta_arg_appstack.
  Qed.

  Lemma sliceC_zipp_appstack_snd t l π : zipp t (appstack l (decompose_stack π).2) = mkApps t l.
  Proof.
    unfold zipp. rewrite decompose_stack_appstack decompose_stack_snd_idem. cbn [fst].
    now rewrite app_nil_r.
  Qed.

  Lemma sliceC_red_zipp (Σ : global_env) Γ t u π : red Σ Γ t u -> red Σ Γ (zipp t π) (zipp u π).
  Proof.
    intros r. unfold zipp. destruct (decompose_stack π) as [args ρ]. now apply red_mkApps_f.
  Qed.

  Lemma sliceC_open_ctx_len (Γ1 Γ2 : context) (t : term) :
    #|Γ1| = #|Γ2| -> is_open_term Γ2 t -> is_open_term Γ1 t.
  Proof. intros e h. rewrite e. exact h. Qed.

  Lemma sliceC_eta_rename_tProj π d p c : eta_rename π d (tProj p c) = tProj p (eta_rename π d c).
  Proof. rewrite !eta_rename_rename. reflexivity. Qed.

  Lemma sliceC_eta_rename_tPrimArray π d a :
    eta_rename π d (tPrim (primArray; primArrayModel a)) =
    tPrim (primArray; primArrayModel {| array_level := array_level a;
                                         array_value := map (eta_rename π d) (array_value a);
                                         array_default := eta_rename π d (array_default a);
                                         array_type := eta_rename π d (array_type a) |}).
  Proof.
    assert (e : map (eta_rename π d) (array_value a) = map (rename (eta_ren π d)) (array_value a))
      by (apply map_ext; intros; apply eta_rename_rename).
    rewrite e !eta_rename_rename. reflexivity.
  Qed.

  (* The η context of the fix bodies: the renamed fix context is the renamed declarations. *)
  Lemma sliceC_fix_context_eta_rename π mfix :
    fix_context (map (map_def (eta_rename π 0) (eta_rename π (#|mfix| + 0))) mfix) =
    fold_context_k (fun k => eta_rename π k) (fix_context mfix).
  Proof.
    transitivity (rename_context (eta_ren π 0) (fix_context mfix)).
    - rewrite -eta_rename_fix_context. f_equal. apply map_ext. intros d.
      unfold map_def. rewrite !eta_rename_rename. f_equal.
      apply rename_ext. exact (eta_ren_shiftn π #|mfix| 0).
    - exact (eq_sym (eta_rename_fold_context π 0 (fix_context mfix))).
  Qed.

  (* A rigid head in a whnf η view carries no argument and no virtual argument. *)
  Lemma sliceC_zipp_eta_rigid Γ t π :
    isred_full Γ t π -> rigid_head t = true -> zipp_eta t π = eta_rename π 0 t.
  Proof.
    intros [_ hw] hr.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hw Σ wfΣ) as [w].
    destruct (whnf_zipp_eta_rigid _ _ _ _ w hr) as [h1 h2].
    revert h1 h2. unfold zipp_eta, decompose_stack_eta.
    destruct (decompose_stack π) as [args ρ]. cbn [fst snd].
    intros -> ->. reflexivity.
  Qed.

  (* The η context is closed when it is well formed. *)
  Lemma sliceC_closed_ctx Σ (wfΣ : abstract_env_ext_rel X Σ) Γ π :
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥) ->
    is_closed_context (Γ ,,, stack_context_eta π).
  Proof.
    intros hwf. destruct (hwf Σ wfΣ) as [hl].
    destruct (abstract_env_ext_sq_wf _ _ _ wfΣ) as [wΣ].
    exact (PCUICClosedTypEta.wf_local_closed_contextE (wfΣ := wΣ) hl).
  Qed.

  Lemma sliceC_open_view Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π :
    no_Eta_arg π -> welltypedE Σ Γ (zipc t π) ->
    is_closed_context (Γ ,,, stack_context_eta π) ->
    is_open_term (Γ ,,, stack_context_eta π) (zipp_eta t π).
  Proof.
    intros hna h hcl. destruct (heΣ _ wfΣ) as [hwf].
    apply zipp_eta_open; [unfold virt_ok; rewrite hna; reflexivity| |exact hcl].
    exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) Σ Γ _ hwf h).
  Qed.

  Lemma sliceC_open_head Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π :
    no_Eta_arg π -> welltypedE Σ Γ (zipc t π) ->
    is_closed_context (Γ ,,, stack_context_eta π) ->
    is_open_term (Γ ,,, stack_context_eta π) (eta_rename π 0 t).
  Proof.
    intros hna h hcl.
    pose proof (sliceC_open_view Σ wfΣ Γ t π hna h hcl) as ho.
    unfold zipp_eta in ho. rewrite on_free_vars_mkApps in ho.
    now move/andP: ho => [ho _].
  Qed.

  Lemma sliceC_wt_zipp Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π :
    no_Eta_arg π -> welltypedE Σ Γ (zipc t π) ->
    is_closed_context (Γ ,,, stack_context π) /\ is_open_term (Γ ,,, stack_context π) (zipp t π).
  Proof.
    intros hna h. destruct (heΣ _ wfΣ) as [hwf].
    pose proof (PCUICSafeConversionEtaFacts.wt_zipc_zipp Σ Γ t π hwf hna h) as h'.
    split.
    - exact (ref_closed_context (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf h').
    - exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) Σ _ _ hwf h').
  Qed.

  (* A reduction of the structural view, read through the η view. *)
  Lemma sliceC_red_eta_view (Σ : global_env_ext) (cb : ClosedBodies Σ) Γ ρ x y :
    no_Eta_arg ρ -> is_closed_context (Γ ,,, stack_context ρ) ->
    is_open_term (Γ ,,, stack_context ρ) x ->
    red Σ (Γ ,,, stack_context ρ) x y ->
    red Σ (Γ ,,, stack_context_eta ρ)
      (mkApps (eta_rename ρ 0 x) (eta_virtuals (eta_run ρ)))
      (mkApps (eta_rename ρ 0 y) (eta_virtuals (eta_run ρ))).
  Proof.
    intros hna hcl ho r. apply red_mkApps_f.
    exact (eta_rename_red Σ Γ ρ x y cb hna hcl ho r).
  Qed.

  Lemma sliceC_closed_red_view Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π y :
    no_Eta_arg π -> welltypedE Σ Γ (zipc t π) ->
    is_closed_context (Γ ,,, stack_context_eta π) ->
    red Σ (Γ ,,, stack_context π) (zipp t π) y ->
    ∥ Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta t π ⇝
        mkApps (eta_rename (decompose_stack π).2 0 y) (eta_virtuals (eta_run (decompose_stack π).2)) ∥.
  Proof.
    intros hna h hcl r.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (sliceC_wt_zipp Σ wfΣ Γ t π hna h) as [hcl0 ho0].
    constructor.
    apply into_closed_red; [|exact hcl|exact (sliceC_open_view Σ wfΣ Γ t π hna h hcl)].
    rewrite zipp_eta_decompose -(sliceC_stack_context_eta_decompose π).
    rewrite -(sliceC_stack_context_decompose π) in hcl0.
    rewrite -(sliceC_stack_context_decompose π) in ho0.
    rewrite -(sliceC_stack_context_decompose π) in r.
    exact (sliceC_red_eta_view Σ cb Γ _ _ _ (sliceC_no_Eta_arg_decompose π hna) hcl0 ho0 r).
  Qed.

  Lemma sliceC_closed_red_zipp Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t u π :
    no_Eta_arg π -> welltypedE Σ Γ (zipc t π) ->
    is_closed_context (Γ ,,, stack_context_eta π) ->
    red Σ (Γ ,,, stack_context π) t u ->
    ∥ Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta t π ⇝ zipp_eta u π ∥.
  Proof.
    intros hna h hcl r.
    destruct (sliceC_closed_red_view Σ wfΣ Γ t π (zipp u π) hna h hcl
                (sliceC_red_zipp _ _ _ _ π r)) as [r'].
    rewrite -zipp_eta_decompose in r'. now constructor.
  Qed.

  (* The discriminant reduction of the Case and Proj views. *)
  Lemma sliceC_reduce_termE_red Σ (wfΣ : abstract_env_ext_rel X Σ) f Γ t h :
    ∥ red Σ Γ t (reduce_termE f Γ t h) ∥.
  Proof.
    destruct (PCUICSafeReduceEta.reduce_term_sound (wt := welltypedE) (wfP := wf_extE)
                (normalization_in := normalization_in) f X_type X Γ t h Σ wfΣ) as [r].
    exact (sq (clrel_rel r)).
  Qed.

  Lemma sliceC_eqb_term_refl Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t :
    welltypedE Σ Γ t -> eqb_term t t.
  Proof.
    intros ht. destruct (heΣ _ wfΣ) as [hwf].
    pose proof (ctf_wf_universes Σ Γ t hwf ht) as hu.
    exact (snd (cmpb_term_correct Σ wfΣ Conv 0 t t hu hu) ltac:(reflexivity)).
  Qed.

  Lemma sliceC_reduce_termE_cored Σ (wfΣ : abstract_env_ext_rel X Σ) f Γ t h :
    eqb_term (reduce_termE f Γ t h) t = false ->
    cored Σ Γ (reduce_termE f Γ t h) t.
  Proof.
    intros hneq.
    destruct (sliceC_reduce_termE_red Σ wfΣ f Γ t h) as [r].
    apply (red_neq_cored Σ Γ t (reduce_termE f Γ t h) r).
    intros e. rewrite -e in hneq.
    pose proof (sliceC_eqb_term_refl Σ wfΣ Γ t (h Σ wfΣ)) as hrefl.
    rewrite hneq in hrefl. discriminate hrefl.
  Qed.

  (* whnf of the η view after [reduce_args_E] (G2b: [eta_head_ok]). *)
  Lemma sliceC_whnf_reduced (Σ : global_env_ext) Γ π fn' args' :
    no_Eta_arg (decompose_stack π).2 -> isApp fn' = false ->
    whnf RedFlags.nodelta Σ (Γ ,,, stack_context (decompose_stack π).2) (mkApps fn' args') ->
    eta_head_ok fn' (decompose_stack π).2 ->
    whnf RedFlags.nodelta Σ (Γ ,,, stack_context_eta (appstack args' (decompose_stack π).2))
      (zipp_eta fn' (appstack args' (decompose_stack π).2)).
  Proof.
    intros hna ha hw hok.
    rewrite stack_context_eta_appstack zipp_eta_appstack_snd eta_rename_mkApps.
    apply whnf_mkApps_eta_virtuals.
    - rewrite -eta_rename_mkApps. exact (eta_rename_whnf _ _ Γ _ _ hna hw).
    - now rewrite eta_rename_isApp.
    - intros k hk. destruct (stack_context_eta_run_vass _ k hk) as [d [hd hb]].
      pose proof (nth_error_Some_length hd) as hlt.
      rewrite (@nth_error_app1 _ _ Γ _ hlt) hd. cbn. now rewrite hb.
    - unfold eta_head_ok in hok. move/orP: hok => [h|h].
      + left. exact (proj1 (Nat.eqb_eq _ _) h).
      + right. rewrite eta_rename_rigid_head. now apply negb_true_iff.
  Qed.

  (* See https://github.com/coq/coq/blob/master/kernel/reduction.ml#L367 *)
  (* T1 (rev 14 B4): every view except [prog_view_other] needs both stacks without Eta_arg; the
     equation [hg] is passed to the helper Equations. On false: the deliberate refusal point. *)
  (* Whether [prog_viewc] answers [prog_view_other] (the T1 refusal branch keeps [t1], [t2]). *)
  Definition prog_view_other_b (t1 t2 : term) : bool :=
    match prog_viewc t1 t2 with prog_view_other _ _ _ => true | _ => false end.

  Lemma sliceC_prog_view_other_discr t1 t2 : prog_view_other_b t1 t2 = true -> prog_discr t1 t2.
  Proof.
    unfold prog_view_other_b. destruct (prog_viewc t1 t2); intros e;
      first [discriminate e | assumption].
  Qed.

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
    | @exist false _ with inspect (prog_view_other_b t1 t2) := {
      | @exist true hother := isconv_fallback leq t1 π1 t2 π2 aux ;
      | @exist false _ := no (EtaStackRefusal (Γ ,,, focus_context π1) t1 (Γ ,,, focus_context π2) t2)
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
            | @exist _ _ := unfold_prims_args Γ leq c u π1 f1 h1 c' u' π2 f2 h2 hx (eq_sym hg) hwf1 hwf2 aux
            }
          } ;
        (* If universes are different, we unfold one of the constants *)
        | @exist false uneq_u := unfold_constants Γ leq c u π1 f1 h1 c' u' π2 f2 h2 _ hx (eq_sym hg) hwf1 hwf2 aux
        } ;
      (* If the two constants are different, we unfold one of them *)
      | right uneq_c := unfold_constants Γ leq c u π1 f1 h1 c' u' π2 f2 h2 _ hx (eq_sym hg) hwf1 hwf2 aux
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
                  with isconv_predicate Γ ci p c brs π1 f1 _ ci' p' c' brs' π2 f2 _ hx (eq_sym hg) hwf1 hwf2 _ aux := {
                | Success convp with isconv_red_raw Conv
                                  c (Case_discr ci p brs :: π1)
                                  c' (Case_discr ci' p' brs' :: π2) aux := {
                  | Success convdiscr with isconv_branches' Γ ci p c brs π1 f1 _ ci' p' c' brs' π2 f2 _ hx (eq_sym hg) hwf1 hwf2 _ _ aux := {
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
          | @exist true eq4 with isws_cumul_pb_Fix IndFix Γ mfix idx π1 f1 _ mfix' idx' π2 f2 _ hx (eq_sym hg) hwf1 hwf2 _ aux := {
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
      | @exist true eq4 with isws_cumul_pb_Fix CoIndFix Γ mfix idx π1 f1 _ mfix' idx' π2 f2 _ hx (eq_sym hg) hwf1 hwf2 _ aux := {
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
                | Success convdiscrdef with isconv_array_values Γ a π1 f1 _ a' π2 f2 _ hx (eq_sym hg) hwf1 hwf2 aux := {
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

  (* The obligations of [_isconv_prog] (slice C). The T1 equation [hg] gives [no_Eta_arg] on
     both stacks in every view but [prog_view_other]; it is read with
     [andb_prop _ _ (eq_sym hg)], never rewritten. The obligations that are arguments of an
     [inspect]ed call ([reduce_termE]'s and [reduce_args_E]'s welltypedness) take [no_Eta_arg]
     from [virt_ok_not_head] on [hv1]/[hv2] instead: an obligation's constant keeps the
     variables its proof uses, so a use of [hg] there makes the inspected equations depend on
     [hg], and [etak_hint] (whose [etak_pre] rewrites [hg]) then stops closing the later
     invariant obligations, which shifts every following [Next Obligation]. *)

  (* tApp *)
  Next Obligation.
    destruct ir1 as [ha1 _]. discriminate ha1.
  Qed.

  (* tConst *)
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb]. destruct (heΣ _ wfΣ) as [hwf].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (h _ wfΣ) as [hargs].
    pose proof (ctf_wf_universes Σ _ _ hwf (ctf_context Σ Γ _ π1 hwf hna1 (h1 Σ wfΣ))) as hu.
    pose proof (ctf_wf_universes Σ _ _ hwf (ctf_context Σ Γ _ π2 hwf hna2 (h2 Σ wfΣ))) as hu'.
    constructor. unfold zipp_eta. rewrite !eta_rename_rename. cbn [rename].
    apply ws_cumul_pbE_mkApps; [|exact hargs].
    apply ws_cumul_pbE_Const; [exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)|].
    symmetry in eq2. exact (eqb_universe_instance_spec u u' Σ wfΣ hu hu' eq2).
  Qed.
  Next Obligation.
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (abstract_env_lookup_correct' X c' wfΣ) as el. rewrite <- el in eq3.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h1 Σ wfΣ)
             (red_context_zip_eta Σ Γ _ _ π1 (red_const Σ eq3))).
  Qed.
  Next Obligation.
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (abstract_env_lookup_correct' X c' wfΣ) as el. rewrite <- el in eq3.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h2 Σ wfΣ)
             (red_context_zip_eta Σ Γ _ _ π2 (red_const Σ eq3))).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    eapply R_cored. intros Σ wfΣ.
    pose proof (eq_trans eq3 (eq_sym (abstract_env_lookup_correct' X c' wfΣ))) as eq3'.
    exact (cored_context_eta Σ Γ _ _ π1 hna1 (cored_const Σ eq3')).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (eq_trans eq3 (eq_sym (abstract_env_lookup_correct' X c' wfΣ))) as eq3'.
    destruct (sliceC_closed_red_zipp Σ wfΣ Γ (tConst c' u) body@[u] π1 hna1 (h1 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1) (red_const Σ eq3')) as [r1].
    destruct (sliceC_closed_red_zipp Σ wfΣ Γ (tConst c' u') body@[u'] π2 hna2 (h2 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π2 hwf2) (red_const Σ eq3')) as [r2].
    destruct (h Σ wfΣ) as [h'], (hx Σ wfΣ) as [hx'].
    constructor.
    eapply WS8_trans; [exact (red_ws_cumul_pbE r1)|].
    eapply WS8_trans; [exact h'|].
    eapply ws_cumul_pbE_ws_cumul_ctx; [exact (ws_cumul_ctx_pbE_sym hx')|].
    exact (red_ws_cumul_pbE_inv r2).
  Qed.
  Next Obligation.
    right. split; [reflexivity|]. intros e. rewrite <- uneq_u in e. discriminate e.
  Qed.

  (* tLambda *)
  Next Obligation.
    eapply R_positionR; [constructor; reflexivity|].
    exact (sliceC_positionR_cons (Lambda_ty na t1) π1 eq_refl).
  Qed.
  Next Obligation.
    eapply R_positionR; [constructor; reflexivity|].
    exact (sliceC_positionR_cons (Lambda_bd na A1) π1 eq_refl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hx Σ wfΣ) as [hx'], (h Σ wfΣ) as [h'].
    symmetry in e; apply eqb_binder_annot_spec in e.
    change (∥ ws_cumul_ctx_pbE Conv Σ ((Γ ,,, stack_context_eta π1) ,, vass na (eta_rename π1 0 A1))
                ((Γ ,,, stack_context_eta π2) ,, vass na' (eta_rename π2 0 A2)) ∥).
    constructor. constructor; [exact hx'|].
    constructor; [exact e|]. exact h'.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf]. destruct (hwf1 Σ wfΣ) as [hl].
    exact (wf_localE_push_real welltypedE_context Σ Γ t1 (Lambda_bd na A1) π1
             eq_refl hna1 (h1 Σ wfΣ) hl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf]. destruct (hwf2 Σ wfΣ) as [hl].
    exact (wf_localE_push_real welltypedE_context Σ Γ t2 (Lambda_bd na' A2) π2
             eq_refl hna2 (h2 Σ wfΣ) hl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    rewrite (sliceC_zipp_eta_rigid _ _ _ ir1 eq_refl) (sliceC_zipp_eta_rigid _ _ _ ir2 eq_refl).
    rewrite !eta_rename_tLambda.
    destruct (h Σ wfΣ) as [hb], (h0 Σ wfΣ) as [hA].
    constructor. apply ws_cumul_pbE_Lambda; [exact (wsE_right hA)|exact hb].
  Qed.

  (* tProd *)
  Next Obligation.
    eapply R_positionR; [constructor; reflexivity|].
    exact (sliceC_positionR_cons (Prod_l na B1) π1 eq_refl).
  Qed.
  Next Obligation.
    eapply R_positionR; [constructor; reflexivity|].
    exact (sliceC_positionR_cons (Prod_r na A1) π1 eq_refl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hx Σ wfΣ) as [hx'], (h Σ wfΣ) as [h'].
    symmetry in e; apply eqb_binder_annot_spec in e.
    change (∥ ws_cumul_ctx_pbE Conv Σ ((Γ ,,, stack_context_eta π1) ,, vass na (eta_rename π1 0 A1))
                ((Γ ,,, stack_context_eta π2) ,, vass na' (eta_rename π2 0 A2)) ∥).
    constructor. constructor; [exact hx'|].
    constructor; [exact e|]. exact h'.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf]. destruct (hwf1 Σ wfΣ) as [hl].
    exact (wf_localE_push_real welltypedE_context Σ Γ B1 (Prod_r na A1) π1
             eq_refl hna1 (h1 Σ wfΣ) hl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf]. destruct (hwf2 Σ wfΣ) as [hl].
    exact (wf_localE_push_real welltypedE_context Σ Γ B2 (Prod_r na' A2) π2
             eq_refl hna2 (h2 Σ wfΣ) hl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    rewrite (sliceC_zipp_eta_rigid _ _ _ ir1 eq_refl) (sliceC_zipp_eta_rigid _ _ _ ir2 eq_refl).
    rewrite !eta_rename_tProd.
    symmetry in e; apply eqb_binder_annot_spec in e.
    destruct (h Σ wfΣ) as [hB], (h0 Σ wfΣ) as [hA].
    constructor. apply ws_cumul_pbE_Prod; [exact e|exact hA|exact hB].
  Qed.

  (* tCase *)
  Next Obligation.
    rename H into wfΣ.
    pose proof (virt_ok_not_head _ _ hv1 eq_refl) as hna1.
    destruct (heΣ _ wfΣ) as [hwf].
    exact (ctf_context Σ Γ c (Case_discr ci p brs :: π1) hwf hna1 (h1 Σ wfΣ)).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    pose proof (virt_ok_not_head _ _ hv2 eq_refl) as hna2.
    destruct (heΣ _ wfΣ) as [hwf].
    exact (ctf_context Σ Γ c' (Case_discr ci' p' brs' :: π2) hwf hna2 (h2 Σ wfΣ)).
  Qed.
  Next Obligation.
    exact (eqb_eq _ _ (eq_sym eq5)).
  Qed.
  Next Obligation.
    eapply R_positionR; [constructor; reflexivity|].
    exact (sliceC_positionR_cons (Case_discr ci p brs) π1 eq_refl).
  Qed.
  Next Obligation.
    exact (eqb_eq _ _ (eq_sym eq5)).
  Qed.
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (eqb_eq _ _ (eq_sym eq5)) as eci. subst ci'.
    destruct (convp Σ wfΣ) as [[hpars hu hctx hret]].
    destruct (convdiscr Σ wfΣ) as [hc].
    destruct (convbrs Σ wfΣ) as [hbrs].
    destruct (convargs Σ wfΣ) as [hargs].
    destruct (hx Σ wfΣ) as [hx'].
    pose proof (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1) as hcl1.
    pose proof (sliceC_closed_ctx Σ wfΣ Γ π2 hwf2) as hcl2.
    pose proof (sliceC_open_head Σ wfΣ Γ _ π1 hna1 (h1 Σ wfΣ) hcl1) as ho1.
    pose proof (sliceC_open_ctx_len _ _ _ (All2_fold_length hx')
                  (sliceC_open_head Σ wfΣ Γ _ π2 hna2 (h2 Σ wfΣ) hcl2)) as ho2.
    rewrite eta_rename_tCase in ho1. rewrite eta_rename_tCase in ho2.
    constructor. unfold zipp_eta.
    apply ws_cumul_pbE_mkApps; [|exact hargs].
    rewrite !eta_rename_tCase.
    eapply ws_cumul_pbE_Case; [exact ho1|exact ho2|exact hpars|exact hu|exact hctx|exact hret|exact hc|].
    apply (All2_map (f := eta_rename_br π1) (g := eta_rename_br π2)). exact hbrs.
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf].
    match goal with
    | |- context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h2 Σ wfΣ)
             (red_context_zip_eta Σ Γ _ _ (Case_discr ci' p' brs' :: π2) r)).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    eapply R_cored2; [constructor; reflexivity|reflexivity|].
    intros Σ wfΣ.
    match type of eq4 with
    | false = eqb_term (reduce_termE ?f ?Γ' ?t ?hh) _ =>
        pose proof (sliceC_reduce_termE_cored Σ wfΣ f Γ' t hh (eq_sym eq4)) as hc
    end.
    exact (cored_context_eta Σ Γ _ _ (Case_discr ci' p' brs' :: π2) hna2 hc).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (h Σ wfΣ) as [h'], (hx Σ wfΣ) as [hx'].
    match type of h' with
    | context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    destruct (sliceC_closed_red_zipp Σ wfΣ Γ (tCase ci' p' c' brs') _ π2 hna2 (h2 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π2 hwf2) (red_case_c ci' p' c' brs' _ r)) as [r2].
    constructor. eapply WS8_trans; [exact h'|].
    eapply ws_cumul_pbE_ws_cumul_ctx; [exact (ws_cumul_ctx_pbE_sym hx')|].
    exact (red_ws_cumul_pbE_inv r2).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf].
    match goal with
    | |- context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h1 Σ wfΣ)
             (red_context_zip_eta Σ Γ _ _ (Case_discr ci p brs :: π1) r)).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    eapply R_cored. intros Σ wfΣ.
    match type of eq3 with
    | false = eqb_term (reduce_termE ?f ?Γ' ?t ?hh) _ =>
        pose proof (sliceC_reduce_termE_cored Σ wfΣ f Γ' t hh (eq_sym eq3)) as hc
    end.
    exact (cored_context_eta Σ Γ _ _ (Case_discr ci p brs :: π1) hna1 hc).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (h Σ wfΣ) as [h'].
    match type of h' with
    | context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    destruct (sliceC_closed_red_zipp Σ wfΣ Γ (tCase ci p c brs) _ π1 hna1 (h1 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1) (red_case_c ci p c brs _ r)) as [r1].
    constructor. eapply WS8_trans; [exact (red_ws_cumul_pbE r1)|exact h'].
  Qed.

  (* tProj *)
  Next Obligation.
    rename H into wfΣ.
    pose proof (virt_ok_not_head _ _ hv1 eq_refl) as hna1.
    destruct (heΣ _ wfΣ) as [hwf].
    exact (ctf_context Σ Γ c (Proj p :: π1) hwf hna1 (h1 Σ wfΣ)).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    pose proof (virt_ok_not_head _ _ hv2 eq_refl) as hna2.
    destruct (heΣ _ wfΣ) as [hwf].
    exact (ctf_context Σ Γ c' (Proj p' :: π2) hwf hna2 (h2 Σ wfΣ)).
  Qed.
  Next Obligation.
    eapply R_positionR; [constructor; reflexivity|].
    exact (sliceC_positionR_cons (Proj p) π1 eq_refl).
  Qed.
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    pose proof (eqb_eq _ _ (eq_sym eq5)) as ep. subst p'.
    destruct (convdiscr Σ wfΣ) as [hc], (h Σ wfΣ) as [hargs].
    constructor. unfold zipp_eta.
    apply ws_cumul_pbE_mkApps; [|exact hargs].
    rewrite !sliceC_eta_rename_tProj.
    apply ws_cumul_pbE_Proj_c. exact hc.
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf].
    match goal with
    | |- context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h2 Σ wfΣ)
             (red_context_zip_eta Σ Γ _ _ (Proj p' :: π2) r)).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    eapply R_cored2; [constructor; reflexivity|reflexivity|].
    intros Σ wfΣ.
    match type of eq4 with
    | false = eqb_term (reduce_termE ?f ?Γ' ?t ?hh) _ =>
        pose proof (sliceC_reduce_termE_cored Σ wfΣ f Γ' t hh (eq_sym eq4)) as hc
    end.
    exact (cored_context_eta Σ Γ _ _ (Proj p' :: π2) hna2 hc).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (h Σ wfΣ) as [h'], (hx Σ wfΣ) as [hx'].
    match type of h' with
    | context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    destruct (sliceC_closed_red_zipp Σ wfΣ Γ (tProj p' c') _ π2 hna2 (h2 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π2 hwf2) (red_proj_c p' c' _ r)) as [r2].
    constructor. eapply WS8_trans; [exact h'|].
    eapply ws_cumul_pbE_ws_cumul_ctx; [exact (ws_cumul_ctx_pbE_sym hx')|].
    exact (red_ws_cumul_pbE_inv r2).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf].
    match goal with
    | |- context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h1 Σ wfΣ)
             (red_context_zip_eta Σ Γ _ _ (Proj p :: π1) r)).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    eapply R_cored. intros Σ wfΣ.
    match type of eq3 with
    | false = eqb_term (reduce_termE ?f ?Γ' ?t ?hh) _ =>
        pose proof (sliceC_reduce_termE_cored Σ wfΣ f Γ' t hh (eq_sym eq3)) as hc
    end.
    exact (cored_context_eta Σ Γ _ _ (Proj p :: π1) hna1 hc).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (h Σ wfΣ) as [h'].
    match type of h' with
    | context [reduce_termE ?f ?Γ' ?t ?hh] => destruct (sliceC_reduce_termE_red Σ wfΣ f Γ' t hh) as [r]
    end.
    destruct (sliceC_closed_red_zipp Σ wfΣ Γ (tProj p c) _ π1 hna1 (h1 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1) (red_proj_c p c _ r)) as [r1].
    constructor. eapply WS8_trans; [exact (red_ws_cumul_pbE r1)|exact h'].
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

  (* tFix: unfolding on side 1. [θ'] is side 1's stack tail (unfold_one_fix_decompose). *)
  Next Obligation.
    rename H into wfΣ.
    pose proof (virt_ok_not_head _ _ hv1 eq_refl) as hna1.
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    destruct (unfold_one_fix_red _ _ _ _ _ _ _ eq1 Σ wfΣ) as [rf].
    pose proof (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h1 Σ wfΣ) rf) as hw.
    rewrite eθ zipc_appstack in hw.
    change (PCUICPosition.zip (fn, PCUICPosition.appstack l' []))
      with (PCUICPosition.zipc fn (PCUICPosition.appstack l' [])).
    rewrite PCUICPosition.zipc_appstack.
    exact (ctf_context Σ Γ _ _ hwf (sliceC_no_Eta_arg_decompose π1 hna1) hw).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    destruct (unfold_one_fix_red _ _ _ _ _ _ _ eq1 Σ wfΣ) as [rf].
    pose proof (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h1 Σ wfΣ) rf) as hw.
    rewrite eθ zipc_appstack in hw.
    reduce_args_facts Σ wfΣ.
    rewrite zipc_appstack.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf hw
             (red_context_zip_eta Σ Γ _ _ _ (clrel_rel r))).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    eapply R_cored. intros Σ wfΣ.
    change (cored Σ Γ (zipc fn' (appstack args' (decompose_stack π1).2)) (zipc (tFix mfix idx) π1)).
    pose proof (unfold_one_fix_cored _ _ _ _ _ _ _ eq1 Σ wfΣ) as hc.
    rewrite eθ zipc_appstack in hc.
    reduce_args_facts Σ wfΣ.
    rewrite zipc_appstack.
    exact (red_cored_cored Σ Γ _ _ _ (red_context_zip_eta Σ Γ _ _ _ (clrel_rel r)) hc).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    rewrite stack_context_eta_appstack sliceC_stack_context_eta_decompose.
    exact (hx Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    exact (virt_ok_reduce _ _ _ _ hv1 (or_introl hna1)).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    rewrite stack_context_eta_appstack sliceC_stack_context_eta_decompose.
    exact (hwf1 Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (eq_sym g3) as g3'. unfold rebuilt_ok in g3'. apply andb_prop in g3' as [_ hok].
    match type of eq3 with
    | (_, _) = reduce_args_E ?f ?XT ?XX ?Γ' ?t ?args ?hh =>
        pose proof (reduce_args_E_isred f XT XX Γ' t args hh eq_refl) as [ha _]
    end.
    rewrite <- eq3 in ha. cbn [fst] in ha.
    split; [exact ha|].
    intros Σ wfΣ. reduce_args_facts Σ wfΣ.
    constructor.
    exact (sliceC_whnf_reduced Σ Γ π1 fn' args' (sliceC_no_Eta_arg_decompose π1 hna1) ha w hok).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    destruct (unfold_one_fix_red_zipp _ _ _ _ _ _ _ eq1 Σ wfΣ) as [rf].
    rewrite eθ sliceC_zipp_appstack_snd in rf.
    reduce_args_facts Σ wfΣ.
    rewrite sliceC_stack_context_decompose in r.
    assert (r12 : red Σ (Γ ,,, stack_context π1) (zipp (tFix mfix idx) π1) (mkApps fn' args'))
      by (etransitivity; [exact rf|exact (clrel_rel r)]).
    destruct (sliceC_closed_red_view Σ wfΣ Γ (tFix mfix idx) π1 (mkApps fn' args') hna1 (h1 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1) r12) as [rv].
    destruct (h Σ wfΣ) as [h'].
    rewrite stack_context_eta_appstack sliceC_stack_context_eta_decompose zipp_eta_appstack_snd in h'.
    constructor. eapply WS8_trans; [exact (red_ws_cumul_pbE rv)|exact h'].
  Qed.
  (* tFix: unfolding on side 2. *)
  Next Obligation.
    rename H into wfΣ.
    pose proof (virt_ok_not_head _ _ hv2 eq_refl) as hna2.
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    destruct (unfold_one_fix_red _ _ _ _ _ _ _ eq1 Σ wfΣ) as [rf].
    pose proof (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h2 Σ wfΣ) rf) as hw.
    rewrite eθ zipc_appstack in hw.
    change (PCUICPosition.zip (fn, PCUICPosition.appstack l' []))
      with (PCUICPosition.zipc fn (PCUICPosition.appstack l' [])).
    rewrite PCUICPosition.zipc_appstack.
    exact (ctf_context Σ Γ _ _ hwf (sliceC_no_Eta_arg_decompose π2 hna2) hw).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    destruct (heΣ _ wfΣ) as [hwf].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    destruct (unfold_one_fix_red _ _ _ _ _ _ _ eq1 Σ wfΣ) as [rf].
    pose proof (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf (h2 Σ wfΣ) rf) as hw.
    rewrite eθ zipc_appstack in hw.
    reduce_args_facts Σ wfΣ.
    rewrite zipc_appstack.
    exact (PCUICSafeReduceEta.red_wt (wt := welltypedE) Σ hwf hw
             (red_context_zip_eta Σ Γ _ _ _ (clrel_rel r))).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    eapply R_cored2; [constructor; reflexivity|reflexivity|].
    intros Σ wfΣ.
    change (cored Σ Γ (zipc fn' (appstack args' (decompose_stack π2).2)) (zipc (tFix mfix' idx') π2)).
    pose proof (unfold_one_fix_cored _ _ _ _ _ _ _ eq1 Σ wfΣ) as hc.
    rewrite eθ zipc_appstack in hc.
    reduce_args_facts Σ wfΣ.
    rewrite zipc_appstack.
    exact (red_cored_cored Σ Γ _ _ _ (red_context_zip_eta Σ Γ _ _ _ (clrel_rel r)) hc).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    rewrite stack_context_eta_appstack sliceC_stack_context_eta_decompose.
    exact (hx Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    exact (virt_ok_reduce _ _ _ _ hv2 (or_introl hna2)).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    rewrite stack_context_eta_appstack sliceC_stack_context_eta_decompose.
    exact (hwf2 Σ wfΣ).
  Qed.
  Next Obligation.
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (eq_sym g3) as g3'. unfold rebuilt_ok in g3'. apply andb_prop in g3' as [_ hok].
    match type of eq3 with
    | (_, _) = reduce_args_E ?f ?XT ?XX ?Γ' ?t ?args ?hh =>
        pose proof (reduce_args_E_isred f XT XX Γ' t args hh eq_refl) as [ha _]
    end.
    rewrite <- eq3 in ha. cbn [fst] in ha.
    split; [exact ha|].
    intros Σ wfΣ. reduce_args_facts Σ wfΣ.
    constructor.
    exact (sliceC_whnf_reduced Σ Γ π2 fn' args' (sliceC_no_Eta_arg_decompose π2 hna2) ha w hok).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    pose proof (unfold_one_fix_decompose _ _ _ _ _ _ _ eq1) as d1.
    rewrite <- eq2 in d1. cbn [snd] in d1. subst θ'.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as eθ.
    destruct (unfold_one_fix_red_zipp _ _ _ _ _ _ _ eq1 Σ wfΣ) as [rf].
    rewrite eθ sliceC_zipp_appstack_snd in rf.
    reduce_args_facts Σ wfΣ.
    rewrite sliceC_stack_context_decompose in r.
    assert (r12 : red Σ (Γ ,,, stack_context π2) (zipp (tFix mfix' idx') π2) (mkApps fn' args'))
      by (etransitivity; [exact rf|exact (clrel_rel r)]).
    destruct (sliceC_closed_red_view Σ wfΣ Γ (tFix mfix' idx') π2 (mkApps fn' args') hna2 (h2 Σ wfΣ)
                (sliceC_closed_ctx Σ wfΣ Γ π2 hwf2) r12) as [rv].
    destruct (h Σ wfΣ) as [h'], (hx Σ wfΣ) as [hx'].
    rewrite zipp_eta_appstack_snd in h'.
    constructor. eapply WS8_trans; [exact h'|].
    eapply ws_cumul_pbE_ws_cumul_ctx; [exact (ws_cumul_ctx_pbE_sym hx')|].
    exact (red_ws_cumul_pbE_inv rv).
  Qed.
  (* tFix: no unfolding; the fixpoints are compared. *)
  Next Obligation.
    exact (eqb_eq _ _ (eq_sym eq4)).
  Qed.
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    pose proof (eqb_eq _ _ (eq_sym eq4)) as ei. subst idx'.
    destruct convfix as [hfix].
    destruct (convargs Σ wfΣ) as [hargs].
    constructor. unfold zipp_eta.
    apply ws_cumul_pbE_mkApps; [|exact hargs].
    rewrite !eta_rename_tFix.
    apply ws_cumul_pbE_Fix; [exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)|].
    unfold ws_mfix_rel. rewrite sliceC_fix_context_eta_rename.
    apply All2_map. eapply All2_impl; [exact hfix|].
    intros d d' [hty [hbo [hra hnb]]].
    split; [exact (hty Σ wfΣ)|]. split; [exact (hbo Σ wfΣ)|]. split; assumption.
  Qed.

  (* tCoFix *)
  Next Obligation.
    exact (eqb_eq _ _ (eq_sym eq4)).
  Qed.
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    pose proof (eqb_eq _ _ (eq_sym eq4)) as ei. subst idx'.
    destruct convfix as [hfix].
    destruct (convargs Σ wfΣ) as [hargs].
    constructor. unfold zipp_eta.
    apply ws_cumul_pbE_mkApps; [|exact hargs].
    rewrite !eta_rename_tCoFix.
    apply ws_cumul_pbE_CoFix; [exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)|].
    unfold ws_mfix_rel. rewrite sliceC_fix_context_eta_rename.
    apply All2_map. eapply All2_impl; [exact hfix|].
    intros d d' [hty [hbo [hra hnb]]].
    split; [exact (hty Σ wfΣ)|]. split; [exact (hbo Σ wfΣ)|]. split; assumption.
  Qed.

  (* Primitive values *)
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    pose proof (eqb_eq _ _ (eq_sym eqi)) as ei. subst i'.
    rewrite (sliceC_zipp_eta_rigid _ _ _ ir1 eq_refl) (sliceC_zipp_eta_rigid _ _ _ ir2 eq_refl).
    rewrite !eta_rename_rename. cbn.
    constructor. apply ws_cumul_pbE_refl; [exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)|reflexivity].
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    pose proof (eqb_eq _ _ (eq_sym eqf)) as ef. subst f'.
    rewrite (sliceC_zipp_eta_rigid _ _ _ ir1 eq_refl) (sliceC_zipp_eta_rigid _ _ _ ir2 eq_refl).
    rewrite !eta_rename_rename. cbn.
    constructor. apply ws_cumul_pbE_refl; [exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)|reflexivity].
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    pose proof (eqb_eq _ _ (eq_sym eqf)) as ef. subst f'.
    rewrite (sliceC_zipp_eta_rigid _ _ _ ir1 eq_refl) (sliceC_zipp_eta_rigid _ _ _ ir2 eq_refl).
    rewrite !eta_rename_rename. cbn.
    constructor. apply ws_cumul_pbE_refl; [exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)|reflexivity].
  Qed.

  (* Primitive arrays *)
  Next Obligation.
    destruct a. exact (h1 Σ wfΣ).
  Qed.
  Next Obligation.
    destruct a'. exact (h2 Σ wfΣ).
  Qed.
  Next Obligation.
    eapply R_positionR; [constructor; destruct a; reflexivity|].
    exact (sliceC_positionR_cons (PrimArray_ty (array_level a) (array_value a) (array_default a)) π1 eq_refl).
  Qed.
  Next Obligation.
    destruct a. exact (h1 Σ wfΣ).
  Qed.
  Next Obligation.
    destruct a'. exact (h2 Σ wfΣ).
  Qed.
  Next Obligation.
    eapply R_positionR; [constructor; destruct a; reflexivity|].
    exact (sliceC_positionR_cons (PrimArray_def (array_level a) (array_value a) (array_type a)) π1 eq_refl).
  Qed.
  Next Obligation.
    rename H into wfΣ.
    destruct (hΣ _ wfΣ) as [cb]. destruct (heΣ _ wfΣ) as [hwf].
    destruct (andb_prop _ _ (eq_sym hg)) as [hna1 hna2].
    assert (hl1 : wf_universe Σ (Universe.make' (array_level a))).
    { pose proof (ctf_wf_universes Σ _ _ hwf (ctf_context Σ Γ _ π1 hwf hna1 (h1 Σ wfΣ))) as hu.
      cbn -[wf_universeb] in hu. move/andP: hu => [/andP [/andP [hu _] _] _].
      now apply wf_universe_iff. }
    assert (hl2 : wf_universe Σ (Universe.make' (array_level a'))).
    { pose proof (ctf_wf_universes Σ _ _ hwf (ctf_context Σ Γ _ π2 hwf hna2 (h2 Σ wfΣ))) as hu.
      cbn -[wf_universeb] in hu. move/andP: hu => [/andP [/andP [hu _] _] _].
      now apply wf_universe_iff. }
    rewrite (sliceC_zipp_eta_rigid _ _ _ ir1 eq_refl) (sliceC_zipp_eta_rigid _ _ _ ir2 eq_refl).
    rewrite !sliceC_eta_rename_tPrimArray.
    destruct (convdiscrty Σ wfΣ) as [hty], (convdiscrdef Σ wfΣ) as [hdef],
      (convdiscrval Σ wfΣ) as [hval].
    constructor. apply ws_cumul_pbE_Prim; [|exact (sliceC_closed_ctx Σ wfΣ Γ π1 hwf1)].
    apply onPrimsArray.
    - apply (abstract_env_compare_universe_correct X wfΣ Conv _ _ hl1 hl2).
      symmetry in eql. exact eql.
    - exact hdef.
    - exact hty.
    - exact hval.
  Qed.

  (* Fallback *)
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    eapply R_stateR; constructor; reflexivity.
  Qed.
  Next Obligation.
    exact (sliceC_prog_view_other_discr t1 t2 (eq_sym hother)).
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

  (* ---- Slice D helpers (EtaConv): views of the frames the argument machinery pushes, the
     virtual tail, and the invariant tactics of slice D's obligations. ---- *)
  Lemma zipp_eta_App_r u x π : zipp_eta u (App_r x :: π) = eta_rename π 0 u.
  Proof using All. reflexivity. Qed.

  Lemma stack_context_eta_App_r x π : stack_context_eta (App_r x :: π) = stack_context_eta π.
  Proof using All. reflexivity. Qed.

  Lemma zipp_eta_Eta_arg_nil t u π : zipp_eta t (Eta_arg u [] :: π) = t.
  Proof using All. reflexivity. Qed.

  Lemma zipc_App_r_mkApps t args u l θ :
    zipc u (App_r (mkApps t args) :: appstack l θ) = zipc t (appstack (args ++ u :: l) θ).
  Proof using All. cbn [zipc fill_hole]. rewrite !zipc_appstack mkApps_app. reflexivity. Qed.

  Lemma zipc_tApp_mkApps t args u l θ :
    zipc (tApp (mkApps t args) u) (appstack l θ) = zipc t (appstack (args ++ u :: l) θ).
  Proof using All. rewrite !zipc_appstack mkApps_app. reflexivity. Qed.

  Lemma decompose_stack_nostack θ : isStackApp θ = false -> decompose_stack θ = ([], θ).
  Proof using All. destruct θ as [|[] θ]; cbn; first [reflexivity | discriminate]. Qed.

  Lemma nth_error_skipn_cons {A} (l : list A) j x :
    nth_error l j = Some x -> skipn j l = x :: skipn (S j) l.
  Proof using All.
    induction l as [|a l IH] in j |- *; destruct j as [|j]; cbn; intros h; try discriminate h.
    - now injection h as ->.
    - now apply IH.
  Qed.

  Lemma eta_virtuals_cons m : eta_virtuals (S m) = tRel m :: eta_virtuals m.
  Proof using All. unfold eta_virtuals. rewrite seq_S rev_app_distr. reflexivity. Qed.

  Lemma skipn_eta_virtuals j m : skipn j (eta_virtuals m) = eta_virtuals (m - j).
  Proof using All.
    induction j as [|j IH] in m |- *; [now rewrite Nat.sub_0_r|].
    destruct m as [|m]; [reflexivity|].
    rewrite eta_virtuals_cons. exact (IH m).
  Qed.

  Lemma skipn_eta_virtuals_focus j m : j < m ->
    skipn j (eta_virtuals m) = virtual_focus m j :: skipn (S j) (eta_virtuals m).
  Proof using All. intros h. apply nth_error_skipn_cons, virtual_focus_nth, h. Qed.

  Lemma eta_virtuals_open Γ π m : m <= eta_run π ->
    forallb (is_open_term (Γ ,,, stack_context_eta π)) (eta_virtuals m).
  Proof using All.
    induction m as [|m IH]; [reflexivity|]. intros hm.
    rewrite eta_virtuals_cons. cbn [forallb]. rewrite (IH ltac:(lia)) andb_true_r.
    destruct (stack_context_eta_run_vass π m ltac:(lia)) as [decl [hn _]].
    cbn [on_free_vars]. rewrite /shiftnP. apply/orP; left. apply/Nat.ltb_lt.
    rewrite app_context_length. have := nth_error_Some_length hn. lia.
  Qed.

  Lemma zip_appstack_nil_base t args :
    PCUICPosition.zip (t, PCUICPosition.appstack args []) = mkApps t args.
  Proof using All.
    unfold PCUICPosition.zip. cbn [fst snd]. rewrite PCUICPosition.zipc_appstack. reflexivity.
  Qed.

  Lemma decompose_stack_noStackApp_eta π l ρ : decompose_stack π = (l, ρ) -> isStackApp ρ = false.
  Proof using All.
    induction π as [|[] π IH] in l, ρ |- *; cbn; intros e; try (now inversion e).
    destruct (decompose_stack π) as [l' ρ'] eqn:e'. inversion e; subst. now apply (IH l').
  Qed.

  Lemma stack_context_eta_decompose π : stack_context_eta π = stack_context_eta (decompose_stack π).2.
  Proof using All.
    destruct (decompose_stack π) as [l ρ] eqn:e. cbn [snd].
    rewrite (decompose_stack_eq _ _ _ e). apply stack_context_eta_appstack.
  Qed.

  Lemma ws_cumul_ctx_pbE_length pb Σ Δ Δ' : ws_cumul_ctx_pbE pb Σ Δ Δ' -> #|Δ| = #|Δ'|.
  Proof using All. induction 1; cbn; congruence. Qed.

  Lemma zipp_eta_Lambda_bd b na A π : zipp_eta b (Lambda_bd na A :: π) = eta_rename π 1 b.
  Proof using All. reflexivity. Qed.

  Lemma eta_lambda_open Γ na A b π :
    is_open_term (Γ ,,, stack_context_eta π) (zipp_eta (tLambda na A b) π) ->
    is_open_term (Γ ,,, stack_context_eta π) (eta_rename π 0 A).
  Proof using All.
    unfold zipp_eta. rewrite on_free_vars_mkApps. move/andP => [h _].
    rewrite eta_rename_tLambda in h. cbn [on_free_vars] in h. now move/andP: h => [? _].
  Qed.

  (* The η view of a λ whose state is a whnf (isred_full): no spine, no pending η run. *)
  Lemma zipp_eta_lambda_whnf Γ na A b π :
    isred_full Γ (tLambda na A b) π ->
    zipp_eta (tLambda na A b) π = tLambda na (eta_rename π 0 A) (eta_rename π 1 b).
  Proof using All.
    intros [_ ir]. destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (ir Σ wfΣ) as [ir'].
    destruct (whnf_zipp_eta_rigid _ _ _ _ ir' eq_refl) as [hargs hrun].
    unfold zipp_eta, decompose_stack_eta. destruct (decompose_stack π) as [l ρ] eqn:dπ.
    rewrite ?dπ in hargs hrun. cbn in hargs, hrun |- *. subst l. rewrite hrun. cbn.
    apply eta_rename_tLambda.
  Qed.

  (* A rebuilt state after reduce_args_E stays well typed (T1 through wt_red). *)
  Lemma rebuilt_wt Σ (wfΣ : abstract_env_ext_rel X Σ) Γ fn l θ fn' l' :
    welltypedE Σ Γ (zipc fn (appstack l θ)) ->
    red Σ (Γ ,,, stack_context θ) (mkApps fn l) (mkApps fn' l') ->
    welltypedE Σ Γ (zipc fn' (appstack l' θ)).
  Proof using All.
    intros hw r. destruct (heΣ _ wfΣ) as [hΣe]. rewrite zipc_appstack in hw. rewrite zipc_appstack.
    eapply (wt_red (wt := welltypedE) (wfP := wf_extE)); [exact hΣe|exact hw|].
    now apply red_context_zip_eta.
  Qed.

  (* The Term state's premise after a G2/G2b-checked rebuild (plan rev 14 B4 G2, G2b). *)
  Lemma isred_full_rebuilt Γ θ t' l' :
    no_Eta_arg θ = true -> isStackApp θ = false -> eta_head_ok t' θ = true -> isApp t' = false ->
    (forall Σ, abstract_env_ext_rel X Σ ->
       ∥ whnf RedFlags.nodelta Σ (Γ ,,, stack_context θ) (mkApps t' l') ∥) ->
    isred_full Γ t' (appstack l' θ).
  Proof using All.
    intros hna hθ hok hap hw. split; [exact hap|]. intros Σ wfΣ. destruct (hw Σ wfΣ) as [w].
    have e := zipp_eta_appstack_snd t' l' θ.
    rewrite (decompose_stack_nostack θ hθ) in e. cbn [snd] in e.
    rewrite e stack_context_eta_appstack. constructor.
    apply eta_rename_whnf in w; [|exact hna]. rewrite eta_rename_mkApps in w. rewrite eta_rename_mkApps.
    apply whnf_mkApps_eta_virtuals; [exact w | now rewrite eta_rename_isApp | | ].
    - intros k hk. destruct (stack_context_eta_run_vass θ k hk) as [decl [hn hb]].
      have hlt := nth_error_Some_length hn.
      rewrite /app_context nth_error_app1 //. rewrite hn /= hb. reflexivity.
    - unfold eta_head_ok in hok. apply orb_prop in hok as [h0|h0].
      + left. now apply Nat.eqb_eq.
      + right. rewrite eta_rename_rigid_head. now apply negb_true_iff.
  Qed.

  Ltac etakD_pre := intros; cbn beta in *; try unfold rebuilt_ok in *;
    repeat match goal with
    | H : true = _ |- _ => symmetry in H
    | H : (_ && _) = true |- _ => apply andb_prop in H as [? ?]
    | H : is_true (_ && _) |- _ => apply andb_prop in H as [? ?]
    end; try subst.
  Ltac etakD_noeta := etakD_pre; try unfold virt_ok;
    cbn [wf_stack is_eta_frame no_Eta_arg is_Eta_arg negb andb orb];
    rewrite ?no_Eta_arg_appstack;
    repeat match goal with H : no_Eta_arg ?π = true |- context [no_Eta_arg ?π] => rewrite H end;
    first [reflexivity | assumption].
  Ltac etakD_wf := match goal with w : abstract_env_ext_rel X ?Σ |- _ => specialize_Σ w end.
  Ltac etakD_ctx := unfold PCUICSafeConversionEtaK4.conv_stack_ctx_eta in *;
    rewrite ?stack_context_eta_App_r ?stack_context_eta_Eta_arg_appstack ?stack_context_eta_appstack in *.

  Ltac etakD_args_red_at Σ w := match goal with
    | e : (?a, ?b) = reduce_args_E ?f ?XT ?X' ?Γ' ?t ?args ?hh |- _ =>
      let rr := fresh "rr" in pose proof (reduce_args_E_sound f XT X' Σ w Γ' t args hh) as [rr];
      rewrite <- e in rr; cbn [fst snd] in rr
    end.
  Ltac etakD_args_red := match goal with w : abstract_env_ext_rel X ?Σ |- _ => etakD_args_red_at Σ w end.
  Ltac etakD_args_whnf := match goal with
    | e : (?a, ?b) = reduce_args_E ?f ?XT ?X' ?Γ' ?t ?args ?hh, w : abstract_env_ext_rel X ?Σ |- _ =>
      let ww := fresh "ww" in pose proof (reduce_args_E_whnf f XT X' Σ w Γ' t args hh) as [ww];
      rewrite <- e in ww; cbn [fst snd] in ww
    end.
  Ltac etakD_args_isr := match goal with
    | e : (?a, ?b) = reduce_args_E ?f ?XT ?X' ?Γ' ?t ?args ?hh |- _ =>
      let ii := fresh "ii" in pose proof (reduce_args_E_isred f XT X' Γ' t args hh) as ii;
      rewrite <- e in ii; cbn [fst snd] in ii
    end.
  Ltac etakD_sce :=
    rewrite ?stack_context_eta_Eta_arg_appstack ?stack_context_eta_App_r ?stack_context_eta_appstack.
  Ltac etakD_ctx_solve := etakD_pre; etakD_sce;
    match goal with w : abstract_env_ext_rel X _, h : PCUICSafeConversionEtaK4.conv_stack_ctx_eta _ _ _ _ |- _ =>
      exact (h _ w) end.
  Ltac etakD_hwf_solve := etakD_pre; etakD_sce;
    match goal with w : abstract_env_ext_rel X _, h : forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ _ ∥ |- _ =>
      exact (h _ w) end.
  Ltac etak_hint_extra ::= solve [ etakD_noeta ].
  Ltac etakD_wtp_solve := etakD_pre; rewrite ?zipc_tApp_mkApps ?zipc_App_r_mkApps;
    match goal with w : abstract_env_ext_rel X _ |- _ => eauto end.
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
  Next Obligation.
    etakD_pre; etakD_wf; destruct hwf1 as [hwf1]; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; destruct (hΣ _ ltac:(eassumption)) as [cb]; apply Nat.eqb_eq in eqm; rewrite !skipn_eta_virtuals -eqm; constructor; apply WT_refl; [ exact (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) hwf1) | apply eta_virtuals_open; lia ].
  Qed.

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
  Next Obligation.
    try clear _isconv_args_vl; etakD_wtp_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vl; etakD_pre; eapply K4_virtual_descent_frame_left.
  Defined.
  Next Obligation.
    try clear _isconv_args_vl; etakD_ctx_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vl; etakD_pre; unfold virt_ok, virtual_focus; cbn [no_Eta_arg is_Eta_arg negb andb orb decompose_stack drop_eta_run is_nil]; rewrite decompose_stack_appstack (decompose_stack_nostack _ hθ1); cbn [snd fst]; apply Nat.ltb_lt; apply Nat.ltb_lt in hj; lia.
  Defined.
  Next Obligation.
    try clear _isconv_args_vl; etakD_hwf_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vl; etakD_hwf_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vl; etakD_pre; etakD_wf; destruct H1 as [H1]; destruct H2 as [H2]; rewrite ?zipp_eta_Eta_arg_nil ?zipp_eta_App_r ?stack_context_eta_Eta_arg_appstack ?stack_context_eta_appstack ?eta_rename_appstack in H1; rewrite (skipn_eta_virtuals_focus _ _ (proj1 (Nat.ltb_lt _ _) hj)); cbn [map app] in H2 |- *; constructor; constructor; assumption.
  Defined.

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
  Next Obligation.
    try clear _isconv_args_vr; etakD_wtp_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vr; etakD_pre; eapply K4_virtual_descent_frame_right.
  Defined.
  Next Obligation.
    try clear _isconv_args_vr; etakD_ctx_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vr; etakD_pre; unfold virt_ok, virtual_focus; cbn [no_Eta_arg is_Eta_arg negb andb orb decompose_stack drop_eta_run is_nil]; rewrite decompose_stack_appstack (decompose_stack_nostack _ hθ2); cbn [snd fst]; apply Nat.ltb_lt; apply Nat.ltb_lt in hj; lia.
  Defined.
  Next Obligation.
    try clear _isconv_args_vr; etakD_hwf_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vr; etakD_hwf_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args_vr; etakD_pre; etakD_wf; destruct H1 as [H1]; destruct H2 as [H2]; rewrite ?zipp_eta_Eta_arg_nil ?zipp_eta_App_r ?stack_context_eta_App_r ?stack_context_eta_appstack ?eta_rename_appstack in H1; rewrite (skipn_eta_virtuals_focus _ _ (proj1 (Nat.ltb_lt _ _) hj)); cbn [map app] in H2 |- *; constructor; constructor; assumption.
  Defined.

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
    try clear _isconv_args'; etakD_wtp_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args'; etakD_wtp_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args'; etakD_pre; eapply R_positionR; cbn -[stack_position zipc appstack]; [ constructor; apply zipc_App_r_mkApps | apply positionR_App_r_appstack_gen; rewrite length_app; cbn; lia ].
  Defined.
  Next Obligation.
    try clear _isconv_args'; etakD_ctx_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args'; etakD_hwf_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args'; etakD_hwf_solve.
  Defined.
  Next Obligation.
    try clear _isconv_args'; etakD_pre; etakD_wf; destruct H1 as [H1]; destruct H2 as [H2]; rewrite ?zipp_eta_App_r ?stack_context_eta_App_r ?stack_context_eta_appstack ?eta_rename_appstack in H1; constructor; constructor; assumption.
  Defined.

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
    etakD_pre; rewrite -(decompose_stack_eq _ _ _ (eq_sym eq1)); exact f1.
  Qed.
  Next Obligation.
    etakD_pre; rewrite -(decompose_stack_eq _ _ _ (eq_sym eq2)); exact f2.
  Qed.
  Next Obligation.
    etakD_pre; rewrite -(decompose_stack_eq _ _ _ (eq_sym eq1)); eauto.
  Qed.
  Next Obligation.
    etakD_pre; rewrite -(decompose_stack_eq _ _ _ (eq_sym eq2)); eauto.
  Qed.
  Next Obligation.
    etakD_pre; exact (decompose_stack_noStackApp_eta _ _ _ (eq_sym eq1)).
  Qed.
  Next Obligation.
    etakD_pre; exact (decompose_stack_noStackApp_eta _ _ _ (eq_sym eq2)).
  Qed.
  Next Obligation.
    etakD_pre; match goal with w : abstract_env_ext_rel X _ |- _ => destruct (hx _ w) as [x] end; rewrite (decompose_stack_eq _ _ _ (eq_sym eq1)) (decompose_stack_eq _ _ _ (eq_sym eq2)) !stack_context_eta_appstack in x; constructor; exact x.
  Qed.
  Next Obligation.
    etakD_pre; rewrite -(stack_context_eta_appstack l1) -(decompose_stack_eq _ _ _ (eq_sym eq1)); eauto.
  Qed.
  Next Obligation.
    etakD_pre; rewrite -(stack_context_eta_appstack l2) -(decompose_stack_eq _ _ _ (eq_sym eq2)); eauto.
  Qed.
  Next Obligation.
    intros; cbn beta in *; eapply aux; eauto; match goal with hR : PCUICSafeConversionEtaK4.R _ _ _ _ _ |- PCUICSafeConversionEtaK4.R _ _ _ _ _ => eapply R_irrelevance; [ | exact hR ]; cbn; rewrite -(decompose_stack_eq _ _ _ (eq_sym eq1)) -(decompose_stack_eq _ _ _ (eq_sym eq2)); reflexivity end.
  Qed.
  Next Obligation.
    etakD_pre; rewrite (decompose_stack_eta_eq _ _ _ (eq_sym eq1)) (decompose_stack_eta_eq _ _ _ (eq_sym eq2)) (decompose_stack_eq _ _ _ (eq_sym eq1)) stack_context_eta_appstack; cbn [fst]; eauto.
  Qed.

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
      | ccview_cofix mfix idx with inspect ci.(ci_cofix_nondep) := {
        | @exist true eqnd with inspect (unfold_cofix mfix idx) := {
          | @exist (Some (narg, fn)) eq2 := Some (tCase ci p (mkApps fn args) brs) ;
          | @exist None eq2 := False_rect _ _
          } ;
        (* A cofixpoint does not unfold under a case whose return type may depend
           on the scrutinee (BET-339; re-synced from integ-all7's PCUICSafeConversion). *)
        | @exist false eqnd := None
        } ;
      | ccview_other cred _ := None
      }
    }.
  Next Obligation.
    etakD_pre; etakD_wf; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; exact (ctf_context _ Γ c [Case_discr ci p brs] hΣe eq_refl h).
  Qed.
  Next Obligation.
    etakD_pre; destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]; etakD_args_red_at Σ wfΣ; destruct (heΣ _ wfΣ) as [hΣe]; assert (r' : red Σ Γ (tCase ci p c brs) (tCase ci p (mkApps (tConstruct ind' n ui) args) brs)) by (eapply red_case_c; exact (clrel_rel rr)); pose proof (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r') as h'; destruct (rtf_case_construct _ _ _ _ _ _ _ _ _ hΣe h') as [_ [br [hbr _]]]; congruence.
  Qed.
  Next Obligation.
    etakD_pre; destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]; etakD_args_red_at Σ wfΣ; destruct (heΣ _ wfΣ) as [hΣe]; assert (r' : red Σ Γ (tCase ci p c brs) (tCase ci p (mkApps (tCoFix mfix idx) args) brs)) by (eapply red_case_c; exact (clrel_rel rr)); pose proof (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r') as h'; assert (h'' : welltypedE Σ Γ (zipc (tCoFix mfix idx) (appstack args [Case_discr ci p brs]))) by (rewrite zipc_appstack; exact h'); pose proof (ctf_context Σ Γ (tCoFix mfix idx) (appstack args [Case_discr ci p brs]) hΣe (eq_trans (no_Eta_arg_appstack args _) eq_refl) h'') as h3; pose proof (rtf_cofix _ _ _ _ hΣe h3) as h4; unfold unfold_cofix in eq2; revert eq2 h4; destruct (nth_error mfix idx); intros eq2 h4; [discriminate eq2 | exact (h4 eq_refl)].
  Qed.

  Lemma unfold_one_case_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci p c brs h t,
      Some t = unfold_one_case Γ ci p c brs h ->
      cored Σ Γ t (tCase ci p c brs).
  Proof using All.
    intros Σ wfΣ Γ ci p c brs h t e.
    revert e.
    funelim (unfold_one_case Γ ci p c brs h).
    all: try Program.Tactics.bang.
    all: intros eq'' ; noconf eq''.
    - etakD_args_red_at Σ wfΣ.
      destruct (heΣ _ wfΣ) as [hΣe].
      assert (r' : red Σ Γ (tCase ci p c brs) (tCase ci p (mkApps (tConstruct ind' n ui) args) brs))
        by (eapply red_case_c; exact (clrel_rel rr)).
      pose proof (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r') as h'.
      destruct (rtf_case_construct _ _ _ _ _ _ _ _ _ hΣe h') as [<- [br' [hbr hlen]]].
      have ebr : br' = br by congruence. subst br'.
      eapply cored_red_cored.
      + constructor. eapply red_iota; [symmetry; exact eqbr | exact hlen].
      + exact r'.
    - etakD_args_red_at Σ wfΣ.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_case; [exact (eq_sym eqnd)|eauto].
      + eapply red_case_c. exact (clrel_rel rr).
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
    etakD_pre; etakD_wf; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; exact (ctf_context _ Γ c [Proj _] hΣe eq_refl h).
  Qed.
  Next Obligation.
    etakD_pre; destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]; etakD_args_red_at Σ wfΣ; destruct (heΣ _ wfΣ) as [hΣe]; assert (r' : red Σ Γ (tProj (mkProjection i pars narg) c) (tProj (mkProjection i pars narg) (mkApps (tConstruct ind' 0 ui) args))) by (eapply red_proj_c; exact (clrel_rel rr)); pose proof (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r') as h'; destruct (rtf_proj_construct _ _ _ _ _ _ _ hΣe h') as [_ [_ hlt]]; cbn in hlt; symmetry in eq2; apply nth_error_None in eq2; lia.
  Qed.
  Next Obligation.
    etakD_pre; destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]; etakD_args_red_at Σ wfΣ; destruct (heΣ _ wfΣ) as [hΣe]; assert (r' : red Σ Γ (tProj (mkProjection i pars narg) c) (tProj (mkProjection i pars narg) (mkApps (tCoFix mfix idx) args))) by (eapply red_proj_c; exact (clrel_rel rr)); pose proof (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r') as h'; assert (h'' : welltypedE Σ Γ (zipc (tCoFix mfix idx) (appstack args [Proj (mkProjection i pars narg)]))) by (rewrite zipc_appstack; exact h'); pose proof (ctf_context Σ Γ (tCoFix mfix idx) (appstack args [Proj (mkProjection i pars narg)]) hΣe (eq_trans (no_Eta_arg_appstack args _) eq_refl) h'') as h3; pose proof (rtf_cofix _ _ _ _ hΣe h3) as h4; unfold unfold_cofix in eq2; revert eq2 h4; destruct (nth_error mfix idx); intros eq2 h4; [discriminate eq2 | exact (h4 eq_refl)].
  Qed.

  Lemma unfold_one_proj_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ p c h t,
      Some t = unfold_one_proj Γ p c h ->
      cored Σ Γ t (tProj p c).
  Proof using All.
    intros Σ wfΣ Γ p c h t e.
    revert e.
    funelim (unfold_one_proj Γ p c h).
    all: intros eq'' ; noconf eq''.
    - etakD_args_red_at Σ wfΣ.
      destruct (heΣ _ wfΣ) as [hΣe].
      assert (r' : red Σ Γ (tProj (mkProjection i pars narg) c)
                     (tProj (mkProjection i pars narg) (mkApps (tConstruct ind' 0 ui) args)))
        by (eapply red_proj_c; exact (clrel_rel rr)).
      pose proof (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r') as h'.
      destruct (rtf_proj_construct _ _ _ _ _ _ _ hΣe h') as [ei _]. cbn in ei. subst ind'.
      eapply cored_red_cored.
      + constructor. eapply (red_proj _ _ (mkProjection i pars narg)). eauto.
      + exact r'.
    - match type of eq'' with
      | _ = False_rect _ ?f => destruct f
      end.
    - etakD_args_red_at Σ wfΣ.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_proj. eauto.
      + eapply red_proj_c. exact (clrel_rel rr).
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
      | @exist _ _ := unfold_one_prim Γ c u π (eq_sym hna) h
      }
    } ;

    reducible_head Γ _ π h := None.
  Next Obligation.
    etakD_pre; etakD_wf; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; exact (ctf_context _ _ _ _ hΣe hna h).
  Qed.
  Next Obligation.
    etakD_pre; etakD_wf; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; exact (ctf_context _ _ _ _ hΣe hna h).
  Qed.

  (* Hypothesis finders for the funelim cases of [reducible_head] (the inspect equations come
     in either orientation). *)
  Ltac etakD_lookup := match goal with
    | e : abstract_env_lookup X _ = Some _ |- _ => exact e
    | e : Some _ = abstract_env_lookup X _ |- _ => exact (eq_sym e) end.
  Ltac etakD_hna := match goal with
    | e : no_Eta_arg _ = true |- _ => exact e
    | e : true = no_Eta_arg _ |- _ => exact (eq_sym e) end.
  Ltac etakD_case_proj_cored wfΣ := match goal with
    | e : Some _ = unfold_one_case _ _ _ _ _ _ |- _ => pose proof (unfold_one_case_cored _ wfΣ _ _ _ _ _ _ _ e) as rc
    | e : unfold_one_case _ _ _ _ _ _ = Some _ |- _ => pose proof (unfold_one_case_cored _ wfΣ _ _ _ _ _ _ _ (eq_sym e)) as rc
    | e : Some _ = unfold_one_proj _ _ _ _ |- _ => pose proof (unfold_one_proj_cored _ wfΣ _ _ _ _ _ e) as rc
    | e : unfold_one_proj _ _ _ _ = Some _ |- _ => pose proof (unfold_one_proj_cored _ wfΣ _ _ _ _ _ (eq_sym e)) as rc
    end.
  Ltac etakD_delta_red wfΣ := match goal with
    | e : Some (ConstantDecl _) = abstract_env_lookup X _ |- _ => exact (A_const_red _ wfΣ _ _ _ _ _ e eq_refl) end.
  Ltac etakD_delta_cored wfΣ := match goal with
    | e : Some (ConstantDecl _) = abstract_env_lookup X _ |- _ => exact (A_const_cored _ wfΣ _ _ _ _ _ e eq_refl) end.

  Lemma reducible_head_red_zipp :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp t π) (zipp fn ξ) ∥.
  Proof using All.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; try noconf ee.
    all: try solve [ match goal with ee : Some (_, _) = unfold_one_prim _ _ _ _ _ _ |- _ =>
                       exact (fst (snd (unfold_one_prim_facts _ _ _ _ _ _ _ _ ee)) _ wfΣ) end ].
    all: try solve [ eapply unfold_one_fix_red_zipp; eauto ].
    all: try solve [ constructor; unfold zipp; destruct (decompose_stack π) as [l ρ];
                     apply red_mkApps_f; etakD_delta_red wfΣ ].
    all: try solve [ etakD_case_proj_cored wfΣ; apply cored_red in rc; destruct rc as [rc];
                     constructor; unfold zipp; destruct (decompose_stack π) as [l ρ];
                     apply red_mkApps_f; exact rc ].
  Qed.

  Lemma reducible_head_cored :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      cored Σ Γ (zipc fn ξ) (zipc t π).
  Proof using All.
    intros Σ wfΣ Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; try noconf ee.
    all: try solve [ match goal with ee : Some (_, _) = unfold_one_prim _ _ _ _ _ _ |- _ =>
                       exact (snd (snd (snd (unfold_one_prim_facts _ _ _ _ _ _ _ _ ee))) _ wfΣ) end ].
    all: try solve [ eapply unfold_one_fix_cored; eauto ].
    all: try solve [ eapply cored_context_eta; [ etakD_hna | etakD_delta_cored wfΣ ] ].
    all: try solve [ eapply cored_context_eta; [ etakD_hna | etakD_case_proj_cored wfΣ; exact rc ] ].
  Qed.

  Lemma reducible_head_decompose :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof using All.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; try discriminate ee ; try (injection ee; intros; subst).
    all: try solve [ match goal with ee : Some (_, _) = unfold_one_prim _ _ _ _ _ _ |- _ =>
      destruct (unfold_one_prim_shape _ _ _ _ _ _ _ _ ee) as (args & ρ & l & [ed eξ _ _]);
      rewrite ed; subst; rewrite decompose_stack_appstack;
      rewrite (decompose_stack_twice _ _ _ ed); reflexivity end ].
    all: try solve [ eapply unfold_one_fix_decompose; eassumption ].
    all: try reflexivity.
  Qed.

  (* rev 14 B4: a Some answer of reducible_head means its guard held. *)
  Lemma unfold_one_fix_Some_guard Γ mfix idx π h r :
    Some r = unfold_one_fix Γ mfix idx π h -> no_Eta_arg π = true.
  Proof using All. funelim (unfold_one_fix Γ mfix idx π h); intros ee; congruence. Qed.

  Lemma reducible_head_Some_guard Γ t π h r :
    Some r = reducible_head Γ t π h -> no_Eta_arg π = true.
  Proof using All.
    funelim (reducible_head Γ t π h); intros ee; try congruence.
    all: eapply unfold_one_fix_Some_guard; eassumption.
  Qed.

  Lemma reducible_head_stack Γ t π h fn ξ l θ :
    Some (fn, ξ) = reducible_head Γ t π h -> (l, θ) = decompose_stack ξ ->
    [× ξ = appstack l θ, (decompose_stack π).2 = θ, no_Eta_arg θ = true & isStackApp θ = false].
  Proof using All.
    intros e ed.
    have eξ := decompose_stack_eq _ _ _ (eq_sym ed).
    have hd := reducible_head_decompose _ _ _ _ _ _ e. rewrite -ed in hd. cbn [snd] in hd.
    have hna := reducible_head_Some_guard _ _ _ _ _ e.
    split; auto.
    - destruct (decompose_stack π) as [l0 ρ0] eqn:dπ. cbn in hd. subst ρ0.
      rewrite (decompose_stack_eq _ _ _ dπ) no_Eta_arg_appstack in hna. exact hna.
    - exact (decompose_stack_noStackApp_eta _ _ _ (eq_sym ed)).
  Qed.

  Lemma reducible_head_wt Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ :
    Some (fn, ξ) = reducible_head Γ t π h -> welltypedE Σ Γ (zipc fn ξ).
  Proof using All.
    intros e. destruct (heΣ _ wfΣ) as [hΣe].
    pose proof (reducible_head_cored _ wfΣ _ _ _ _ _ _ e) as hc. apply cored_red in hc as [r].
    exact (wt_red (wt := welltypedE) (wfP := wf_extE) Σ Γ _ _ hΣe (h _ wfΣ) r).
  Qed.

  Lemma reducible_head_red_spine Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h fn ξ l θ fn' l' :
    Some (fn, ξ) = reducible_head Γ t π h -> (l, θ) = decompose_stack ξ ->
    red Σ (Γ ,,, stack_context ξ) (mkApps fn l) (mkApps fn' l') ->
    ∥ red Σ (Γ ,,, stack_context π) (zipp t π) (mkApps fn' l') ∥.
  Proof using All.
    intros e ed r.
    destruct (reducible_head_stack _ _ _ _ _ _ _ _ e ed) as [eξ hd hna hst].
    destruct (reducible_head_red_zipp _ wfΣ _ _ _ _ _ _ e) as [rz].
    have ez : zipp fn ξ = mkApps fn l.
    { rewrite eξ /zipp decompose_stack_appstack (decompose_stack_nostack _ hst) /= app_nil_r. reflexivity. }
    have ec : stack_context ξ = stack_context π.
    { rewrite eξ stack_context_appstack -hd. destruct (decompose_stack π) as [l0 ρ0] eqn:dπ. cbn.
      rewrite (decompose_stack_eq _ _ _ dπ) stack_context_appstack. reflexivity. }
    rewrite ez in rz. rewrite ec in r. constructor. etransitivity; eassumption.
  Qed.

  (* A real state's spine reduction, read on its η view (slice A's [A_red_eta_real]), inside a
     Prop goal so that the environment facts can be unsquashed. *)
  Lemma red_spine_eta Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π t' l' θ :
    (decompose_stack π).2 = θ -> no_Eta_arg θ = true -> wtp Γ t π ->
    ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥ ->
    red Σ (Γ ,,, stack_context π) (zipp t π) (mkApps t' l') ->
    ∥ Σ ;;; Γ ,,, stack_context_eta π ⊢ zipp_eta t π ⇝ zipp_eta t' (appstack l' θ) ∥.
  Proof using All.
    intros hd hna ht [w] hr.
    destruct (heΣ _ wfΣ) as [hΣe]. destruct (hΣ _ wfΣ) as [cb].
    unfold zipp in hr.
    destruct (decompose_stack π) as [args ρ] eqn:e. cbn [snd] in hd. subst ρ.
    have hna' : no_Eta_arg π = true by rewrite (decompose_stack_eq _ _ _ e) no_Eta_arg_appstack; exact hna.
    have hcl : is_closed_context (Γ ,,, stack_context_eta π) :=
      wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w.
    constructor. exact (A_red_eta_real Σ hΣe cb Γ t π args θ t' l' hna' e (ht _ wfΣ) hcl hr).
  Qed.

  Lemma conv_term_red_l leq Γ t π t' l' θ t2 π2 :
    (decompose_stack π).2 = θ -> no_Eta_arg θ = true -> wtp Γ t π ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥) ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ red Σ (Γ ,,, stack_context π) (zipp t π) (mkApps t' l') ∥) ->
    conv_term leq Γ t' (appstack l' θ) t2 π2 -> conv_term leq Γ t π t2 π2.
  Proof using All.
    intros hd hna ht hwf hr hc Σ wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (hr Σ wfΣ) as [r]. destruct (hc Σ wfΣ) as [c].
    destruct (red_spine_eta Σ wfΣ Γ t π t' l' θ hd hna ht (hwf Σ wfΣ) r) as [rr].
    have esc : stack_context_eta (appstack l' θ) = stack_context_eta π.
    { rewrite stack_context_eta_appstack -hd. symmetry. apply stack_context_eta_decompose. }
    rewrite esc in c.
    constructor. exact (A_ws_red_l Σ cb leq _ _ _ _ rr c).
  Qed.

  Lemma conv_term_red_r leq Γ t1 π1 t π t' l' θ :
    (decompose_stack π).2 = θ -> no_Eta_arg θ = true -> wtp Γ t π ->
    conv_stack_ctx Γ π1 π ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥) ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ red Σ (Γ ,,, stack_context π) (zipp t π) (mkApps t' l') ∥) ->
    conv_term leq Γ t1 π1 t' (appstack l' θ) -> conv_term leq Γ t1 π1 t π.
  Proof using All.
    intros hd hna ht hx hwf hr hc Σ wfΣ.
    destruct (hΣ _ wfΣ) as [cb].
    destruct (hr Σ wfΣ) as [r]. destruct (hc Σ wfΣ) as [c]. destruct (hx Σ wfΣ) as [x].
    destruct (red_spine_eta Σ wfΣ Γ t π t' l' θ hd hna ht (hwf Σ wfΣ) r) as [rr].
    constructor. exact (A_ws_red_r Σ cb leq _ _ _ _ _ x rr c).
  Qed.

  Lemma wf_stack_eta_step_decompose π args ρ na A :
    (args, ρ) = decompose_stack π -> wf_stack π -> wf_stack (appstack args (Eta_app na A :: ρ)).
  Proof using Type.
    intros e f. have eπ := decompose_stack_eq _ _ _ (eq_sym e). subst π.
    apply wf_stack_eta_step. destruct args as [|a args]; [left; split; [reflexivity|exact f]|right].
    cbn [appstack map app wf_stack is_eta_frame] in f.
    change (map App_l args ++ ρ) with (appstack args ρ) in f.
    rewrite no_Eta_arg_appstack in f. exact f.
  Qed.

  (* The η step, side 1 a λ: the recursive Reduction-state result (a TERM fact) under the λ's
     binder, into the conclusion by K6 ([K6_eta_step_join], the join form of [K6_eta_step], plan row K6). *)
  Lemma eta_step_sound_left leq Γ na A b π1 t2 π2 args2 ρ2 :
    (args2, ρ2) = decompose_stack π2 ->
    isred_full Γ (tLambda na A b) π1 ->
    wtp Γ (tLambda na A b) π1 -> virt_ok (tLambda na A b) π1 = true ->
    wtp Γ t2 π2 -> virt_ok t2 π2 = true ->
    conv_stack_ctx Γ π1 π2 ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥) ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥) ->
    conv_term Conv Γ b (Lambda_bd na A :: π1) t2 (appstack args2 (Eta_app na (eta_rename π1 0 A) :: ρ2)) ->
    conv_term leq Γ (tLambda na A b) π1 t2 π2.
  Proof using All.
    intros e2 ir ht1 hv1 ht2 hv2 hx hwf1 hwf2 hc Σ wfΣ.
    destruct (heΣ _ wfΣ) as [hΣe]. destruct (hΣ _ wfΣ) as [cb].
    destruct (hc Σ wfΣ) as [c]. destruct (hx Σ wfΣ) as [x].
    destruct (hwf1 Σ wfΣ) as [w1]. destruct (hwf2 Σ wfΣ) as [w2].
    have eπ2 := decompose_stack_eq _ _ _ (eq_sym e2).
    have hρ2 := decompose_stack_noStackApp_eta _ _ _ (eq_sym e2).
    have ez1 := zipp_eta_lambda_whnf _ _ _ _ _ ir.
    have ez2 : zipp_eta t2 (appstack args2 (Eta_app na (eta_rename π1 0 A) :: ρ2)) =
               tApp (lift0 1 (zipp_eta t2 π2)) (tRel 0).
    { rewrite (zipp_eta_eta_step _ _ _ _ _ hρ2). now rewrite -eπ2. }
    rewrite ez2 stack_context_eta_eta_step_lambda zipp_eta_Lambda_bd in c.
    rewrite ez1. constructor.
    have hcl1 : is_closed_context (Γ ,,, stack_context_eta π1) :=
      wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w1.
    have hl : is_open_term (Γ ,,, stack_context_eta π1) (tLambda na (eta_rename π1 0 A) (eta_rename π1 1 b)).
    { rewrite -ez1. eapply zipp_eta_open; [exact hv1| |exact hcl1].
      exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe (ht1 _ wfΣ)). }
    have hu : is_open_term (Γ ,,, stack_context_eta π1) (zipp_eta t2 π2).
    { rewrite (ws_cumul_ctx_pbE_length _ _ _ _ x).
      eapply zipp_eta_open; [exact hv2| |exact (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w2)].
      exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe (ht2 _ wfΣ)). }
    exact {| wsE_ctx := hcl1; wsE_left := hl; wsE_right := hu;
             wsE_join := K6_eta_step_join Σ cb (Γ ,,, stack_context_eta π1) leq na (eta_rename π1 0 A)
                           (eta_rename π1 1 b) (zipp_eta t2 π2) hcl1 hl hu (wsE_join c) |}.
  Qed.

  (* The η step, side 2 a λ (symmetric; ws_cumul_pbE_eta_r is K6 through symmetry). *)
  Lemma eta_step_sound_right leq Γ t1 π1 args1 ρ1 na A b π2 :
    (args1, ρ1) = decompose_stack π1 ->
    isred_full Γ (tLambda na A b) π2 ->
    wtp Γ t1 π1 -> virt_ok t1 π1 = true ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥) ->
    conv_term Conv Γ t1 (appstack args1 (Eta_app na (eta_rename π2 0 A) :: ρ1)) b (Lambda_bd na A :: π2) ->
    conv_term leq Γ t1 π1 (tLambda na A b) π2.
  Proof using All.
    intros e1 ir ht1 hv1 hwf1 hc Σ wfΣ.
    destruct (heΣ _ wfΣ) as [hΣe]. destruct (hΣ _ wfΣ) as [cb].
    destruct (hc Σ wfΣ) as [c]. destruct (hwf1 Σ wfΣ) as [w1].
    have eπ1 := decompose_stack_eq _ _ _ (eq_sym e1).
    have hρ1 := decompose_stack_noStackApp_eta _ _ _ (eq_sym e1).
    have ez1 := zipp_eta_lambda_whnf _ _ _ _ _ ir.
    have ez2 : zipp_eta t1 (appstack args1 (Eta_app na (eta_rename π2 0 A) :: ρ1)) =
               tApp (lift0 1 (zipp_eta t1 π1)) (tRel 0).
    { rewrite (zipp_eta_eta_step _ _ _ _ _ hρ1). now rewrite -eπ1. }
    have esc : stack_context_eta ρ1 = stack_context_eta π1 by rewrite eπ1 stack_context_eta_appstack.
    rewrite ez2 stack_context_eta_eta_step_other esc zipp_eta_Lambda_bd in c.
    rewrite ez1. constructor. apply ws_cumul_pbE_eta_r; [exact c|].
    eapply zipp_eta_open; [exact hv1| |exact (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w1)].
    exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe (ht1 _ wfΣ)).
  Qed.

  (* wf_universes of a fallback head, read on the η view (needed by cmpb_term_correct and
     must_expand_check_sound). A real side: through eta_rename_typing (EtaPosK4, row T0); a
     virtual side: the head is a variable. *)
  Lemma heads_wf_universes Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π :
    wtp Γ t π -> virt_ok t π = true ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π) ∥) ->
    wf_universes Σ (eta_rename π 0 t).
  Proof using All.
    intros ht hv hwf. destruct (heΣ _ wfΣ) as [hΣe]. destruct (hwf Σ wfΣ) as [w].
    destruct (no_Eta_arg π) eqn:hna.
    - pose proof (ctf_context (wt := welltypedE) (wfP := wf_extE) Σ Γ t π hΣe hna (ht Σ wfΣ)) as [T hT].
      apply (ctf_wf_universes (wt := welltypedE) (wfP := wf_extE) Σ (Γ ,,, stack_context_eta π) _ hΣe).
      exists (eta_rename π 0 T).
      exact (@eta_rename_typing _ Σ (wf_extE_wfE _ hΣe) Γ π t T hna w hT).
    - destruct (virt_ok_virtual t π hv hna) as (k & u & a & σ & [-> _ _ _]).
      rewrite eta_rename_rename. reflexivity.
  Qed.

  (* The checker's head comparison [compare_term_napp] at #args (base eq_term_upto_univ_napp) on
     two non-application heads, with convertible argument lists, gives the E relation on the
     applications (it replaces the hypothesis [cmpb_heads_ws], 09:20Z-11:50Z). tInd/tConstruct
     heads: the napp-aware congruences [ws_cumul_pbE_Ind]/[ws_cumul_pbE_Construct]
     (PCUICConversionEtaCongr; base's [cumul_Ind_univ]/[cumul_Construct_univ] at #args). Any other
     head: [eq_term_upto_univ_napp] reads [napp] only at a tInd/tConstruct root, so the
     comparison holds at napp 0 ([compare_term]); then base [ws_cumul_pb_compare] ⊆ E
     ([ws_cumul_pb_incl_E]) and the application congruence. *)
  Lemma ws_cumul_pbE_mkApps_terms (Σ : global_env_ext) (cb : ClosedBodies Σ) pb Γ t t' l l' :
    ws_cumul_pbE pb Σ Γ t t' -> ws_cumul_pbE_terms Σ Γ l l' ->
    ws_cumul_pbE pb Σ Γ (mkApps t l) (mkApps t' l').
  Proof using Type.
    intros h hl. induction hl as [|a a' l l' ha hl IH] in t, t', h |- *; [exact h|].
    cbn [mkApps]. apply IH. apply ws_cumul_pbE_App; assumption.
  Qed.

  Lemma cmpb_heads_ws (Σ : global_env_ext) (cb : ClosedBodies Σ) Γ pb t1 args1 t2 args2 :
    isApp t1 = false ->
    is_closed_context Γ -> is_open_term Γ (mkApps t1 args1) -> is_open_term Γ (mkApps t2 args2) ->
    compare_term_napp Σ Σ pb #|args1| t1 t2 ->
    ws_cumul_pbE_terms Σ Γ args1 args2 ->
    ws_cumul_pbE pb Σ Γ (mkApps t1 args1) (mkApps t2 args2).
  Proof using Type.
    intros hap hΓ ho1 ho2 hc ha.
    rewrite !on_free_vars_mkApps in ho1 ho2.
    move/andP: ho1 => [ho1 _]. move/andP: ho2 => [ho2 _].
    destruct hc; try discriminate hap.
    all: try solve [ eapply ws_cumul_pbE_Ind; eassumption ].
    all: try solve [ eapply ws_cumul_pbE_Construct; eassumption ].
    all: apply (ws_cumul_pbE_mkApps_terms Σ cb pb Γ); [|exact ha].
    all: apply ws_cumul_pb_incl_E; eapply ws_cumul_pb_compare; [exact hΓ|exact ho1|exact ho2|].
    all: unfold compare_term; econstructor; eassumption.
  Qed.

  Lemma fallback_cmpb_sound leq Γ t1 π1 t2 π2 :
    isApp t1 = false ->
    wtp Γ t1 π1 -> wtp Γ t2 π2 -> virt_ok t1 π1 = true -> virt_ok t2 π2 = true ->
    conv_stack_ctx Γ π1 π2 ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥) ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥) ->
    cmpb_term_napp leq #|(decompose_stack_eta π1).1| (eta_rename π1 0 t1) (eta_rename π2 0 t2) = true ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π1)
        (decompose_stack_eta π1).1 (decompose_stack_eta π2).1 ∥) ->
    conv_term leq Γ t1 π1 t2 π2.
  Proof using All.
    intros hap ht1 ht2 hv1 hv2 hx hwf1 hwf2 hc ha Σ wfΣ.
    destruct (heΣ _ wfΣ) as [hΣe]. destruct (hΣ _ wfΣ) as [cb].
    destruct (ha Σ wfΣ) as [a]. destruct (hx Σ wfΣ) as [x].
    destruct (hwf1 Σ wfΣ) as [w1]. destruct (hwf2 Σ wfΣ) as [w2].
    have hcl1 := wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w1.
    have ho1 : is_open_term (Γ ,,, stack_context_eta π1) (zipp_eta t1 π1).
    { eapply zipp_eta_open; [exact hv1| |exact hcl1].
      exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe (ht1 _ wfΣ)). }
    have ho2 : is_open_term (Γ ,,, stack_context_eta π1) (zipp_eta t2 π2).
    { rewrite (ws_cumul_ctx_pbE_length _ _ _ _ x).
      eapply zipp_eta_open; [exact hv2| |exact (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w2)].
      exact (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe (ht2 _ wfΣ)). }
    constructor. unfold zipp_eta in ho1, ho2 |- *.
    apply (cmpb_heads_ws Σ cb); [rewrite eta_rename_isApp; exact hap | exact hcl1 | exact ho1 | exact ho2 | | exact a].
    exact (fst (cmpb_term_correct Σ wfΣ leq _ _ _ (heads_wf_universes Σ wfΣ Γ t1 π1 ht1 hv1 hwf1)
                  (heads_wf_universes Σ wfΣ Γ t2 π2 ht2 hv2 hwf2)) hc).
  Qed.

  Lemma fallback_k1_sound leq Γ t1 π1 t2 π2 :
    wtp Γ t1 π1 -> wtp Γ t2 π2 -> virt_ok t1 π1 = true -> virt_ok t2 π2 = true ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π1) ∥) ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ wf_localE Σ (Γ ,,, stack_context_eta π2) ∥) ->
    must_expand_check (abstract_env_lookup X) eqb_term abstract_env_compare_global_instance
      (eta_rename π1 0 t1) (decompose_stack_eta π1).1 (eta_rename π2 0 t2) (decompose_stack_eta π2).1 = true ->
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ ws_cumul_pbE_terms Σ (Γ ,,, stack_context_eta π1)
        (decompose_stack_eta π1).1 (decompose_stack_eta π2).1 ∥) ->
    conv_term leq Γ t1 π1 t2 π2.
  Proof using All.
    intros ht1 ht2 hv1 hv2 hwf1 hwf2 hk ha Σ wfΣ.
    destruct (heΣ _ wfΣ) as [hΣe]. destruct (hΣ _ wfΣ) as [cb].
    destruct (ha Σ wfΣ) as [a]. destruct (hwf1 Σ wfΣ) as [w1].
    constructor. unfold zipp_eta.
    eapply (must_expand_check_sound Σ (abstract_env_lookup X) eqb_term abstract_env_compare_global_instance leq).
    - intros gr n u u' hu hu' hcmp. exact (proj2 (compare_global_instance_correct wfΣ Conv gr n u u' hu hu') hcmp).
    - exact hk.
    - exact (heads_wf_universes Σ wfΣ Γ t1 π1 ht1 hv1 hwf1).
    - exact (heads_wf_universes Σ wfΣ Γ t2 π2 ht2 hv2 hwf2).
    - exact (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w1).
    - exact a.
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
                            (eta_rename π1 0 t1) (decompose_stack_eta π1).1
                            (eta_rename π2 0 t2) (decompose_stack_eta π2).1) := {
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
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; match goal with w : abstract_env_ext_rel X ?Σ |- _ => pose proof (reducible_head_wt Σ w _ _ _ _ _ _ eq1) as hz end; rewrite sp_e zipc_appstack in hz; rewrite zip_appstack_nil_base sp_e stack_context_appstack; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; exact (ctf_context _ _ _ _ hΣe sp_n hz).
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; etakD_args_red; match goal with w : abstract_env_ext_rel X ?Σ |- _ => pose proof (reducible_head_wt Σ w _ _ _ _ _ _ eq1) as hz; rewrite sp_e in hz rr; rewrite stack_context_appstack in rr; exact (rebuilt_wt Σ w _ _ _ _ _ _ hz (clrel_rel rr)) end.
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; eapply R_cored; cbn -[zipc appstack]; intros Σ0 w0; etakD_args_red_at Σ0 w0; pose proof (reducible_head_cored _ w0 _ _ _ _ _ _ eq1) as hc; eapply red_cored_cored; [ | exact hc ]; rewrite sp_e stack_context_appstack in rr; rewrite sp_e !zipc_appstack; apply red_context_zip_eta; exact (clrel_rel rr).
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; rewrite stack_context_eta_appstack -sp_d -stack_context_eta_decompose; match goal with w : abstract_env_ext_rel X _ |- _ => exact (hx _ w) end.
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; unfold virt_ok; rewrite no_Eta_arg_appstack sp_n; reflexivity.
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; rewrite stack_context_eta_appstack -sp_d -stack_context_eta_decompose; eauto.
  Qed.
  Next Obligation.
    etakD_pre; cbn; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; etakD_args_isr; apply isred_full_rebuilt; [ exact sp_n | exact sp_s | assumption | exact (proj1 (ii eq_refl)) | intros Σ0 w0; etakD_args_whnf; rewrite sp_e stack_context_appstack in ww; constructor; exact ww ].
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; refine (conv_term_red_l leq Γ t1 π1 rt1' l1' θ1 t2 π2 sp_d sp_n h1 hwf1 _ h _ _); [ intros Σ0 w0; etakD_args_red_at Σ0 w0; exact (reducible_head_red_spine _ w0 _ _ _ _ _ _ _ _ _ _ eq1 eq2 (clrel_rel rr)) | assumption ].
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; match goal with w : abstract_env_ext_rel X ?Σ |- _ => pose proof (reducible_head_wt Σ w _ _ _ _ _ _ eq1) as hz end; rewrite sp_e zipc_appstack in hz; rewrite zip_appstack_nil_base sp_e stack_context_appstack; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; exact (ctf_context _ _ _ _ hΣe sp_n hz).
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; etakD_args_red; match goal with w : abstract_env_ext_rel X ?Σ |- _ => pose proof (reducible_head_wt Σ w _ _ _ _ _ _ eq1) as hz; rewrite sp_e in hz rr; rewrite stack_context_appstack in rr; exact (rebuilt_wt Σ w _ _ _ _ _ _ hz (clrel_rel rr)) end.
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; eapply R_cored2; cbn -[zipc appstack]; [ constructor; reflexivity | reflexivity | intros Σ0 w0; etakD_args_red_at Σ0 w0; pose proof (reducible_head_cored _ w0 _ _ _ _ _ _ eq1) as hc; eapply red_cored_cored; [ | exact hc ]; rewrite sp_e stack_context_appstack in rr; rewrite sp_e !zipc_appstack; apply red_context_zip_eta; exact (clrel_rel rr) ].
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; rewrite stack_context_eta_appstack -sp_d -stack_context_eta_decompose; match goal with w : abstract_env_ext_rel X _ |- _ => exact (hx _ w) end.
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; unfold virt_ok; rewrite no_Eta_arg_appstack sp_n; reflexivity.
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; rewrite stack_context_eta_appstack -sp_d -stack_context_eta_decompose; eauto.
  Qed.
  Next Obligation.
    etakD_pre; cbn; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; etakD_args_isr; apply isred_full_rebuilt; [ exact sp_n | exact sp_s | assumption | exact (proj1 (ii eq_refl)) | intros Σ0 w0; etakD_args_whnf; rewrite sp_e stack_context_appstack in ww; constructor; exact ww ].
  Qed.
  Next Obligation.
    etakD_pre; destruct (reducible_head_stack _ _ _ _ _ _ _ _ eq1 eq2) as [sp_e sp_d sp_n sp_s]; refine (conv_term_red_r leq Γ t1 π1 t2 π2 rt2' l2' θ2 sp_d sp_n h2 hx hwf2 _ h _ _); [ intros Σ0 w0; etakD_args_red_at Σ0 w0; exact (reducible_head_red_spine _ w0 _ _ _ _ _ _ _ _ _ _ eq1 eq2 (clrel_rel rr)) | assumption ].
  Qed.
  Next Obligation.
    etakD_pre; exact (wf_stack_eta_step_decompose _ _ _ _ _ eq2 f2).
  Qed.
  Next Obligation.
    etakD_pre; rewrite zipc_appstack_Eta_app -(decompose_stack_eq _ _ _ (eq_sym eq2)); eauto.
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as e2'; subst π2; eapply K4_eta_branch_lambda_left.
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as e2'; subst π2; etakD_wf; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; destruct hx as [hx]; destruct hwf1 as [hwf1]; constructor; apply ws_cumul_ctx_pbE_eta_step; [ exact (eta_lambda_open _ _ _ _ _ (zipp_eta_open _ _ _ hv1 (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe h1) (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) hwf1))) | exact hx ].
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as e2'; subst π2; apply virt_ok_eta_step; exact hv2.
  Qed.
  Next Obligation.
    etakD_pre; etakD_wf; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; destruct hwf1 as [hwf1]; exact (@wf_localE_push_real _ welltypedE_context _ (wf_extE_wfE _ hΣe) Γ b (Lambda_bd na A) π1 eq_refl ltac:(first [exact g3 | exact (eq_sym g3)]) h1 hwf1).
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)) as e2'; subst π2; etakD_wf; pose proof closed_context_conversionE as [ccE]; destruct (heΣ _ ltac:(eassumption)) as [hΣe]; destruct hwf1 as [hwf1]; destruct hwf2 as [hwf2]; destruct hx as [hx]; rewrite stack_context_eta_appstack in hwf2 hx; destruct (@wf_localE_push_real _ welltypedE_context _ (wf_extE_wfE _ hΣe) Γ b (Lambda_bd na A) π1 eq_refl ltac:(first [exact g3 | exact (eq_sym g3)]) h1 hwf1) as [hwl]; constructor; exact (@wf_localE_eta_step _ ccE _ (wf_extE_wfE _ hΣe) Γ na A π1 args2 ρ2 hwl hx hwf2).
  Qed.
  Next Obligation.
    etakD_pre; eapply eta_step_sound_left; eassumption.
  Qed.
  Next Obligation.
    etakD_pre; exact (wf_stack_eta_step_decompose _ _ _ _ _ eq1 f1).
  Qed.
  Next Obligation.
    etakD_pre; rewrite zipc_appstack_Eta_app -(decompose_stack_eq _ _ _ (eq_sym eq1)); eauto.
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)) as e1'; subst π1; eapply K4_eta_branch_lambda_right.
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)) as e1'; subst π1; match goal with w : abstract_env_ext_rel X ?Σ |- _ => destruct (heΣ _ w) as [hΣe]; destruct (hΣ _ w) as [cb]; destruct (hx _ w) as [x]; destruct (hwf2 _ w) as [w2]; constructor; apply ws_cumul_ctx_pbE_sym; apply ws_cumul_ctx_pbE_eta_step; [ exact (eta_lambda_open _ _ _ _ _ (zipp_eta_open _ _ _ hv2 (ref_open_term (wt := welltypedE) (wfP := wf_extE) _ _ _ hΣe (h2 _ w)) (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) w2))) | exact (ws_cumul_ctx_pbE_sym x) ] end.
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)) as e1'; subst π1; apply virt_ok_eta_step; exact hv1.
  Qed.
  Next Obligation.
    etakD_pre; pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)) as e1'; subst π1; pose proof closed_context_conversionE as [ccE]; match goal with w : abstract_env_ext_rel X ?Σ |- _ => destruct (heΣ _ w) as [hΣe]; destruct (hΣ _ w) as [cb]; destruct (hwf1 _ w) as [w1]; destruct (hwf2 _ w) as [w2]; destruct (hx _ w) as [x]; rewrite stack_context_eta_appstack in w1 x; destruct (@wf_localE_push_real _ welltypedE_context _ (wf_extE_wfE _ hΣe) Γ b (Lambda_bd na A) π2 eq_refl ltac:(first [exact g3 | exact (eq_sym g3)]) (h2 _ w) w2) as [hwl]; constructor; exact (@wf_localE_eta_step _ ccE _ (wf_extE_wfE _ hΣe) Γ na A π2 args1 ρ1 hwl (ws_cumul_ctx_pbE_sym x) w1) end.
  Qed.
  Next Obligation.
    etakD_pre; match goal with w : abstract_env_ext_rel X ?Σ |- _ => destruct (heΣ _ w) as [hΣe]; destruct (hwf2 _ w) as [w2]; exact (@wf_localE_push_real _ welltypedE_context _ (wf_extE_wfE _ hΣe) Γ b (Lambda_bd na A) π2 eq_refl ltac:(first [exact g3 | exact (eq_sym g3)]) (h2 _ w) w2) end.
  Qed.
  Next Obligation.
    etakD_pre; eapply eta_step_sound_right; eassumption.
  Qed.
  Next Obligation.
    etakD_pre; eapply R_stateR; cbn -[zipc]; first [ reflexivity | constructor; reflexivity | constructor ].
  Qed.
  Next Obligation.
    etakD_pre; eapply fallback_cmpb_sound; first [ eassumption | match goal with h : isred_full _ _ _ |- isApp _ = false => exact (proj1 h) end ].
  Qed.
  Next Obligation.
    etakD_pre; eapply R_stateR; cbn -[zipc]; first [ reflexivity | constructor; reflexivity | constructor ].
  Qed.
  Next Obligation.
    etakD_pre; eapply fallback_k1_sound; eassumption.
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
    destruct (heΣ _ wfΣ) as [hΣe].
    destruct x, y; cbn in *.
    red in HR. cbn in HR. red in HR. cbn in HR.
    depind HR.
    - cbn in *.
      eapply cored'_postpone in H as [u' [cor eq]]; [|exact wfΣ].
      destruct eq as [<-].
      apply cored_red in cor as [r].
      eapply (wt_red (wt := welltypedE) (wfP := wf_extE)); [exact hΣe|exact H0|exact r].
    - simpl in *. destruct e. now rewrite e.
  Qed.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (f1 : wf_stack π1) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (f2 : wf_stack π2) (h2 : wtp Γ t2 π2)
    : Ret s Γ t1 π1 t2 π2 :=

    isconv_full s Γ t1 π1 f1 h1 t2 π2 f2 h2 hx :=
      Fix_F (R := R Γ)
            (fun '(PCUICSafeConversionEtaK4.mkpack s' t1' π1' t2' π2' f1' f2' h2') =>
              wtp Γ t1' π1' ->
              wtp Γ t2' π2' ->
              Ret s' Γ t1' π1' t2' π2'
            )
            (fun pp f => _)
            (x := mkpack Γ s t1 π1 t2 π2 f1 f2 _)
            _ _ _ _.
  Next Obligation.
    destruct pp as [s0 t0 π0 t0' π0' g1 g2 hh]. cbn beta iota zeta in *.
    unshelve eapply (_isconv s0 Γ t0 π0 g1 _ t0' π0' g2 hh).
    all: try assumption.
    intros s' t1' π1' t2' π2' f1' f2' h1' h2' hx' hR.
    exact (f (mkpack Γ s' t1' π1' t2' π2' f1' f2' h2') hR h1' h2').
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
    intros; try unfold PCUICSafeConversionEtaK4.conv_stack_ctx_eta; intros.
    match goal with w : abstract_env_ext_rel X ?Σ, h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ _ _ |- _ =>
      destruct (h _ w) as [T ht]; destruct (heΣ _ w) as [hΣe]; destruct (hΣ _ w) as [cb] end.
    constructor. cbn. apply ws_cumul_ctx_pbE_refl.
    exact (wf_local_closed_contextE (wfΣ := wf_extE_wfE _ hΣe) (typingE_wf_local ht)).
  Qed.
  Next Obligation.
    intros.
    match goal with w : abstract_env_ext_rel X ?Σ, h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ _ _ |- _ =>
      destruct (h _ w) as [T ht] end.
    constructor. cbn. exact (typingE_wf_local ht).
  Qed.
  Next Obligation.
    intros.
    match goal with w : abstract_env_ext_rel X ?Σ, h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ _ _ |- _ =>
      destruct (h _ w) as [T ht] end.
    constructor. cbn. exact (typingE_wf_local ht).
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

  (* Satisfying instance of the squashed named hypothesis [closed_context_conversionE], at base
     typing: the squash of EtaPosK4's [closed_context_conversion_inst]. (1) It shows the
     hypothesis is consistent; (2) it does NOT discharge the typingE instantiation (row T0). *)
  Lemma closed_context_conversionE_base_inst :
    ∥ forall (Σ : global_env_ext), wf Σ.1 -> forall Γ t T Γ',
      Σ ;;; Γ |- t : T -> wf_local Σ Γ' -> Σ ⊢ Γ = Γ' -> Σ ;;; Γ' |- t : T ∥.
  Proof using Type. exact (sq closed_context_conversion_inst). Qed.

  Transparent reduce_args_E.

End Conversion.

(* Satisfying instances of the named hypotheses of section [Conversion], at base typing,
   restated here so that each hypothesis has its instance in this file (the squashed
   [closed_context_conversionE] has [closed_context_conversionE_base_inst] above). Each one
   (1) shows the hypothesis is consistent, so the theorems above are about something real, and
   (2) does NOT discharge the [welltypedE]/[typingE] instantiation, which waits for the rows named
   at each hypothesis (reduce_factsE: T1/T6/W-c; conv_factsE: T6; closed_context_conversionE: T0;
   welltypedE_context: T6/T2a). [reduce_factsE] and [conv_factsE] hold the GENUINE fields of the
   two classes at [welltypedE] ([ReduceTypedFactsE], [ConvTypedFactsE]); the base instances of the
   full classes below prove the same statements at [welltyped]/[wf_ext]. *)
Lemma reduce_factsE_base_inst {cf : checker_flags} : ReduceTypedFacts welltyped wf_ext.
Proof. exact reduce_typed_facts_base. Qed.

Lemma conv_factsE_base_inst {cf : checker_flags} : ConvTypedFacts welltyped wf_ext.
Proof. exact conv_typed_facts_base. Qed.

Lemma welltypedE_context_base_inst {cf : checker_flags} (Σ : global_env_ext) : wf Σ.1 -> forall Γ t,
  no_Eta_arg (snd t) -> welltyped Σ Γ (zip t) -> welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
Proof. exact (welltyped_context_inst Σ). Qed.

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
