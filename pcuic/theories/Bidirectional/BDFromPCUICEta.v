(* Distributed under the terms of the MIT license.   *)

(** * Bidirectional completeness over the η relations (plan row T6): the E copy of [BDFromPCUIC]

  A copy of base [Bidirectional/BDFromPCUIC.v] from [typingE] to the landed bidirectional E
  judgments ([BDTypingEta]: [checkingE], [inferingE], ...): [typing] → [typingE], [wf] → [wfE],
  [wf_local] → [wf_localE], [wf_local_rel] → [wf_local_relE], [isType] → [isTypeE], [isTypeRel] →
  [isTypeRelE], [ctx_inst (typing Σ)] → [ctx_instE Σ], the bidirectional judgments → their E
  copies, [env_prop] → [env_propE], [Σ ;;; Γ ⊢ _ ≤ _] / [⊢ _ = _] → [⊢E], [ws_cumul_pb_terms] →
  [ws_cumul_pbE_terms]. Nothing else changes in a statement; each name takes the suffix [E]
  (plan [t0-plan.md] §2, D1). Map, base → E: [conv_check] → [conv_checkE]; [conv_infer_sort] →
  [conv_infer_sortE]; [conv_infer_prod] → [conv_infer_prodE]; [conv_infer_ind] →
  [conv_infer_indE]; [conv_lift_judgment] → [conv_lift_judgmentE]; [conv_lift_judgment_univ] →
  [conv_lift_judgment_univE]; [bidirectional_from_pcuic] → [bidirectional_from_pcuicE];
  [typing_infering], [typing_checking], [typing_infering_sort], [lift_typing_lift_sorting],
  [isType_infering_sort], [isTypeRel_infering_sort], [typing_infer_prod], [typing_infer_ind],
  [wf_local_wf_local_bd], [wf_local_rel_wf_local_bd], [ctx_inst_typing_bd] → the same name with
  [E]. Base's two untyped lemmas [ctx_inst_length] and [ctx_inst_app_impl] mention neither
  typing nor conversion; they are used from base ([BDFromPCUIC.ctx_inst_length],
  [BDFromPCUIC.ctx_inst_app_impl]), not copied.

  ** Where T8 enters: the three [conv_infer_*] helpers and the (co)fixpoint witness

  Base [conv_infer_sort]/[_prod]/[_ind] ([BDFromPCUIC.v:55-93]) invert [T' ≤ tSort s] (resp.
  [tProd], [mkApps (tInd ..)]) into a REDUCT of [T'] by [ws_cumul_pb_Sort_r_inv] (resp.
  [_Prod_r_inv], [_Ind_r_inv]): base confluence. Over η the raw inversion is false
  ([A6_F_raw_false]); its typed form is T8. Here each helper takes T8 from the proved theorems
  of row B1 ([PCUICEtaT8Probe.T8_*_r], through [T8_*_r_plug] below), and discharges the
  premise [Σ ;;; Γ |-E T' : tSort s'] as [lanes/eta/meta/t8-consumers.md] §2 says: the
  helper's typing premise [tyt] (unused in base) gives [wf_localE Σ Γ] ([typingE_wf_local]),
  soundness gives [t :E T'] ([infering_typingE], [BDToPCUICEta]), validity gives [isTypeE T']
  ([validityE]). Forms used: [Sort_r], [Prod_r], [Ind_r] (each at [pb := Cumul] in the
  helpers; [Prod_r] and [Ind_r] at [pb := Conv] in the fixpoint witness). The [_l] forms are
  not used.

  [conv_infer_ind]'s universe clause. T8's [Ind_r] relates the instances by
  [cmp_global_instance_finst] at [#|l|]; base's conclusion is [cmp_ind_universes] at [#|args|]
  (base [cmp_global_instance] at [Cumul]). They agree at full application
  ([finst_ind_glue_full], [PCUICEtaFInstGlue]). The typing premise gives it: validity types
  [mkApps (tInd ind ui) args] at a sort, and copy 16's [isType_mkApps_Ind_invE]
  ([PCUICInductivesEta]) gives [#|args| = ind_npars + context_assumptions indices], which is the
  head's full arity ([isTypeE_mkApps_Ind_head_arity] below). No statement changes.

  ** The (co)fixpoint witness: conversion witness ⇒ reduction witness, TYPED (proved here)

  [typingE]'s [wf_fixpointE]/[wf_cofixpointE] carry a [conv_witnessE] (η conversion);
  [inferE_Fix]/[inferE_CoFix] carry base's reduction witness [wf_fixpoint_red]/
  [wf_cofixpoint_red] ([BDTypingEta], design point B). Base goes from one to the other with
  [mfix_on_ind_conv_red] ([PCUICFixWitness.v:217-225], used at [BDFromPCUIC.v:357,372]). Its
  closed-only form is FALSE over η ([PCUICFixWitnessEtaCounter.v]); the ruled route
  ([t0-plan.md] §6 risk 5, row PCUICFixWitness, option (i)) is a typed reduct lemma proved
  with E subject reduction. It is proved here ([red_fix_witnessE], [red_cofix_witnessE],
  [mfix_body_on_conv_redE_fix]/[_cofix], [mfix_on_ind_conv_redE_fix]/[_cofix],
  [wf_fixpointE_wf_fixpoint_red], [wf_cofixpointE_wf_cofixpoint_red]), with no new forecast:
  - the witness [ty] is a telescope [it_mkProd_or_LetIn ctx concl] ([check_one_fix_inv],
    [check_one_cofix_inv]); its let-ins are zeta-reduced on the witness side
    ([ws_cumul_pbE_red_r_inv], untyped, and [smash_context_app_def]);
  - at each assumption, T8 [Prod_r] at [Conv] reduces the TYPED declared type to a product;
    E subject reduction types the reduct ([isType_redE], T1) and [isType_tProdE] its domain
    and codomain; the codomain comparison is moved into the reduct's context by
    [ws_cumul_pbE_ws_cumul_ctx] (untyped);
  - at the recursive argument (fixpoint) or the conclusion (cofixpoint), T8 [Ind_r] at [Conv]
    reduces the TYPED domain (resp. codomain) to an applied inductive. The [Ind_r] premise is a
    typing at a sort taken from the typed reduct, never from a [welltypedE] fact (the
    [t8-consumers.md] trap).
  Base's lemma is generic over a [ShapeCheck] check; the E proof reads the structure of
  [check_one_fix]/[check_one_cofix], so there is one E lemma per check (the two checks base's
  completeness uses). Each keeps base's premises with [wf_local] → [wf_localE], [isType] →
  [isTypeE], [conv_witness] → [conv_witnessE].

  ** Proof routes that differ from base (statements do not)

  - Case, the return-type comparison: base rebuilds [ws_cumul_ctx_pb_refl] of the predicate
    context from [wf_case_predicate_context] and validity; here the [typingE] induction
    principle already carries [wf_localE Σ (Γ ,,, predctx)].
  - LetIn: base's [ws_cumul_pb_LetIn_bo] keeps [pb] on the body; the A5 twin
    [ws_cumul_pbE_LetIn_bo] is at [Conv], so the landed [ws_cumul_pbE_LetIn_bo_pb] (A7) is used.
  - App: base's [substitution_ws_cumul_pb_vass] (typed) → the untyped
    [substitution0_ws_cumul_pbE] with the scoping of the argument.
  - Proj: base types the substitution [c :: rev args] with [projection_subslet] and then forgets
    the typing ([subslet_untyped_subslet]); here the untyped substitution is built directly
    ([untyped_subslet_assumption_context]: the projection context is an assumption context of
    the right length), and the closedness of the projection context comes from the closed
    parameters ([declared_inductive_closed_paramsE]) instead of [wf_projection_context]. The
    instances' consistency comes from [isType_mkApps_Ind_invE] (copy 16) in place of
    base [invert_type_mkApps_ind].

  ** The forecast block

  The lemmas take the forecast classes of [BDToPCUICEta] (T1's [SRForecastCopy18], copy 18b, and
  [BDForecastCopy18], copy 18a's [ctx_inst_app_weakE], kept for a binder-name mismatch) as
  section [Context]s; they are imported, never redefined. Copies 10, 12, 14, 15, 16 and 18a have
  landed and are imported; this file's [BDFromForecastCopy18] (copy 18a's
  [projection_cumulative_indicesE], [PCUICInductiveInversionEta]) was deleted after a
  compiled-form identity check. [Print Assumptions] in [BDFromPCUICEtaInstances] shows every
  class as an argument.

  ** The checker's facts

  [T6BDc_<field>_fit] restates, verbatim, each field of the checker's [T6BDc_facts]
  ([safechecker/theories/PCUICTypingEtaHyps.v:192-205] on [wip/etak-k7-2026-10-29] @ [7818e65b],
  blob [990d9532]) and proves it with the lemma here. *)

From Stdlib Require Import Bool List Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping
     PCUICEquality PCUICUnivSubst PCUICClosed PCUICCumulativity PCUICReduction PCUICContexts
     PCUICCases PCUICSpine PCUICSubstitution
     PCUICWellScopedCumulativity PCUICConversion PCUICOnFreeVars PCUICClosedTyp PCUICSigmaCalculus
     PCUICInductives PCUICInductiveInversion PCUICWeakeningEnv
     PCUICUnivSubstitutionConv PCUICFixWitness BDTyping.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningEnvTypEta
     PCUICWeakeningTypEta PCUICEtaFInst PCUICEtaFInstGlue
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICEtaA6 PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICInversionEta PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta
     PCUICInductivesEta PCUICInductiveInversionEta
     PCUICValidityEta PCUICSREtaConv PCUICSREta BDTypingEta BDToPCUICEta.
From MetaRocq.PCUIC Require BDFromPCUIC PCUICEtaT8Probe.

From Stdlib Require Import ssreflect.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** Forecast notes *)

(* Row B1's [fix_rarg_inductive] is PROVED ([PCUICEtaT8Probe.fix_rarg_inductive], section
   [FixRargInductive]), and T8 is used through the two-hypothesis forms [PCUICEtaT8Probe.T8_*_r_two],
   so this file has no B1 forecast. The class [BDFromForecastB1] it had was deleted after a
   compiled check: its field has the type of [PCUICEtaT8Probe.fix_rarg_inductive] (both-way
   ascription), with [cf] and [Σ] explicit where the proved lemma has them implicit. *)


(** ** Syntactic and untyped helpers (no class) *)

(** An assumption context is kept, in order, at the end of the smash of a larger context. *)
Lemma smash_context_acc_assumption_context acc Δ :
  assumption_context Δ -> smash_context acc Δ = acc ++ Δ.
Proof.
  induction 1 as [|na t Γ hΓ IH] in acc |- *; cbn; [now rewrite app_nil_r|].
  rewrite IH. now rewrite -app_assoc.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn_nil Δ B :
  decompose_prod_assum [] (it_mkProd_or_LetIn Δ B) = decompose_prod_assum Δ B.
Proof.
  induction Δ as [|[na [b|] A] Δ IH] in B |- *; cbn; [reflexivity| |]; now rewrite IH.
Qed.

Lemma nth_error_app_mid {A} (l l' : list A) x n : #|l| = n -> nth_error (l ++ x :: l') n = Some x.
Proof. intros <-. induction l; cbn; auto. Qed.

(** [check_one_fix] on a telescope whose first [S n] binders are assumptions, the last of them
    an applied inductive, at [rarg := n]. *)
Lemma check_one_fix_it_mkProd_ass dn db n na ind u l Δ B :
  assumption_context Δ -> #|Δ| = n ->
  check_one_fix {| dname := dn; dtype := it_mkProd_or_LetIn (vass na (mkApps (tInd ind u) l) :: Δ) B;
                   dbody := db; rarg := n |} = Some (inductive_mind ind).
Proof.
  intros ass len.
  have hass : assumption_context (vass na (mkApps (tInd ind u) l) :: Δ) by constructor.
  cbv beta iota delta [check_one_fix].
  rewrite decompose_prod_assum_it_mkProd_or_LetIn_nil decompose_prod_assum_ctx.
  destruct (decompose_prod_assum [] B) as [ctxB concl].
  cbv beta iota.
  rewrite /app_context smash_context_app (smash_context_acc_assumption_context _ _ hass).
  have e : List.rev (smash_context [] ctxB ++ vass na (mkApps (tInd ind u) l) :: Δ) =
    List.rev Δ ++ vass na (mkApps (tInd ind u) l) :: List.rev (smash_context [] ctxB).
  { rewrite List.rev_app_distr /=. now rewrite -app_assoc. }
  have hn : #|List.rev Δ| = n by rewrite List.length_rev.
  rewrite e (nth_error_app_mid _ _ _ _ hn).
  change (decl_type (vass na (mkApps (tInd ind u) l))) with (mkApps (tInd ind u) l).
  rewrite decompose_app_mkApps //=. now destruct ind.
Qed.


(** ** The lemmas *)

Section BDFromPCUICEta.

(* FORECAST-ONLY: one premise per class: T1's one ([PCUICSREta], copy 18b) and [BDToPCUICEta]'s
   one (copy 18a's [ctx_inst_app_weakE], kept: binder-name mismatch); delete each when its row
   lands. *)
Context {F18 : SRForecastCopy18} {B18 : BDForecastCopy18}.

(** ** Typed T8, proved (row B1)

  The three T8 forms the proofs use. Each is the proved two-hypothesis theorem
  [PCUICEtaT8Probe.T8_*_r_two] with its one hypothesis, [subject_reduction], discharged by
  [PCUICSREta.subject_reductionE] (the same compiled type: [T1_subject_reduction_fit], the
  checker contract's text). Its [wfE Σ] is the statement's own premise ([t8-assembly-review.md]
  N1), and [fix_rarg_inductive] is proved inside [PCUICEtaT8Probe]. The type of each is the
  body of the pinned
  [Definition] of [PCUICEtaT8Probe.v] (section [Statements]) under [forall (cf : checker_flags)
  (Σ : global_env_ext),], verbatim: [T8_Sort_r_plug] is [T8_Sort_r_statement] (:121-125),
  [T8_Prod_r_plug] is [T8_Prod_r_statement] (:133-140), [T8_Ind_r_plug] is
  [T8_Ind_r_statement] (:151-158). [T8_*_r_plug_fit] type-checks each against its
  [Definition]. The [_l] forms are not used. *)
Definition T8_Sort_r_plug :
    forall (cf : checker_flags) (Σ : global_env_ext),
    forall Γ pb T s s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ T (tSort s) ->
      ∑ s'', Σ ;;; Γ ⊢ T ⇝ tSort s'' × compare_sort Σ pb s'' s :=
  fun cf Σ => @PCUICEtaT8Probe.T8_Sort_r_two cf Σ (PCUICSREta.subject_reductionE (cf := cf)).

Definition T8_Prod_r_plug :
    forall (cf : checker_flags) (Σ : global_env_ext),
    forall Γ pb T na dom codom s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ T (tProd na dom codom) ->
      ∑ na' dom' codom',
        [× Σ ;;; Γ ⊢ T ⇝ tProd na' dom' codom', eq_binder_annot na' na,
           ws_cumul_pbE Conv Σ Γ dom' dom &
           ws_cumul_pbE pb Σ (Γ ,, vass na dom) codom' codom] :=
  fun cf Σ => @PCUICEtaT8Probe.T8_Prod_r_two cf Σ (PCUICSREta.subject_reductionE (cf := cf)).

Definition T8_Ind_r_plug :
    forall (cf : checker_flags) (Σ : global_env_ext),
    forall Γ pb T ind ui l s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ T (mkApps (tInd ind ui) l) ->
      ∑ ui' l',
        [× Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind ui') l',
           cmp_global_instance_finst Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| ui' ui &
           ws_cumul_pbE_terms Σ Γ l' l] :=
  fun cf Σ => @PCUICEtaT8Probe.T8_Ind_r_two cf Σ (PCUICSREta.subject_reductionE (cf := cf)).

(** Each type is its pinned statement: the type at [cf] and [Σ] is the [Definition] of
    [PCUICEtaT8Probe.v] at [cf] and [Σ]. *)
Definition T8_Sort_r_plug_fit (cf : checker_flags) (Σ : global_env_ext) :
  @PCUICEtaT8Probe.T8_Sort_r_statement cf Σ := T8_Sort_r_plug cf Σ.
Definition T8_Prod_r_plug_fit (cf : checker_flags) (Σ : global_env_ext) :
  @PCUICEtaT8Probe.T8_Prod_r_statement cf Σ := T8_Prod_r_plug cf Σ.
Definition T8_Ind_r_plug_fit (cf : checker_flags) (Σ : global_env_ext) :
  @PCUICEtaT8Probe.T8_Ind_r_statement cf Σ := T8_Ind_r_plug cf Σ.

Lemma isTypeE_mkApps_Ind_head_arity {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ ind u args} :
  wf_localE Σ Γ -> isTypeE Σ Γ (mkApps (tInd ind u) args) ->
  head_arity Σ.1 (IndRef ind) <= #|args|.
Proof.
  intros wfΓ hT. cbv beta iota delta [head_arity_gen].
  destruct (lookup_inductive_gen (lookup_env Σ.1) ind) as [[mdecl idecl]|] eqn:hl; [|lia].
  have decl : declared_inductive Σ.1 ind mdecl idecl.
  { apply declared_inductive_from_gen. now apply lookup_inductive_declared. }
  destruct (isType_mkApps_Ind_invE wfΣ decl wfΓ hT) as (ps & as' & hs). cbv zeta in hs.
  destruct hs as [_ _ h1 h2 _].
  rewrite /app_context context_assumptions_app -(declared_minductive_ind_nparsE (proj1 decl)).
  rewrite -(firstn_skipn (ind_npars mdecl) args) List.length_app h1 h2. lia.
Qed.

(** Lemmas to get checking and constrained inference from inference + cumulativity. Relies on
    T8 (the typed inversion to a head form; base: confluence + injectivity of type
    constructors) *)

(** Base [conv_check] ([BDFromPCUIC.v:46]). *)
Lemma conv_checkE `{checker_flags} Σ (wfΣ : wfE Σ) Γ t T :
  (∑ T' : term, Σ ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ T) ->
  Σ ;;; Γ |-E t ◃ T.
Proof.
  intros (?&?&?).
  econstructor ; tea.
  now apply ws_cumul_pbE_forget.
Qed.

(** Base [conv_infer_sort] ([BDFromPCUIC.v:55]). T8 [Sort_r]. *)
Lemma conv_infer_sortE `{checker_flags} Σ (wfΣ : wfE Σ) Γ t s :
  Σ ;;; Γ |-E t : tSort s ->
  (∑ T' : term, Σ ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ tSort s) ->
  {s' & Σ ;;; Γ |-E t ▹□ s' × leq_sort Σ s' s}.
Proof.
  intros tyt (T'&inf&Cumt).
  have wfΓ := typingE_wf_local tyt.
  destruct (validityE (infering_typingE Σ Γ t T' wfΣ wfΓ inf)) as (_ & s1 & tyT' & _).
  destruct (T8_Sort_r_plug _ Σ Γ Cumul T' s s1 wfΣ tyT' Cumt) as (s'' & r & le).
  exists s''. split; [|exact le].
  econstructor ; tea.
  now apply closed_red_red.
Qed.

(** Base [conv_infer_prod] ([BDFromPCUIC.v:68]). T8 [Prod_r]. *)
Lemma conv_infer_prodE `{checker_flags} Σ (wfΣ : wfE Σ) Γ t na A B :
  Σ ;;; Γ |-E t : tProd na A B ->
  (∑ T', (Σ ;;; Γ |-E t ▹ T') × (Σ ;;; Γ ⊢E T' ≤ tProd na A B)) ->
  ∑ na' A' B', [× Σ ;;; Γ |-E t ▹Π (na',A',B'),
    eq_binder_annot na na', Σ ;;; Γ ⊢E A' = A & Σ ;;; Γ ,, vass na A ⊢E B' ≤ B].
Proof.
  intros tyt (T'&inf&Cumt).
  have wfΓ := typingE_wf_local tyt.
  destruct (validityE (infering_typingE Σ Γ t T' wfΣ wfΓ inf)) as (_ & s1 & tyT' & _).
  destruct (T8_Prod_r_plug _ Σ Γ Cumul T' na A B s1 wfΣ tyT' Cumt) as (na' & A' & B' & [r ena hA hB]).
  exists na', A', B'. split; tea.
  2: now apply eq_binder_annot_sym.
  econstructor ; tea.
  now apply closed_red_red.
Qed.

(** Base [conv_infer_ind] ([BDFromPCUIC.v:81]). T8 [Ind_r]; the universe clause at full
    application ([isTypeE_mkApps_Ind_head_arity], [finst_ind_glue_full]). *)
Lemma conv_infer_indE `{checker_flags} Σ (wfΣ : wfE Σ) Γ t ind ui args :
  Σ ;;; Γ |-E t : mkApps (tInd ind ui) args ->
  (∑ T', (Σ ;;; Γ |-E t ▹ T') × (Σ ;;; Γ ⊢E T' ≤ mkApps (tInd ind ui) args)) ->
  ∑ ui' args', [× Σ ;;; Γ |-E t ▹{ind} (ui',args'),
      cmp_ind_universes Σ ind #|args| ui' ui
      & ws_cumul_pbE_terms Σ Γ args' args].
Proof.
  intros tyt (T'&inf&Cumt).
  have wfΓ := typingE_wf_local tyt.
  destruct (validityE (infering_typingE Σ Γ t T' wfΣ wfΓ inf)) as (_ & s1 & tyT' & _).
  pose proof (isTypeE_mkApps_Ind_head_arity wfΓ (validityE tyt)) as harity.
  destruct (T8_Ind_r_plug _ Σ Γ Cumul T' ind ui args s1 wfΣ tyT' Cumt) as (ui' & args' & [r hcmp hargs]).
  exists ui', args'. split; tea.
  - econstructor ; tea.
    now apply closed_red_red.
  - exact (finst_ind_glue_full Σ.1 _ Cumul ind _ _ _ harity hcmp).
Qed.

(** Base [conv_lift_judgment] ([BDFromPCUIC.v:95]). *)
Lemma conv_lift_judgmentE `{checker_flags} Σ Γ na b ty :
  lift_sorting (checkingE Σ Γ) (fun T u => ∑ u', Σ;;; Γ |-E T ▹□ u' × leq_sort Σ u' u) (j_decl (mkdecl na b ty)) ->
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_decl (mkdecl na b ty)).
Proof.
  intro Hj.
  apply lift_sorting_ex_it_impl_gen with Hj => //=.
  1: now destruct b.
  intros (u' & ? & Hle) er; eexists; split; tea. eapply geq_relevance; tea.
Qed.

(** Base [conv_lift_judgment_univ] ([BDFromPCUIC.v:105]). *)
Lemma conv_lift_judgment_univE `{checker_flags} Σ Γ na b ty u :
  lift_sorting (checkingE Σ Γ) (fun T u => ∑ u', Σ;;; Γ |-E T ▹□ u' × leq_sort Σ u' u) (j_decl_s (mkdecl na b ty) (Some u)) ->
  ∑ u', lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_decl_s (mkdecl na b ty) (Some u')) × leq_sort Σ u' u.
Proof.
  intros (Htm & u0 & (u' & Hty & Hle) & <- & Her); cbn in *.
  exists u'; split; tas.
  repeat (eexists; tea).
  eapply geq_relevance; tea.
Qed.

(** ** The (co)fixpoint witness: from the conversion witness to a reduction witness, typed

  Twin of base [mfix_body_on_conv_red] / [mfix_on_ind_conv_red] ([PCUICFixWitness.v:206-225])
  for the two checks; see the header. *)

Section FixWitnessE.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** The context move of the codomain comparison: [Γ ,, vass na A ≡ Γ ,, vass na' A']. *)
  Lemma ws_cumul_ctx_pbE_vass {Γ na na' A A'} :
    is_closed_context Γ -> eq_binder_annot na na' -> ws_cumul_pbE Conv Σ Γ A A' ->
    ws_cumul_ctx_pbE Conv Σ (Γ ,, vass na A) (Γ ,, vass na' A').
  Proof.
    intros clΓ ena hA. constructor.
    - exact (ws_cumul_ctx_pbE_refl (Σ := Σ) Γ clΓ).
    - cbv beta delta [ws_cumul_declsE]. constructor; assumption.
  Qed.

  (** The fixpoint check. A TYPED [T], E-convertible to a telescope whose [n]-th smashed
      assumption is an applied inductive, reduces to a telescope whose first [S n] binders are
      assumptions, the last of them an applied inductive of the same block. *)
  Lemma red_fix_witnessE ctx :
    forall n argd Γ T concl ind u args,
      isTypeE Σ Γ T ->
      ws_cumul_pbE Conv Σ Γ T (it_mkProd_or_LetIn ctx concl) ->
      nth_error (List.rev (smash_context [] ctx)) n = Some argd ->
      decl_type argd = mkApps (tInd ind u) args ->
      ∑ Δ na u' l' B,
        [× red Σ Γ T (it_mkProd_or_LetIn (vass na (mkApps (tInd ind u') l') :: Δ) B),
           assumption_context Δ & #|Δ| = n].
  Proof.
    induction ctx as [|d ctx0 IH] using ctx_length_rev_ind.
    { intros n argd Γ T concl ind u args _ _ hnth. cbn in hnth. now rewrite nth_error_nil in hnth. }
    intros n argd Γ T concl ind u args isT hT hnth hargd.
    pose proof (wfE_ClosedBodies Σ (wfΣ := wfΣ)) as cbΣ.
    rewrite it_mkProd_or_LetIn_app in hT.
    destruct d as [na [b|] A].
    - (* a let-in of the witness: zeta on the witness side *)
      have hT1 : ws_cumul_pbE Conv Σ Γ T (tLetIn na b A (it_mkProd_or_LetIn ctx0 concl)) := hT.
      pose proof (ws_cumul_pbE_red_r_inv (wfΣ := cbΣ) _ hT1
        (red1_red _ _ _ _ (red_zeta _ _ na b A (it_mkProd_or_LetIn ctx0 concl)))) as hT'.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in hT'.
      rewrite smash_context_app_def in hnth.
      eapply (IH (subst_context [b] 0 ctx0)); tea.
      now rewrite subst_context_length.
    - (* an assumption: T8 [Prod_r] at [Conv] *)
      have hT1 : ws_cumul_pbE Conv Σ Γ T (tProd na A (it_mkProd_or_LetIn ctx0 concl)) := hT.
      destruct isT as (_ & s & tyT & _).
      destruct (T8_Prod_r_plug _ Σ Γ Conv T na A (it_mkProd_or_LetIn ctx0 concl) s wfΣ tyT hT1)
        as (na' & A' & B' & [r ena hA hB]).
      assert (isP : isTypeE Σ Γ (tProd na' A' B')) by exact (isType_redE (has_sort_isTypeE _ tyT) (clrel_rel r)).
      destruct (fst (isType_tProdE (wfΣ := wfΣ)) isP) as [isA' isB'].
      rewrite smash_context_app_ass List.rev_app_distr in hnth.
      destruct n as [|m]; cbn in hnth.
      + (* the recursive argument: T8 [Ind_r] at [Conv] on the typed domain *)
        noconf hnth. cbn in hargd. subst A.
        destruct isA' as (_ & sA & tyA' & _).
        destruct (T8_Ind_r_plug _ Σ Γ Conv A' ind u args sA wfΣ tyA' hA) as (u' & l' & [rA _ _]).
        exists [], na', u', l', B'. split; [|constructor|reflexivity].
        eapply red_trans; [exact (clrel_rel r)|].
        apply red_prod_l. exact (clrel_rel rA).
      + (* a later argument: move the codomain comparison into the reduct's context *)
        pose proof (wsE_ctx hT1) as clΓ.
        pose proof (ws_cumul_ctx_pbE_vass clΓ (eq_binder_annot_sym _ _ ena) (ws_cumul_pbE_sym_pb hA)) as hctx.
        pose proof (ws_cumul_pbE_ws_cumul_ctx (wfΣ := cbΣ) hctx hB) as hB'.
        destruct (IH ctx0 (le_n _) m argd (Γ ,, vass na' A') B' concl ind u args isB' hB' hnth hargd)
          as (Δ & na1 & u' & l' & B1 & [r1 ass len]).
        exists (Δ ++ [vass na' A']), na1, u', l', B1. split.
        * eapply red_trans; [exact (clrel_rel r)|].
          rewrite app_comm_cons it_mkProd_or_LetIn_app.
          apply red_prod_r. exact r1.
        * apply assumption_context_app_inv; [exact ass|repeat constructor].
        * rewrite List.length_app len /=. lia.
  Qed.

  (** The cofixpoint check: the conclusion of the telescope. *)
  Lemma red_cofix_witnessE ctx :
    forall Γ T ind u args,
      isTypeE Σ Γ T ->
      ws_cumul_pbE Conv Σ Γ T (it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args)) ->
      ∑ Δ u' l', red Σ Γ T (it_mkProd_or_LetIn Δ (mkApps (tInd ind u') l')).
  Proof.
    induction ctx as [|d ctx0 IH] using ctx_length_rev_ind.
    { intros Γ T ind u args isT hT. cbn in hT.
      destruct isT as (_ & s & tyT & _).
      destruct (T8_Ind_r_plug _ Σ Γ Conv T ind u args s wfΣ tyT hT) as (u' & l' & [r _ _]).
      exists [], u', l'. exact (clrel_rel r). }
    intros Γ T ind u args isT hT.
    pose proof (wfE_ClosedBodies Σ (wfΣ := wfΣ)) as cbΣ.
    rewrite it_mkProd_or_LetIn_app in hT.
    destruct d as [na [b|] A].
    - have hT1 : ws_cumul_pbE Conv Σ Γ T (tLetIn na b A (it_mkProd_or_LetIn ctx0 (mkApps (tInd ind u) args))) := hT.
      pose proof (ws_cumul_pbE_red_r_inv (wfΣ := cbΣ) _ hT1
        (red1_red _ _ _ _ (red_zeta _ _ na b A (it_mkProd_or_LetIn ctx0 (mkApps (tInd ind u) args))))) as hT'.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps in hT'.
      cbn [subst] in hT'.
      eapply (IH (subst_context [b] 0 ctx0)); tea.
      now rewrite subst_context_length.
    - have hT1 : ws_cumul_pbE Conv Σ Γ T (tProd na A (it_mkProd_or_LetIn ctx0 (mkApps (tInd ind u) args))) := hT.
      destruct isT as (_ & s & tyT & _).
      destruct (T8_Prod_r_plug _ Σ Γ Conv T na A (it_mkProd_or_LetIn ctx0 (mkApps (tInd ind u) args)) s wfΣ tyT hT1)
        as (na' & A' & B' & [r ena hA hB]).
      assert (isP : isTypeE Σ Γ (tProd na' A' B')) by exact (isType_redE (has_sort_isTypeE _ tyT) (clrel_rel r)).
      destruct (fst (isType_tProdE (wfΣ := wfΣ)) isP) as [isA' isB'].
      pose proof (wsE_ctx hT1) as clΓ.
      pose proof (ws_cumul_ctx_pbE_vass clΓ (eq_binder_annot_sym _ _ ena) (ws_cumul_pbE_sym_pb hA)) as hctx.
      pose proof (ws_cumul_pbE_ws_cumul_ctx (wfΣ := cbΣ) hctx hB) as hB'.
      destruct (IH ctx0 (le_n _) (Γ ,, vass na' A') B' ind u args isB' hB') as (Δ & u' & l' & r1).
      exists (Δ ++ [vass na' A']), u', l'.
      eapply red_trans; [exact (clrel_rel r)|].
      rewrite it_mkProd_or_LetIn_app.
      apply red_prod_r. exact r1.
  Qed.

  (** Base [mfix_body_on_conv_red] ([PCUICFixWitness.v:206]) at [check_one_fix]. *)
  Lemma mfix_body_on_conv_redE_fix {Γ mind d} :
    wf_localE Σ Γ -> isTypeE Σ Γ (dtype d) ->
    mfix_body_on check_one_fix (conv_witnessE Σ Γ) mind d ->
    mfix_body_on check_one_fix (red Σ Γ) mind d.
  Proof.
    intros wfΓ isty [ty [hc [opty cv]]].
    destruct (check_one_fix_inv _ _ _ hc)
      as (ctx & concl & argd & k & u & args & decomp & hnth & dapp).
    pose proof (decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp) as eqty; cbn in eqty.
    have ws : ws_cumul_pbE Conv Σ Γ (dtype d) ty.
    { exact (into_ws_cumul_pbE_spec (wfΣ := wfE_ClosedBodies Σ) cv (wf_local_closed_contextE wfΓ)
               (PCUICClosedTypEta.isType_is_open_termE isty) opty). }
    rewrite eqty in ws.
    destruct (red_fix_witnessE ctx (rarg d) argd Γ (dtype d) concl _ u args isty ws hnth dapp)
      as (Δ & na & u' & l' & B & [r ass len]).
    eexists; split; [|exact r].
    exact (check_one_fix_it_mkProd_ass (dname d) (dbody d) (rarg d) na _ u' l' Δ B ass len).
  Qed.

  (** Base [mfix_body_on_conv_red] ([PCUICFixWitness.v:206]) at [check_one_cofix]. *)
  Lemma mfix_body_on_conv_redE_cofix {Γ mind d} :
    wf_localE Σ Γ -> isTypeE Σ Γ (dtype d) ->
    mfix_body_on check_one_cofix (conv_witnessE Σ Γ) mind d ->
    mfix_body_on check_one_cofix (red Σ Γ) mind d.
  Proof.
    intros wfΓ isty [ty [hc [opty cv]]].
    destruct (check_one_cofix_inv _ _ _ hc) as [ctx [k [u [args ->]]]].
    pose proof (into_ws_cumul_pbE_spec (wfΣ := wfE_ClosedBodies Σ) cv (wf_local_closed_contextE wfΓ)
      (PCUICClosedTypEta.isType_is_open_termE isty) opty) as ws.
    destruct (red_cofix_witnessE ctx Γ (dtype d) _ u args isty ws) as (Δ & u' & l' & r).
    eexists; split; [|exact r].
    exact (check_one_cofix_it_mkProd (d := d) (ctx := Δ) (i := {| inductive_mind := mind; inductive_ind := k |})
             (u := u') (l := l')).
  Qed.

  (** Base [mfix_on_ind_conv_red] ([PCUICFixWitness.v:217]) at [check_one_fix]. *)
  Lemma mfix_on_ind_conv_redE_fix {ok Γ mfix} :
    wf_localE Σ Γ -> All (fun d => isTypeE Σ Γ (dtype d)) mfix ->
    mfix_on_ind check_one_fix (conv_witnessE Σ Γ) ok mfix ->
    mfix_on_ind check_one_fix (red Σ Γ) ok mfix.
  Proof.
    intros wfΓ alltys. apply mfix_on_ind_All2; [|easy].
    apply All_All2_refl. eapply All_impl; tea. intros d isty m.
    now apply mfix_body_on_conv_redE_fix.
  Qed.

  (** Base [mfix_on_ind_conv_red] ([PCUICFixWitness.v:217]) at [check_one_cofix]. *)
  Lemma mfix_on_ind_conv_redE_cofix {ok Γ mfix} :
    wf_localE Σ Γ -> All (fun d => isTypeE Σ Γ (dtype d)) mfix ->
    mfix_on_ind check_one_cofix (conv_witnessE Σ Γ) ok mfix ->
    mfix_on_ind check_one_cofix (red Σ Γ) ok mfix.
  Proof.
    intros wfΓ alltys. apply mfix_on_ind_All2; [|easy].
    apply All_All2_refl. eapply All_impl; tea. intros d isty m.
    now apply mfix_body_on_conv_redE_cofix.
  Qed.

  (** [wf_fixpointE] (conversion witness) ⇒ [wf_fixpoint_red] (reduction witness), for typed
      declared types. *)
  Lemma wf_fixpointE_wf_fixpoint_red {Γ mfix} :
    wf_localE Σ Γ -> All (fun d => isTypeE Σ Γ (dtype d)) mfix ->
    wf_fixpointE Σ Γ mfix -> wf_fixpoint_red Σ Γ mfix.
  Proof.
    intros wfΓ alltys [isl [hr hm]].
    split; [exact isl|split; [exact hr|]].
    now eapply mfix_on_ind_conv_redE_fix.
  Qed.

  Lemma wf_cofixpointE_wf_cofixpoint_red {Γ mfix} :
    wf_localE Σ Γ -> All (fun d => isTypeE Σ Γ (dtype d)) mfix ->
    wf_cofixpointE Σ Γ mfix -> wf_cofixpoint_red Σ Γ mfix.
  Proof.
    intros wfΓ alltys h.
    now eapply mfix_on_ind_conv_redE_cofix.
  Qed.

End FixWitnessE.

(** The projection context is closed. *)
Lemma is_closed_projection_contextE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {p mdecl idecl cdecl pdecl} v :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  is_closed_context (projection_context p.(proj_ind) mdecl idecl v).
Proof.
  intros isdecl. rewrite /projection_context.
  apply on_free_vars_ctx_snoc_ass.
  - apply on_free_vars_ctx_smash; [|reflexivity].
    rewrite on_free_vars_ctx_subst_instance -is_closed_ctx_closedE.
    exact (declared_inductive_closed_paramsE (proj1 (proj1 isdecl))).
  - rewrite on_free_vars_mkApps /=. apply on_free_vars_to_extended_list.
Qed.

(** The substitution [c :: rev args] of a projection, untyped. *)
Lemma untyped_subslet_projection_contextE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ p mdecl idecl cdecl pdecl c args} v :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  #|args| = ind_npars mdecl ->
  untyped_subslet Γ (c :: List.rev args) (projection_context p.(proj_ind) mdecl idecl v).
Proof.
  intros isdecl hlen.
  apply untyped_subslet_assumption_context.
  - rewrite /projection_context. constructor.
    apply smash_context_assumption_context. constructor.
  - rewrite /projection_context /= List.length_rev smash_context_length /=
      context_assumptions_subst_instance hlen.
    now rewrite (declared_minductive_ind_nparsE (proj1 (proj1 (proj1 isdecl)))).
Qed.

Section BDFromPCUICE.

(** The big theorem*)
Lemma bidirectional_from_pcuicE `{checker_flags} :
      env_propE (fun Σ Γ t T => {T' & Σ ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ T})
        (fun Σ Γ j => lift_sorting (fun t T => Σ ;;; Γ |-E t ◃ T) (fun T u => ∑ u', Σ ;;; Γ |-E T ▹□ u' × leq_sort Σ u' u) j)
        (fun Σ Γ => wf_local_bdE Σ Γ).
Proof.
  apply typingE_ind_env.

  { intros Σ wfΣ Γ j Hj.
    apply lift_sorting_impl with (1 := Hj) => //.
    - intros t T []. now apply conv_checkE.
    - intros t u [HT0 HT1].
      eapply conv_infer_sortE. all: done. }

  all: intros Σ wfΣ Γ wfΓ.

  - intros _ bdwfΓ.
    clear wfΓ.
    apply All_local_env_impl_gen with (1 := bdwfΓ). clear Γ bdwfΓ.
    intros ??.
    apply conv_lift_judgmentE with (na := decl.(decl_name)).

  - intros n decl hnth _.
    eexists.
    split.
    2: exact (typing_ws_cumul_pbE Σ wfΣ Cumul Γ _ _ (typeE_Rel _ _ n decl wfΓ hnth)).
    constructor.
    eassumption.

  - intros u _ hu.
    eexists.
    split.
    2: exact (typing_ws_cumul_pbE Σ wfΣ Cumul Γ _ _ (typeE_Sort _ _ u wfΓ hu)).
    constructor.
    assumption.

  - intros na A B ? ? ? ? CumA ? CumB.
    apply conv_lift_judgment_univE with (na := na) in CumA as (?&?&?).
    apply conv_infer_sortE in CumB ; auto.
    destruct CumB as (?&?&?).
    eexists.
    split.
    + constructor ; eassumption.
    + apply ws_cumul_pbE_Sort.
      1: exact (wf_local_closed_contextE wfΓ).
      cbn. apply leq_sort_product_mon.
      all: assumption.

  - intros na A t ? ? hA CumA ? (?&?&?).
    apply conv_lift_judgmentE with (na := na) in CumA.
    eexists.
    split.
    + econstructor. all: eassumption.
    + apply ws_cumul_pbE_Prod; [reflexivity| |assumption].
      eapply isType_ws_cumul_pbE_refl.
      exact (isTypeRelE_isTypeE _ _ _ _ hA).

  - intros na t A ? ? ? ? CumtA ? (?&?&?).
    apply conv_lift_judgmentE with (na := na) in CumtA.
    eexists.
    split.
    + econstructor.
      all: eassumption.
    + apply ws_cumul_pbE_LetIn_bo_pb.
      eassumption.

  - intros t na A B u ? ? ? ? tyt Cumt tyu (?&?&?).
    apply conv_infer_prodE in Cumt ; auto.
    destruct Cumt as (?&?&?&[]).
    eexists.
    split.
    + econstructor ; eauto.
      econstructor ; eauto.
      apply ws_cumul_pbE_forget.
      etransitivity ; tea.
      now apply ws_cumul_pbE_sym_pb.
    + eapply substitution0_ws_cumul_pbE ; tea.
      exact (subject_is_open_termE tyu).

  - intros.
    eexists.
    split.
    1: econstructor ; tea.
    apply ws_cumul_pbE_refl.
    1: exact (wf_local_closed_contextE wfΓ).
    rewrite on_free_vars_subst_instance.
    now eapply closed_on_free_vars, declared_constant_closed_typeE.

  - intros.
    eexists.
    split.
    1: econstructor ; tea.
    apply ws_cumul_pbE_refl.
    1: exact (wf_local_closed_contextE wfΓ).
    rewrite on_free_vars_subst_instance.
    now eapply closed_on_free_vars, declared_inductive_closed_typeE.

  - intros.
    eexists.
    split.
    1: econstructor ; tea.
    apply ws_cumul_pbE_refl.
    1: exact (wf_local_closed_contextE wfΓ).
    now eapply closed_on_free_vars, declared_constructor_closed_typeE.

  - intros ci p c brs indices ps mdecl idecl isdecl wfΣ' wfbΓ epar ? predctx wfpred ? wfpctx ty_p Cump ? ? Her Hinst ty_c Cumc ? ? ? ty_br.

    apply conv_infer_sortE in Cump as (ps'&hps&hle) ; auto.
    apply conv_infer_indE in Cumc as (ui'&args'&[hci hcmp hargs]) ; auto.
    eexists.
    split.
    + econstructor.
      all: tea.
      * by eapply All_local_app_rel.
      * eapply is_allowed_elimination_monotone.
        all: eassumption.
      * eapply geq_relevance; eassumption.
      * rewrite subst_instance_app_ctx rev_app_distr in Hinst.
        replace (pparams p) with (firstn (context_assumptions (List.rev (subst_instance (puinst p)(ind_params mdecl)))) (pparams p ++ indices)).
        eapply BDFromPCUIC.ctx_inst_app_impl ; tea.
        1: intros ?? [] ; by apply conv_checkE.
        rewrite context_assumptions_rev context_assumptions_subst_instance.
        rewrite -(declared_minductive_ind_nparsE (proj1 isdecl)).
        rewrite firstn_app_left //.
        now destruct wfpred.

      * replace #|args'| with #|pparams p ++ indices|.
        1: assumption.
        symmetry.
        eapply All2_length.
        eassumption.
      * move: (hargs) => /All2_length alen.
        rewrite -(firstn_skipn (ci_npar ci) args') in hargs.
        eapply All2_app_inv in hargs as [].
        1: now eapply All2_impl ; tea ; intros ; eapply ws_cumul_pbE_forget.
        rewrite -epar ; destruct wfpred as [->].
        apply BDFromPCUIC.ctx_inst_length in Hinst; tea.
        move: alen.
        rewrite Hinst context_assumptions_rev context_assumptions_subst_instance
          context_assumptions_app -(declared_minductive_ind_nparsE (proj1 isdecl)) => alen.
        rewrite firstn_length_le.
        all: lia.

      * eapply All2i_impl.
        1: eassumption.
        intros j cdecl br (?&Hbr).
        split ; [assumption|..].
        intros brctxty.
        fold predctx in brctxty.
        fold ptm in brctxty.
        fold brctxty in Hbr.
        destruct Hbr as (?&(?&Cumbody)&?&?&?).
        apply conv_checkE in Cumbody ; auto.
        split ; auto.
        by apply All_local_app_rel.

    + pose proof (wf_local_closed_contextE wfΓ) as clΓ.
      pose proof (wf_local_closed_contextE wfpctx) as clpctx.
      apply ws_cumul_pbE_mkApps ; auto.
      * apply (ws_cumul_pbE_it_mkLambda_or_LetIn (cbΣ := wfE_ClosedBodies Σ)).
        -- exact (ws_cumul_ctx_pbE_refl (Σ := Σ) _ clpctx).
        -- apply ws_cumul_pbE_refl.
           1: exact clpctx.
           exact (subject_is_open_termE ty_p).
      * apply All2_app.
        -- replace indices with (skipn (ci_npar ci) (pparams p ++ indices)).
           2: by apply skipn_all_app_eq ; rewrite <- epar ; destruct wfpred as [->].
           by apply All2_skipn.
        -- constructor ; auto.
           apply ws_cumul_pbE_refl.
           1: exact clΓ.
           exact (subject_is_open_termE ty_c).

  - intros p c u mdecl idecl cdecl pdecl isdecl args ? ? ty_c Cumc hlen.
    apply conv_infer_indE in Cumc as (ui'&args'&[hi hcmp hargs]) ; auto.
    eexists.
    split.
    + econstructor.
      1-2: eassumption.
      etransitivity.
      2: eassumption.
      eapply All2_length.
      eassumption.

    + assert (ty_c' : Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) ui') args')
        by exact (infering_ind_typingE _ _ _ _ _ _ wfΣ wfΓ hi).
      have decli : declared_inductive Σ p.(proj_ind) mdecl idecl := proj1 (proj1 isdecl).
      have cu : consistent_instance_ext Σ (ind_universes mdecl) u.
      { destruct (isType_mkApps_Ind_invE wfΣ decli wfΓ (validityE ty_c)) as (? & ? & hs).
        cbv zeta in hs. now destruct hs. }
      have cu' : consistent_instance_ext Σ (ind_universes mdecl) ui'.
      { destruct (isType_mkApps_Ind_invE wfΣ decli wfΓ (validityE ty_c')) as (? & ? & hs).
        cbv zeta in hs. now destruct hs. }
      have hlen' : #|args'| = ind_npars mdecl by rewrite (All2_length hargs).
      pose proof (wf_local_closed_contextE wfΓ) as clΓ.
      have onud : on_udecl_prop Σ (ind_universes mdecl).
      { unshelve eapply declared_projection_to_gen in isdecl; eauto.
        eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl _)); eauto.
        apply isdecl. }
      have hcmp' : cmp_ind_universes Σ p.(proj_ind) (ind_npars mdecl) ui' u by rewrite -hlen.
      exact (substitution_ws_cumul_pbE_subst_conv (wfΣ := wfE_ClosedBodies Σ) (Δ := [])
        (untyped_subslet_projection_contextE ui' isdecl hlen')
        (untyped_subslet_projection_contextE u isdecl hlen)
        (All2_cons (ws_cumul_pbE_refl clΓ (subject_is_open_termE ty_c)) (All2_rev _ _ _ _ _ hargs))
        (is_closed_context_weaken _ _ clΓ (is_closed_projection_contextE u isdecl))
        (weaken_ws_cumul_pbE (wfΣ := wfE_ClosedBodies Σ) Γ clΓ
          (projection_cumulative_indicesE isdecl onud cu' cu hcmp'))).

  - intros mfix n decl types ? ? ? Htypes Alltypes Hbodies Allbodies wffix.
    eexists.
    split.
    2:{
      apply isType_ws_cumul_pbE_refl.
      eapply isTypeRelE_isTypeE.
      eapply nth_error_all in Htypes as Hj ; tea.
    }
    constructor ; eauto.
    + apply (All_impl Alltypes) => d. apply conv_lift_judgmentE with (na := d.(dname)).
    + apply (All_impl Allbodies) => d. apply conv_lift_judgmentE with (na := d.(dname)).
    + eapply wf_fixpointE_wf_fixpoint_red; tea.
      apply (All_impl Htypes) => d Hj.
      now eapply isTypeRelE_isTypeE.

  - intros mfix n decl types ? ? ? Htypes Alltypes Hbodies Allbodies wfcofix.
    eexists.
    split.
    2:{
      apply isType_ws_cumul_pbE_refl.
      eapply isTypeRelE_isTypeE.
      eapply nth_error_all in Htypes as Hj ; tea.
    }
    constructor ; eauto.
    + apply (All_impl Alltypes) => d. apply conv_lift_judgmentE with (na := d.(dname)).
    + apply (All_impl Allbodies) => d. apply conv_lift_judgmentE with (na := d.(dname)).
    + eapply wf_cofixpointE_wf_cofixpoint_red; tea.
      apply (All_impl Htypes) => d Hj.
      now eapply isTypeRelE_isTypeE.

  - intros p prim_ty cdecl wfΓ' hp hdecl pinv X X0.
    eexists. split; [econstructor; tea|].
    destruct X0. 1-3:constructor; eauto.
    eapply conv_checkE in hty; tea.
    eapply conv_checkE in hdef; tea.
    constructor; eauto. solve_all.
    now eapply conv_checkE in X0.
    apply ws_cumul_pbE_refl.
    1: exact (wf_local_closed_contextE wfΓ).
    depelim X; cbn => //.
    simp prim_type. cbn.
    now eapply subject_is_open_termE.

  - intros ? ? ? ? ? ? (?&?&?) tyB (?&?&?) cum.
    eexists.
    split.
    1: eassumption.
    etransitivity ; eauto.
    apply (into_ws_cumul_pbE_spec (wfΣ := wfE_ClosedBodies Σ) cum (wf_local_closed_contextE wfΓ)).
    + now eapply type_is_open_termE.
    + now eapply subject_is_open_termE.
Qed.

End BDFromPCUICE.

(** The direct consequence on typing *)

(** Base [typing_infering] ([BDFromPCUIC.v:399]). *)
Lemma typing_inferingE `{checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T} :
  Σ ;;; Γ |-E t : T -> ∑ T', Σ ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ T.
Proof.
  intros.
  apply bidirectional_from_pcuicE.
  all: assumption.
Qed.

(** Base [typing_checking] ([BDFromPCUIC.v:407]). *)
Lemma typing_checkingE `{checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T} :
  Σ ;;; Γ |-E t : T -> Σ ;;; Γ |-E t ◃ T.
Proof.
  move => /typing_inferingE [T' [? ?]].
  econstructor ; tea.
  now apply ws_cumul_pbE_forget.
Qed.

(** Base [typing_infering_sort] ([BDFromPCUIC.v:415]). *)
Lemma typing_infering_sortE `{checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t u} :
  Σ ;;; Γ |-E t : tSort u -> ∑ u', Σ ;;; Γ |-E t ▹□ u' × leq_sort Σ u' u.
Proof.
  intros.
  apply conv_infer_sortE ; tea.
  now apply typing_inferingE.
Qed.

(** Base [lift_typing_lift_sorting] ([BDFromPCUIC.v:423]). *)
Lemma lift_typing_lift_sortingE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ} {tm ty rel} :
  lift_typing typingE Σ Γ (Judge tm ty None rel) -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (Judge tm ty None rel).
Proof.
  intro Hj.
  apply lift_sorting_ex_it_impl_gen with Hj.
  - destruct tm => //. apply typing_checkingE.
  - intros Hty Her.
    eapply typing_infering_sortE in Hty as [? []]; tea.
    eexists; split; tea. destruct rel as [rel|] => //=.
    now eapply geq_relevance; tea.
Qed.

(** Base [isType_infering_sort] ([BDFromPCUIC.v:435]). *)
Lemma isType_infering_sortE `{checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t} :
  isTypeE Σ Γ t -> ∑ u', Σ ;;; Γ |-E t ▹□ u'.
Proof.
  move/lift_typing_lift_sortingE.
  intros (_ & s & ty & _).
  now eexists.
Qed.

(** Base [isTypeRel_infering_sort] ([BDFromPCUIC.v:443]). *)
Theorem isTypeRel_infering_sortE `{checker_flags} (Σ : global_env_ext) Γ t r (wfΣ : wfE Σ) :
  isTypeRelE Σ Γ t r -> ∑ u, Σ ;;; Γ |-E t ▹□ u × relevance_of_sort u = r.
Proof.
  move/lift_typing_lift_sortingE.
  intros (_ & s & ty & _ & Her).
  now eexists; split; tea.
Qed.

(** Base [typing_infer_prod] ([BDFromPCUIC.v:451]). *)
Lemma typing_infer_prodE `{checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t na A B} :
  Σ ;;; Γ |-E t : tProd na A B ->
  ∑ na' A' B', [× Σ ;;; Γ |-E t ▹Π (na',A',B'),
    eq_binder_annot na na', Σ ;;; Γ ⊢E A' = A & Σ ;;; Γ ,, vass na A ⊢E B' ≤ B].
Proof.
  intros.
  apply conv_infer_prodE ; tea.
  now apply typing_inferingE.
Qed.

(** Base [typing_infer_ind] ([BDFromPCUIC.v:461]). *)
Lemma typing_infer_indE `{checker_flags} Σ (wfΣ : wfE Σ) Γ t ind ui args :
  Σ ;;; Γ |-E t : mkApps (tInd ind ui) args ->
  ∑ ui' args', [× Σ ;;; Γ |-E t ▹{ind} (ui',args'),
      cmp_ind_universes Σ ind #|args| ui' ui
      & ws_cumul_pbE_terms Σ Γ args' args].
Proof.
  intros.
  apply conv_infer_indE ; tea.
  now apply typing_inferingE.
Qed.

(** Base [wf_local_wf_local_bd] ([BDFromPCUIC.v:472]). *)
Lemma wf_local_wf_local_bdE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ} :
  wf_localE Σ Γ ->
  wf_local_bdE Σ Γ.
Proof.
  intros.
  eapply bidirectional_from_pcuicE ; tea.
  now eapply typeE_Prop_wf.
Qed.

(** Base [wf_local_rel_wf_local_bd] ([BDFromPCUIC.v:481]). *)
Lemma wf_local_rel_wf_local_bdE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ Γ'} :
  wf_local_relE Σ Γ Γ' ->
  wf_local_bd_relE Σ Γ Γ'.
Proof.
  intros wfΓ'.
  apply All_local_env_impl_gen with (1 := wfΓ'); clear Γ' wfΓ'.
  intros Γ' ? Hj.
  apply lift_sorting_ex_it_impl_gen with Hj => //.
  - destruct decl_body => //= Hb. now apply typing_checkingE.
  - intros Hty Her. eapply typing_infering_sortE in Hty as [? []]; tea. eexists; split; tea. eapply geq_relevance; tea.
Qed.

(** Base [ctx_inst_typing_bd] ([BDFromPCUIC.v:493]). *)
Theorem ctx_inst_typing_bdE `{checker_flags} (Σ : global_env_ext) Γ l Δ (wfΣ : wfE Σ) :
  ctx_instE Σ Γ l Δ ->
  PCUICTyping.ctx_inst (checkingE Σ) Γ l Δ.
Proof.
  intros inl.
  induction inl.
  all: constructor ; tea.
  now apply typing_checkingE.
Qed.

(** ** The checker's [T6BDc_facts]

  Each statement is the field's text, verbatim, from [safechecker/theories/PCUICTypingEtaHyps.v]
  ([wip/etak-k7-2026-10-29] @ [7818e65b], blob [990d9532], lines 192-205); the body is the
  lemma above. Every field has base's statement with the relations renamed, so no field
  differs from its base twin. *)

Definition T6BDc_ctx_inst_typing_bd_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (l : list term) (Δ : context) (wfΣ : wfE Σ), ctx_instE Σ Γ l Δ -> PCUICTyping.ctx_inst (checkingE Σ) Γ l Δ
  := @ctx_inst_typing_bdE cf.

Definition T6BDc_lift_typing_lift_sorting_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {tm : option term} {ty : term} {rel : option relevance}, lift_typing typingE Σ Γ (Judge tm ty None rel) -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (Judge tm ty None rel)
  := @lift_typing_lift_sortingE cf.

Definition T6BDc_typing_checking_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> Σ;;; Γ |-E t ◃ T
  := @typing_checkingE cf.

Definition T6BDc_typing_infering_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> ∑ T' : term, Σ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ T
  := @typing_inferingE cf.

Definition T6BDc_typing_infering_sort_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {u : sort}, Σ;;; Γ |-E t : tSort u -> ∑ u' : sort, Σ;;; Γ |-E t ▹□ u' × leq_sort Σ u' u
  := @typing_infering_sortE cf.

Definition T6BDc_wf_local_rel_wf_local_bd_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : list context_decl} {Γ' : context}, wf_local_relE Σ Γ Γ' -> wf_local_bd_relE Σ Γ Γ'
  := @wf_local_rel_wf_local_bdE cf.

End BDFromPCUICEta.
