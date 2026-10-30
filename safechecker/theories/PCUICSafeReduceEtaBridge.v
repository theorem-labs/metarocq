(* Distributed under the terms of the MIT license. *)
(** * The bridge from the E conversion to the reduction machine (plan I7 rev 14 B3)

  The E conversion ([PCUICSafeConversionEta]) works on the η stack of
  [PCUICPositionEta]; the reduction machine ([PCUICSafeReduceEta]) keeps base
  [PCUICPosition]'s stack (rev 14: the stack type is pinned there). Every one of the
  11 [reduce_stack] call sites of the conversion passes an [App_l]-only stack
  ([appstack (decompose_stack _).1 []] or [[]], [lanes/eta/k3-guard-probe.md]), so the
  conversion calls the machine through [reduce_args_E], whose input is a list of
  arguments: the boundary invariant [app_only] holds by construction
  ([app_only_appstack]) and is kept ([reduce_stack_app_only]).

  This file instantiates the machine at [wt := welltypedE] and [wfP := wf_extE].
  - [reduce_env_facts_E : ReduceEnvFacts welltypedE wf_extE] is PROVED here, from the
    E metatheory already on [frac/eta] ([wfE_ClosedBodies], [typing_closed_contextE],
    [subject_is_open_termE], and [prim_op_readback_on_global_env], which holds for any
    [on_global_env]).
  - [ReduceTypedFacts welltypedE wf_extE] is BUILT here ([reduce_typed_facts_E]) from the
    smaller class [ReduceTypedFactsE], the ONE named hypothesis of the section [BridgeE]
    below ([reduce_factsE]), and the six fields proved in [PCUICEtaTypedFactsProved].
  The positions of the two stack files are different types ([PCUICPositionEta] has
  its own [choice]); [stack_position_appstack_bridge] relates their orders. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICPosition
     PCUICNormal PCUICReduction PCUICSafeLemmata PCUICWellScopedCumulativity
     PCUICConversion PCUICClosedBodies PCUICTypingEta PCUICSN PCUICClosedTypEta
     PCUICEquality PCUICCumulativitySpec PCUICArityRed.
From MetaRocq.PCUIC Require PCUICPositionEta.
From MetaRocq.PCUIC Require PCUICCumulativitySpecEtaClosureInstances PCUICEtaA6Instances.
From MetaRocq.SafeChecker Require Import PCUICWfReductionEta PCUICSafeReduceEta PCUICWfEnvEta.
(* The six proved fields of [ReduceTypedFacts] at [welltypedE] (qualified names; nothing imported). *)
From MetaRocq.SafeChecker Require PCUICEtaTypedFactsProved.

(** ** The boundary invariant: every stack crossing the boundary is [App_l]-only *)

Definition app_only (π : PCUICPosition.stack) : Prop :=
  snd (PCUICPosition.decompose_stack π) = [].

Lemma app_only_appstack (args : list term) : app_only (PCUICPosition.appstack args []).
Proof.
  unfold app_only. rewrite PCUICPosition.decompose_stack_appstack. reflexivity.
Qed.

Lemma app_only_zip t π : app_only π ->
  PCUICPosition.zip (t, π) = mkApps t (fst (PCUICPosition.decompose_stack π)).
Proof.
  unfold app_only. intros h.
  destruct (PCUICPosition.decompose_stack π) as [l ρ] eqn:e. cbn in h |- *. subst ρ.
  apply PCUICPosition.decompose_stack_eq in e. subst π.
  unfold PCUICPosition.zip. cbn. rewrite PCUICPosition.zipc_appstack. reflexivity.
Qed.

(** ** The [App_l]-only stacks of the two position files agree *)

Lemma positionR_repeat_app_l_base n m :
  PCUICPosition.positionR (repeat PCUICPosition.app_l n) (repeat PCUICPosition.app_l m)
  <-> (m < n)%nat.
Proof.
  split.
  - induction n as [|n ih] in m |- *; intros h.
    + cbn in h. inversion h.
    + destruct m as [|m]; [lia|].
      cbn in h. inversion h; subst; clear h.
      match goal with H : PCUICPosition.positionR _ _ |- _ => apply ih in H end.
      lia.
  - induction n as [|n ih] in m |- *; intros h; [lia|].
    destruct m as [|m]; cbn.
    + constructor.
    + constructor. apply ih. lia.
Qed.

Lemma positionR_repeat_app_l_eta n m :
  PCUICPositionEta.positionR (repeat PCUICPositionEta.app_l n) (repeat PCUICPositionEta.app_l m)
  <-> (m < n)%nat.
Proof.
  split.
  - induction n as [|n ih] in m |- *; intros h.
    + cbn in h. inversion h.
    + destruct m as [|m]; [lia|].
      cbn in h. inversion h; subst; clear h.
      match goal with H : PCUICPositionEta.positionR _ _ |- _ => apply ih in H end.
      lia.
  - induction n as [|n ih] in m |- *; intros h; [lia|].
    destruct m as [|m]; cbn.
    + constructor.
    + constructor. apply ih. lia.
Qed.

(** STATEMENT CHANGE (approved by the lane lead, 2026-10-29). Plan I7 rev 12
    ([plan.md:651-653]) and the rev 14 B3 table state
    [stack_position_appstack_bridge] as an equation between the two [stack_position]s.
    That statement is ILL-TYPED for every [args]: [PCUICPositionEta] defines its own
    [Inductive choice] and [position := list choice], so the two sides have the
    distinct types [list PCUICPositionEta.choice] and [list PCUICPosition.choice]
    (isomorphic inductives, so no [<>] lemma can refute it). The command below
    records that the rev 14 statement does not type-check. *)
Fail Lemma stack_position_appstack_bridge_rev14 args :
  PCUICPositionEta.stack_position (PCUICPositionEta.appstack args [])
  = PCUICPosition.stack_position (PCUICPosition.appstack args []).

(** The restated bridge: the two position orders agree on [App_l]-only stacks (both
    sides hold iff [#|args| < #|args'|]). This is what [reduce_args_E_Req] needs. *)
Lemma stack_position_appstack_bridge args args' :
  PCUICPosition.positionR (PCUICPosition.stack_position (PCUICPosition.appstack args' []))
                          (PCUICPosition.stack_position (PCUICPosition.appstack args []))
  <-> PCUICPositionEta.positionR
        (PCUICPositionEta.stack_position (PCUICPositionEta.appstack args' []))
        (PCUICPositionEta.stack_position (PCUICPositionEta.appstack args [])).
Proof.
  rewrite !PCUICPosition.stack_position_appstack, !PCUICPositionEta.stack_position_appstack.
  cbn.
  split; intros h.
  - apply positionR_repeat_app_l_eta. apply positionR_repeat_app_l_base in h. exact h.
  - apply positionR_repeat_app_l_base. apply positionR_repeat_app_l_eta in h. exact h.
Qed.

Lemma stack_context_appstack_bridge args :
  PCUICPositionEta.stack_context (PCUICPositionEta.appstack args []) = []
  /\ PCUICPosition.stack_context (PCUICPosition.appstack args []) = [].
Proof.
  split.
  - rewrite PCUICPositionEta.stack_context_appstack. reflexivity.
  - rewrite PCUICPosition.stack_context_appstack. reflexivity.
Qed.

Lemma zipp_appstack_bridge t args :
  PCUICPosition.zipp t (PCUICPosition.appstack args [])
  = PCUICPositionEta.zipp t (PCUICPositionEta.appstack args []).
Proof.
  unfold PCUICPosition.zipp, PCUICPositionEta.zipp.
  rewrite PCUICPosition.decompose_stack_appstack, PCUICPositionEta.decompose_stack_appstack.
  cbn. rewrite !app_nil_r. reflexivity.
Qed.

(** ** The E environment facts, proved *)

#[export] Instance reduce_env_facts_E {cf : checker_flags} : ReduceEnvFacts welltypedE wf_extE.
Proof.
  constructor.
  - intros Σ [wfΣ _]. sq. exact (@wfE_ClosedBodies _ Σ wfΣ).
  - intros Σ Γ t [wfΣ _] [A h]. exact (typing_closed_contextE (wfΣ := wfΣ) h).
  - intros Σ Γ t [wfΣ _] [A h]. exact (subject_is_open_termE (wfΣ := wfΣ) h).
  - intros Σ c cb op ls r [wfΣ _] hl hop hden.
    destruct (prim_op_readback_on_global_env wfΣ hl hop hden) as [v hv]. now exists v.
Qed.

(** ** The E typed facts, built from the GENUINE ones and the proved ones

    [ReduceTypedFacts welltypedE wf_extE] from the nine fields of
    [PCUICSafeReduceEta.ReduceTypedFactsE] (the named hypothesis) and the six fields proved in
    [PCUICEtaTypedFactsProved]. The kernel checks each [rtf_<f>E] against the field [rtf_<f>]
    at [welltypedE]/[wf_extE]. An instance, so the E sections find [ReduceTypedFacts
    welltypedE wf_extE] from their [ReduceTypedFactsE] hypothesis; [Qed]: opaque, as the
    section variable it replaces. *)
#[export] Instance reduce_typed_facts_E {cf : checker_flags} {G : ReduceTypedFactsE} :
  ReduceTypedFacts welltypedE wf_extE.
Proof.
  constructor.
  - exact rtf_wt_redE.
  - exact rtf_contextE.
  - exact PCUICEtaTypedFactsProved.rtf_rel_proved.
  - exact PCUICEtaTypedFactsProved.rtf_const_proved.
  - exact rtf_case_constructE.
  - exact rtf_proj_constructE.
  - exact PCUICEtaTypedFactsProved.rtf_cofix_proved.
  - exact PCUICEtaTypedFactsProved.rtf_app_sort_proved.
  - exact PCUICEtaTypedFactsProved.rtf_app_prod_proved.
  - exact PCUICEtaTypedFactsProved.rtf_app_prim_proved.
  - exact rtf_prim_overappliedE.
  - exact rtf_fix_arg_whneE.
  - exact rtf_case_arg_whneE.
  - exact rtf_proj_arg_whneE.
  - exact rtf_whnf_red_invE.
Qed.

(** ** The machine at [welltypedE], and the bridge facts *)

Section BridgeE.
  Context {cf : checker_flags} {no : normalizing_flags}.

  (** THE NAMED HYPOTHESIS of the E instantiation: the nine GENUINE typed facts of the
      machine at [welltypedE] and [wf_extE] ([PCUICSafeReduceEta.ReduceTypedFactsE], field by
      field with the plan row each waits on); the machine's [ReduceTypedFacts welltypedE
      wf_extE] is [reduce_typed_facts_E] above, from it and six proved fields. Its satisfying
      instance is [PCUICSafeReduceEta.reduce_typed_facts_base], the same statements at base
      [welltyped] and [wf_ext].
      (1) That instance shows the hypothesis is consistent and the machine is about
      something real: at [welltyped] it is the base machine. (2) It does NOT discharge
      this instantiation: subject reduction over [typingE] (plan row T1), the inversion
      and classification facts over [typingE] (row T6) and the [ClosedBodies] port
      of [whnf_red_inv] (row W-c) remain this hypothesis until those rows land.
      Not a known-false form: no field states a fixpoint or cofixpoint witness obtained
      from [conv_witnessE] (or any E-conversion witness of a head shape) under
      closedness premises only, the form refuted by ArityLane's η-expanded-domain
      witness. Every field is either a typed form (its premise is [welltypedE] of the
      term it inverts or classifies, e.g. [rtf_fix_arg_whneE] assumes the fixpoint
      application is [welltypedE]) or untyped ([rtf_whnf_red_invE], about base [red]
      only). *)
  Context {reduce_factsE : ReduceTypedFactsE}.

  Context (flags : RedFlags.t) (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** [PCUICSafeReduceEta.reduce_stack] at [welltypedE]; [None] when the fuel of the machine
      ran out ([PCUICFuelEta]). *)
  Definition reduce_stack_E (Γ : context) (t : term) (π : PCUICPosition.stack)
    (h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ (PCUICPosition.zip (t, π)))
    : option (term × PCUICPosition.stack) :=
    reduce_stack (wt := welltypedE) (wfP := wf_extE) (EF := reduce_env_facts_E)
      (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Γ t π h.

  (** The facts of [PCUICSafeReduceEta] at [welltypedE], stated over the answers of
      [reduce_stack_E]. *)
  Lemma reduce_stack_E_decompose Γ t π h r :
    reduce_stack_E Γ t π h = Some r ->
    snd (PCUICPosition.decompose_stack (snd r)) =
    snd (PCUICPosition.decompose_stack π).
  Proof using Type.
    exact (reduce_stack_decompose (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Γ t π h r).
  Qed.

  Lemma reduce_stack_E_sound Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h r :
    reduce_stack_E Γ t π h = Some r ->
    ∥ Σ ;;; Γ ⊢ PCUICPosition.zip (t, π) ⇝ PCUICPosition.zip r ∥.
  Proof using Type.
    exact (reduce_stack_sound (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Σ wfΣ Γ t π h r).
  Qed.

  Lemma reduce_stack_E_whnf Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ) r :
    reduce_stack_E Γ t π h = Some r ->
    let '(u, ρ) := r in
    ∥ whnf flags Σ (Γ ,,, PCUICPosition.stack_context ρ) (PCUICPosition.zipp u ρ) ∥.
  Proof using Type.
    exact (reduce_stack_whnf (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Γ t π h Σ wfΣ r).
  Qed.

  Lemma reduce_stack_E_isred Γ t π h r :
    RedFlags.beta flags -> reduce_stack_E Γ t π h = Some r -> isred r.
  Proof using Type.
    exact (reduce_stack_isred (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Γ t π h r).
  Qed.

  Lemma reduce_stack_E_Req Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h r :
    reduce_stack_E Γ t π h = Some r ->
    Req Σ Γ r (t, π).
  Proof using Type.
    exact (reduce_stack_Req (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Σ wfΣ Γ t π h r).
  Qed.

  Lemma reduce_stack_app_only Γ t args h r :
    reduce_stack_E Γ t (PCUICPosition.appstack args []) h = Some r ->
    app_only (snd r).
  Proof using Type.
    intros e. unfold app_only. rewrite (reduce_stack_E_decompose _ _ _ _ _ e).
    rewrite PCUICPosition.decompose_stack_appstack. reflexivity.
  Qed.

  (** The machine on an [App_l]-only stack, read as a head and its arguments; [None] when the
      fuel of the machine ran out. *)
  Definition reduce_args_E (Γ : context) (t : term) (args : list term)
    (h : forall Σ, abstract_env_ext_rel X Σ ->
           welltypedE Σ Γ (PCUICPosition.zip (t, PCUICPosition.appstack args [])))
    : option (term × list term) :=
    match reduce_stack_E Γ t (PCUICPosition.appstack args []) h with
    | Some (t', π') => Some (t', fst (PCUICPosition.decompose_stack π'))
    | None => None
    end.

  (** The machine's output on an [App_l]-only input, through [reduce_args_E]. *)
  Lemma reduce_args_E_spec Γ t args h t' args' :
    Some (t', args') = reduce_args_E Γ t args h ->
    reduce_stack_E Γ t (PCUICPosition.appstack args []) h = Some (t', PCUICPosition.appstack args' []).
  Proof using Type.
    unfold reduce_args_E.
    destruct (reduce_stack_E Γ t (PCUICPosition.appstack args []) h) as [[t0 π']|] eqn:er;
      [|discriminate].
    intros e. injection e as -> ->.
    pose proof (reduce_stack_app_only Γ t args h _ er) as ho. revert ho.
    unfold app_only. cbn [fst snd]. intros ho.
    destruct (PCUICPosition.decompose_stack π') as [l ρ] eqn:ed. cbn [fst snd] in ho |- *.
    subst ρ. apply PCUICPosition.decompose_stack_eq in ed. now subst π'.
  Qed.

  Lemma reduce_args_E_sound Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t args h t' args' :
    Some (t', args') = reduce_args_E Γ t args h ->
    ∥ Σ ;;; Γ ⊢ mkApps t args ⇝ mkApps t' args' ∥.
  Proof using Type.
    intros e.
    pose proof (reduce_stack_E_sound Σ wfΣ Γ t _ h _ (reduce_args_E_spec Γ t args h t' args' e)) as s.
    unfold PCUICPosition.zip in s. cbn [fst snd] in s.
    rewrite !PCUICPosition.zipc_appstack in s. exact s.
  Qed.

  Lemma reduce_args_E_whnf Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t args h t' args' :
    Some (t', args') = reduce_args_E Γ t args h ->
    ∥ whnf flags Σ Γ (mkApps t' args') ∥.
  Proof using Type.
    intros e.
    pose proof (reduce_stack_E_whnf Γ t _ h Σ wfΣ _ (reduce_args_E_spec Γ t args h t' args' e)) as w.
    cbn [fst snd] in w.
    rewrite PCUICPosition.stack_context_appstack in w.
    unfold PCUICPosition.zipp in w.
    rewrite PCUICPosition.decompose_stack_appstack in w. cbn [fst snd app] in w.
    rewrite app_nil_r in w. exact w.
  Qed.

  Lemma reduce_args_E_isred Γ t args h t' args' :
    Some (t', args') = reduce_args_E Γ t args h ->
    RedFlags.beta flags ->
    isApp t' = false /\ (isLambda t' -> args' = []).
  Proof using Type.
    intros e hb.
    pose proof (reduce_stack_E_isred Γ t _ h _ hb (reduce_args_E_spec Γ t args h t' args' e)) as hi.
    destruct hi as [hna hl]. cbn [fst snd] in hna, hl |- *.
    split; [exact hna|].
    intros hlam. specialize (hl hlam).
    destruct args'; [reflexivity|discriminate hl].
  Qed.

  Lemma reduce_args_E_Req Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t args h t' args' :
    Some (t', args') = reduce_args_E Γ t args h ->
    (t', args') = (t, args) \/
    cored Σ Γ (mkApps t' args') (mkApps t args) \/
    (mkApps t' args' = mkApps t args /\
     PCUICPositionEta.positionR
       (PCUICPositionEta.stack_position (PCUICPositionEta.appstack args' []))
       (PCUICPositionEta.stack_position (PCUICPositionEta.appstack args []))).
  Proof using Type.
    intros e.
    pose proof (reduce_stack_E_Req Σ wfΣ Γ t _ h _ (reduce_args_E_spec Γ t args h t' args' e)) as hr.
    destruct hr as [heq | hR].
    - left. injection heq as -> heq.
      apply (f_equal (fun π => fst (PCUICPosition.decompose_stack π))) in heq.
      rewrite !PCUICPosition.decompose_stack_appstack in heq. cbn in heq.
      rewrite !app_nil_r in heq. now subst args'.
    - right. apply R_cases in hR as [hc | [hz hp]].
      + left. unfold PCUICPosition.zip in hc. cbn [fst snd] in hc.
        rewrite !PCUICPosition.zipc_appstack in hc. exact hc.
      + right. split.
        * unfold PCUICPosition.zip in hz. cbn [fst snd] in hz.
          rewrite !PCUICPosition.zipc_appstack in hz. exact hz.
        * cbn [snd] in hp. apply stack_position_appstack_bridge. exact hp.
  Qed.

  Lemma reduce_stack_vass Γ n decl h r :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    reduce_stack_E Γ (tRel n) [] h = Some r -> r = (tRel n, []).
  Proof using Type.
    intros hn hb. unfold reduce_stack_E.
    exact (reduce_stack_Rel_assum (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := @reduce_typed_facts_E cf reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      flags X_type X Γ n decl h r hn hb).
  Qed.

  Lemma reduce_args_E_vass Γ n decl h r :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    Some r = reduce_args_E Γ (tRel n) [] h -> r = (tRel n, []).
  Proof using Type.
    intros hn hb. destruct r as [t' args']. intros e.
    pose proof (reduce_args_E_spec Γ (tRel n) [] h t' args' e) as es.
    change (PCUICPosition.appstack [] []) with (@nil PCUICPosition.stack_entry) in es.
    pose proof (reduce_stack_vass Γ n decl h _ hn hb es) as ev.
    injection ev as -> ev.
    destruct args'; [reflexivity|discriminate ev].
  Qed.

End BridgeE.

(** ** Concrete satisfying instances of the fields of [reduce_factsE] at E

    FRAC convention ([PCUICEtaFracInstances]): each field specialised to a concrete
    environment and concrete closed terms, every premise proved (the [welltypedE] ones
    by [typing_incl_E] of a base derivation, [wf_extE] by [wf_ext_incl_E], closed
    bodies by [wfE_ClosedBodies]) and the field's conclusion proved there directly,
    without the field. Each lemma states [premises × conclusion]. Environments:
    - [si_Σ] ([Inductive I (A : Prop) : Prop := c : I A],
      [PCUICCumulativitySpecEtaClosureInstances]): [rtf_wt_red_inst],
      [rtf_context_inst], [rtf_rel_inst], [rtf_whnf_red_inv_inst],
      [rtf_fix_arg_whne_inst] ([(fix f (x : I P) := x) x]), [rtf_case_construct_inst]
      and [rtf_case_arg_whne_inst] (a case on [I P] with the branch [c P]);
    - [sa_Σ] (one axiom, [PCUICEtaA6Instances]): [rtf_const_inst];
    - [co_Σ] ([CoInductive CoI (A : Prop) : Prop := c : CoI A], declared below, as no
      environment on [frac/eta] has a coinductive type): [rtf_cofix_inst];
    - [rec_Σ] ([Record R (A : Prop) : Prop := mk { r : A }], declared below, as no
      environment on [frac/eta] has a record): [rtf_proj_construct_inst],
      [rtf_proj_arg_whne_inst].
    The four fields concluding [False] ([rtf_app_sort], [rtf_app_prod], [rtf_app_prim],
    [rtf_prim_overapplied]) have no such instance by design (their premise is
    unsatisfiable); see their argument in [PCUICSafeReduceEta.ReduceTypedFacts]. *)
Module SI := MetaRocq.PCUIC.PCUICCumulativitySpecEtaClosureInstances.
Module SA := MetaRocq.PCUIC.PCUICEtaA6Instances.

Section FracInstancesE.
  #[local] Existing Instance default_checker_flags.

  Lemma si_wf_ext : wf_ext SI.si_Σ.
  Proof. split; [exact SI.si_wf|exact SI.si_on_udecl]. Qed.

  Lemma si_wf_extE : wf_extE SI.si_Σ.
  Proof. exact (wf_ext_incl_E si_wf_ext). Qed.

  Lemma si_cbE : ClosedBodies SI.si_Σ.
  Proof. exact (@wfE_ClosedBodies _ SI.si_Σ (fst si_wf_extE)). Qed.

  Lemma si_P_typed : SI.si_Σ ;;; [] |- SI.si_P : tSort (Sort.super sProp).
  Proof. apply type_Sort; [constructor|cbn; trivial]. Qed.

  Lemma si_P_wtE : welltypedE SI.si_Σ [] SI.si_P.
  Proof. econstructor. exact (typing_incl_E (Σ := SI.si_Σ) SI.si_wf si_P_typed). Qed.

  Definition si_Γ1 : context := [vass SI.si_na SI.si_P].

  Lemma si_wf_Γ1 : wf_local SI.si_Σ si_Γ1.
  Proof.
    apply localenv_cons_abs; [constructor|].
    split; [exact tt|]. exists (Sort.super sProp).
    split; [exact si_P_typed|]. split; [exact I|reflexivity].
  Qed.

  (** [rtf_wt_red] (T1): [Prop : Type] reduces to itself. *)
  Lemma rtf_wt_red_inst :
    wf_extE SI.si_Σ × welltypedE SI.si_Σ [] SI.si_P × red SI.si_Σ [] SI.si_P SI.si_P ×
    welltypedE SI.si_Σ [] SI.si_P.
  Proof.
    split; [exact si_wf_extE|]. split; [exact si_P_wtE|]. split; [reflexivity|exact si_P_wtE].
  Qed.

  (** [rtf_context] (T6), on the empty stack. *)
  Lemma rtf_context_inst :
    wf_extE SI.si_Σ × welltypedE SI.si_Σ [] (zip (SI.si_P, @nil stack_entry)) ×
    welltypedE SI.si_Σ ([] ,,, stack_context (snd (SI.si_P, @nil stack_entry)))
      (fst (SI.si_P, @nil stack_entry)).
  Proof.
    split; [exact si_wf_extE|]. split; exact si_P_wtE.
  Qed.

  (** [rtf_rel] (T6): a variable of [x : Prop]. *)
  Lemma rtf_rel_inst :
    wf_extE SI.si_Σ × welltypedE SI.si_Σ si_Γ1 (tRel 0) × nth_error si_Γ1 0 <> None.
  Proof.
    split; [exact si_wf_extE|]. split.
    - econstructor. apply (typing_incl_E (Σ := SI.si_Σ) SI.si_wf).
      eapply type_Rel; [exact si_wf_Γ1|reflexivity].
    - discriminate.
  Qed.

  Lemma sa_wf_ext : wf_ext SA.sa_Σ.
  Proof. split; [exact SA.sa_wf|exact SI.si_on_udecl]. Qed.

  (** [rtf_const] (T6): the axiom [A : Prop] of [sa_Σ]. *)
  Lemma rtf_const_inst :
    wf_extE SA.sa_Σ × welltypedE SA.sa_Σ [] (tConst SA.sa_kn []) ×
    exists decl, declared_constant SA.sa_Σ SA.sa_kn decl.
  Proof.
    split; [exact (wf_ext_incl_E sa_wf_ext)|]. split.
    - econstructor. apply (typing_incl_E (Σ := SA.sa_Σ) SA.sa_wf).
      eapply type_Const; [constructor|exact SA.sa_declared|reflexivity].
    - exists SA.sa_cb. exact SA.sa_declared.
  Qed.

  (** [rtf_whnf_red_inv] (untyped, W-c): [Prop] is in weak-head normal form and its
      only reduct is itself. *)
  Lemma rtf_whnf_red_inv_inst :
    wf_extE SI.si_Σ × whnf RedFlags.default SI.si_Σ [] SI.si_P ×
    ∥ SI.si_Σ ;;; [] ⊢ SI.si_P ⇝ SI.si_P ∥ × ∥ whnf_red SI.si_Σ [] SI.si_P SI.si_P ∥.
  Proof.
    split; [exact si_wf_extE|]. split; [exact (whnf_sort _ _ _ _)|]. split.
    - constructor. apply into_closed_red; [reflexivity|reflexivity|reflexivity].
    - constructor. exact (whnf_red_tSort _ _ _).
  Qed.

  (** *** A fixpoint on [I P], [P := ∀ X : Prop, X], applied to a variable *)

  Definition fx_P : term := tProd SI.si_na (tSort sProp) (tRel 0).
  Definition fx_I : term := tApp (tInd SI.si_ind []) fx_P.
  Definition fx_ty : term := tProd SI.si_na fx_I fx_I.
  Definition fx_body : term := tLambda SI.si_na fx_I (tRel 0).
  Definition fx_def : def term :=
    {| dname := SI.si_na; dtype := fx_ty; dbody := fx_body; rarg := 0 |}.
  Definition fx_mfix : mfixpoint term := [fx_def].
  Definition fx_Γ : context := [vass SI.si_na fx_I].

  (** Typing helpers, for any environment [Σ] (used at [si_Σ] and at [co_Σ] below). *)
  Lemma si_vass_gen {Σ : global_env_ext} Γ (na : aname) A s : Σ ;;; Γ |- A : tSort s ->
    isSortRel s na.(binder_relevance) -> lift_typing typing Σ Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma si_vass_s_gen {Σ : global_env_ext} Γ (na : aname) A s : Σ ;;; Γ |- A : tSort s ->
    isSortRel s na.(binder_relevance) -> lift_typing typing Σ Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma si_typrel {Σ : global_env_ext} Γ T s rel : Σ ;;; Γ |- T : tSort s -> isSortRel s rel ->
    lift_typing typing Σ Γ (TypRel T rel).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma si_termtyp {Σ : global_env_ext} Γ t T s rel : Σ ;;; Γ |- t : T -> Σ ;;; Γ |- T : tSort s ->
    isSortRel s rel -> lift_typing typing Σ Γ (TermTypRel t T rel).
  Proof. intros ht h r. split; [exact ht|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma si_wf_cons {Σ : global_env_ext} Γ (na : aname) A s : wf_local Σ Γ -> Σ ;;; Γ |- A : tSort s ->
    isSortRel s na.(binder_relevance) -> wf_local Σ (Γ ,, vass na A).
  Proof. intros hΓ h r. apply localenv_cons_abs; [exact hΓ|exact (si_vass_gen Γ na A s h r)]. Qed.

  Lemma si_Prop_typed {Σ : global_env_ext} Γ : wf_local Σ Γ ->
    Σ ;;; Γ |- tSort sProp : tSort (Sort.super sProp).
  Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

  Lemma fx_P_typed {Σ : global_env_ext} Γ : wf_local Σ Γ -> Σ ;;; Γ |- fx_P : tSort sProp.
  Proof.
    intros h.
    assert (h' : wf_local Σ (Γ ,, vass SI.si_na (tSort sProp)))
      by (apply (si_wf_cons _ _ _ (Sort.super sProp) h (si_Prop_typed _ h)); reflexivity).
    exact (type_Prod _ _ SI.si_na (tSort sProp) (tRel 0) (Sort.super sProp) sProp
      (si_vass_s_gen _ SI.si_na _ _ (si_Prop_typed _ h) eq_refl)
      (type_Rel _ _ 0 (vass SI.si_na (tSort sProp)) h' eq_refl)).
  Qed.

  Lemma si_arity_typed {Σ : global_env_ext} Γ : wf_local Σ Γ ->
    Σ ;;; Γ |- tProd SI.si_na (tSort sProp) (tSort sProp)
      : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
  Proof.
    intros h.
    assert (h' : wf_local Σ (Γ ,, vass SI.si_na (tSort sProp)))
      by (apply (si_wf_cons _ _ _ (Sort.super sProp) h (si_Prop_typed _ h)); reflexivity).
    exact (type_Prod _ _ SI.si_na (tSort sProp) (tSort sProp) (Sort.super sProp) (Sort.super sProp)
      (si_vass_s_gen _ SI.si_na _ _ (si_Prop_typed _ h) eq_refl) (si_Prop_typed _ h')).
  Qed.

  Lemma fx_I_typed Γ : wf_local SI.si_Σ Γ -> SI.si_Σ ;;; Γ |- fx_I : tSort sProp.
  Proof.
    intros h.
    exact (type_App _ _ (tInd SI.si_ind []) SI.si_na (tSort sProp) (tSort sProp) _ fx_P
      (si_arity_typed Γ h)
      (type_Ind _ _ SI.si_ind [] SI.si_mdecl SI.si_idecl h SI.si_declared_inductive eq_refl)
      (fx_P_typed Γ h)).
  Qed.

  Lemma fx_ty_typed Γ : wf_local SI.si_Σ Γ -> SI.si_Σ ;;; Γ |- fx_ty : tSort sProp.
  Proof.
    intros h.
    assert (h' : wf_local SI.si_Σ (Γ ,, vass SI.si_na fx_I))
      by (apply (si_wf_cons _ _ _ sProp h (fx_I_typed _ h)); reflexivity).
    exact (type_Prod _ _ SI.si_na fx_I fx_I sProp sProp
      (si_vass_s_gen _ SI.si_na _ _ (fx_I_typed _ h) eq_refl) (fx_I_typed _ h')).
  Qed.

  Lemma fx_wf_Γ : wf_local SI.si_Σ fx_Γ.
  Proof.
    assert (h0 : wf_local SI.si_Σ []) by constructor.
    apply (si_wf_cons [] _ _ sProp h0 (fx_I_typed _ h0)); reflexivity.
  Qed.

  Lemma fx_body_typed : SI.si_Σ ;;; fx_Γ ,, vass SI.si_na fx_ty |- fx_body : fx_ty.
  Proof.
    assert (h1 : wf_local SI.si_Σ (fx_Γ ,, vass SI.si_na fx_ty))
      by (apply (si_wf_cons _ _ _ sProp fx_wf_Γ (fx_ty_typed _ fx_wf_Γ)); reflexivity).
    assert (h2 : wf_local SI.si_Σ (fx_Γ ,, vass SI.si_na fx_ty ,, vass SI.si_na fx_I))
      by (apply (si_wf_cons _ _ _ sProp h1 (fx_I_typed _ h1)); reflexivity).
    exact (type_Lambda _ _ SI.si_na fx_I (tRel 0) fx_I
      (si_vass_gen _ SI.si_na _ sProp (fx_I_typed _ h1) eq_refl)
      (type_Rel _ _ 0 (vass SI.si_na fx_I) h2 eq_refl)).
  Qed.

  Lemma fx_guard : fix_guard SI.si_Σ fx_Γ fx_mfix.
  Proof.
    unfold fix_guard. cbn. apply gc_check. split; [vm_compute; reflexivity|].
    exists 100. vm_compute. reflexivity.
  Qed.

  Lemma fx_wf_fixpoint : wf_fixpoint SI.si_Σ fx_Γ fx_mfix.
  Proof.
    split; [reflexivity|]. split; [reflexivity|].
    exists SI.si_kn. split; [discriminate|]. split.
    - constructor; [|constructor].
      exists fx_ty. split; [reflexivity|]. split; [reflexivity|apply cumul_Refl].
    - vm_compute. reflexivity.
  Qed.

  Lemma fx_fix_typed : SI.si_Σ ;;; fx_Γ |- tFix fx_mfix 0 : fx_ty.
  Proof.
    eapply (type_Fix _ _ fx_mfix 0 fx_def).
    - exact fx_wf_Γ.
    - exact fx_guard.
    - reflexivity.
    - constructor; [|constructor].
      exact (si_typrel _ _ sProp Relevant (fx_ty_typed _ fx_wf_Γ) eq_refl).
    - constructor; [|constructor].
      assert (h1 : wf_local SI.si_Σ (fx_Γ ,, vass SI.si_na fx_ty))
        by (apply (si_wf_cons _ _ _ sProp fx_wf_Γ (fx_ty_typed _ fx_wf_Γ)); reflexivity).
      exact (si_termtyp (fx_Γ ,, vass SI.si_na fx_ty) fx_body fx_ty sProp Relevant
        fx_body_typed (fx_ty_typed _ h1) eq_refl).
    - exact fx_wf_fixpoint.
  Qed.

  Lemma fx_app_typed : SI.si_Σ ;;; fx_Γ |- tApp (tFix fx_mfix 0) (tRel 0) : fx_I.
  Proof.
    exact (type_App _ _ (tFix fx_mfix 0) SI.si_na fx_I fx_I sProp (tRel 0)
      (fx_ty_typed _ fx_wf_Γ) fx_fix_typed (type_Rel _ _ 0 (vass SI.si_na fx_I) fx_wf_Γ eq_refl)).
  Qed.

  (** [rtf_fix_arg_whne] (T6): [(fix f (x : I P) := x) x] in [x : I P]; the recursive
      argument [x] is a weak-head normal variable, so it is neutral. *)
  Lemma rtf_fix_arg_whne_inst :
    wf_extE SI.si_Σ ×
    unfold_fix fx_mfix 0 = Some (#|@nil term|, subst0 (fix_subst fx_mfix) fx_body) ×
    whnf RedFlags.default SI.si_Σ fx_Γ (mkApps (tRel 0) []) ×
    welltypedE SI.si_Σ fx_Γ (mkApps (tFix fx_mfix 0) ([] ++ mkApps (tRel 0) [] :: [])) ×
    ∥ whne RedFlags.default SI.si_Σ fx_Γ (mkApps (tRel 0) []) ∥.
  Proof.
    split; [exact si_wf_extE|]. split; [reflexivity|]. split.
    { apply whnf_ne. apply whne_rel. reflexivity. }
    split.
    - econstructor. exact (typing_incl_E (Σ := SI.si_Σ) SI.si_wf fx_app_typed).
    - constructor. apply whne_rel. reflexivity.
  Qed.

  (** *** A case on [I P] returning [I P], with the one branch [c P] *)

  Definition cs_ctor_ty : term :=
    tProd SI.si_na (tSort sProp) (tApp (tInd SI.si_ind []) (tRel 0)).
  Definition cs_c : term := tApp (tConstruct SI.si_ind 0 []) fx_P.
  (* FORECAST tree only (EtaK7): this base (integ-all7, BET-339) adds the field [ci_cofix_nondep] to
     [case_info]; [true] as base's [PCUICCasesHelper]; irrelevant here, the case is on an inductive. *)
  Definition cs_ci : case_info :=
    {| ci_ind := SI.si_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.
  Definition cs_p : predicate term :=
    {| pparams := [fx_P]; puinst := [];
       pcontext := ind_predicate_context SI.si_ind SI.si_mdecl SI.si_idecl; preturn := fx_I |}.
  Definition cs_br : branch term := {| bcontext := []; bbody := cs_c |}.
  Definition cs_brs : list (branch term) := [cs_br].
  Definition cs_ptm : term :=
    it_mkLambda_or_LetIn (case_predicate_context SI.si_ind SI.si_mdecl SI.si_idecl cs_p) fx_I.

  Lemma cs_eqctx_refl ctx : eq_context_upto_names ctx ctx.
  Proof.
    induction ctx as [|d ctx IH]; cbn; constructor; [|exact IH].
    destruct d as [na [b|] ty]; [apply compare_vdef|apply compare_vass]; reflexivity.
  Qed.

  Lemma cs_ctor_ty_typed Γ : wf_local SI.si_Σ Γ -> SI.si_Σ ;;; Γ |- cs_ctor_ty : tSort sProp.
  Proof.
    intros h.
    assert (h' : wf_local SI.si_Σ (Γ ,, vass SI.si_na (tSort sProp)))
      by (apply (si_wf_cons _ _ _ (Sort.super sProp) h (si_Prop_typed _ h)); reflexivity).
    exact (type_Prod _ _ SI.si_na (tSort sProp) (tApp (tInd SI.si_ind []) (tRel 0))
      (Sort.super sProp) sProp
      (si_vass_s_gen _ SI.si_na _ _ (si_Prop_typed _ h) eq_refl)
      (type_App _ _ (tInd SI.si_ind []) SI.si_na (tSort sProp) (tSort sProp) _ (tRel 0)
        (si_arity_typed _ h')
        (type_Ind _ _ SI.si_ind [] SI.si_mdecl SI.si_idecl h' SI.si_declared_inductive eq_refl)
        (type_Rel _ _ 0 (vass SI.si_na (tSort sProp)) h' eq_refl))).
  Qed.

  Lemma cs_c_typed Γ : wf_local SI.si_Σ Γ -> SI.si_Σ ;;; Γ |- cs_c : fx_I.
  Proof.
    intros h.
    exact (type_App _ _ (tConstruct SI.si_ind 0 []) SI.si_na (tSort sProp)
      (tApp (tInd SI.si_ind []) (tRel 0)) sProp fx_P
      (cs_ctor_ty_typed _ h)
      (type_Construct _ _ SI.si_ind 0 [] SI.si_mdecl SI.si_idecl SI.si_cdecl h
        SI.si_declared_constructor eq_refl)
      (fx_P_typed _ h)).
  Qed.

  Lemma cs_brty_typed Γ : wf_local SI.si_Σ Γ -> SI.si_Σ ;;; Γ |- tApp cs_ptm cs_c : tSort sProp.
  Proof.
    intros h. unfold cs_ptm. cbn.
    assert (h' : wf_local SI.si_Σ (Γ ,, vass SI.si_na fx_I))
      by (apply (si_wf_cons _ _ _ sProp h (fx_I_typed _ h)); reflexivity).
    eapply type_App with (B := tSort sProp); cycle 1.
    - eapply type_Lambda.
      + apply si_vass_gen with (s := sProp); [apply fx_I_typed; exact h|reflexivity].
      + apply fx_I_typed. apply si_wf_cons with (s := sProp);
          [exact h|apply fx_I_typed; exact h|reflexivity].
    - apply cs_c_typed. exact h.
    - eapply type_Prod.
      + apply si_vass_s_gen with (s := sProp); [apply fx_I_typed; exact h|reflexivity].
      + apply si_Prop_typed. apply si_wf_cons with (s := sProp);
          [exact h|apply fx_I_typed; exact h|reflexivity].
  Qed.

  Lemma cs_case_typed Γ c : wf_local SI.si_Σ Γ -> SI.si_Σ ;;; Γ |- c : fx_I ->
    SI.si_Σ ;;; Γ |- tCase cs_ci cs_p c cs_brs : mkApps cs_ptm ([] ++ [c]).
  Proof.
    intros h hc.
    assert (hpc : wf_local SI.si_Σ
      (Γ ,,, case_predicate_context SI.si_ind SI.si_mdecl SI.si_idecl cs_p)).
    { cbn. apply si_wf_cons with (s := sProp); [exact h|apply fx_I_typed; exact h|reflexivity]. }
    eapply (type_Case _ _ cs_ci cs_p c cs_brs [] sProp SI.si_mdecl SI.si_idecl).
    - exact SI.si_declared_inductive.
    - apply fx_I_typed. exact hpc.
    - exact hc.
    - constructor.
      + reflexivity.
      + split; [reflexivity|]. cbn. repeat constructor.
      + reflexivity.
      + exact hpc.
      + apply cs_eqctx_refl.
      + cbn. trivial.
      + reflexivity.
      + cbn. constructor; [apply fx_P_typed; exact h|constructor].
      + reflexivity.
    - constructor.
      + cbn. repeat constructor.
      + constructor; [|constructor].
        split; [cbn; constructor|].
        split; [cbn; exact h|].
        split.
        * cbn. eapply type_Cumul.
          -- apply cs_c_typed. exact h.
          -- apply cs_brty_typed. exact h.
          -- apply cumul_Sym. apply cumul_beta.
        * cbn. apply cs_brty_typed. exact h.
  Qed.

  (** [rtf_case_construct] (T6): the case on [c P]. *)
  Lemma rtf_case_construct_inst :
    wf_extE SI.si_Σ ×
    welltypedE SI.si_Σ [] (tCase cs_ci cs_p (mkApps (tConstruct SI.si_ind 0 []) [fx_P]) cs_brs) ×
    (cs_ci.(ci_ind) = SI.si_ind /\ exists br, nth_error cs_brs 0 = Some br /\
      (#|[fx_P]| = cs_ci.(ci_npar) + context_assumptions br.(bcontext))%nat).
  Proof.
    assert (h0 : wf_local SI.si_Σ []) by constructor.
    split; [exact si_wf_extE|]. split.
    - econstructor. apply (typing_incl_E (Σ := SI.si_Σ) SI.si_wf).
      exact (cs_case_typed [] cs_c h0 (cs_c_typed [] h0)).
    - split; [reflexivity|]. exists cs_br. split; reflexivity.
  Qed.

  (** [rtf_case_arg_whne] (T6): the case on the variable [x : I P]; the discriminee is
      a weak-head normal variable, so it is neutral. *)
  Lemma rtf_case_arg_whne_inst :
    wf_extE SI.si_Σ ×
    whnf RedFlags.default SI.si_Σ fx_Γ (mkApps (tRel 0) []) ×
    welltypedE SI.si_Σ fx_Γ (tCase cs_ci cs_p (mkApps (tRel 0) []) cs_brs) ×
    ∥ whne RedFlags.default SI.si_Σ fx_Γ (mkApps (tRel 0) []) ∥.
  Proof.
    split; [exact si_wf_extE|]. split; [apply whnf_ne; apply whne_rel; reflexivity|]. split.
    - econstructor. apply (typing_incl_E (Σ := SI.si_Σ) SI.si_wf).
      exact (cs_case_typed fx_Γ (tRel 0) fx_wf_Γ
        (type_Rel _ _ 0 (vass SI.si_na fx_I) fx_wf_Γ eq_refl)).
    - constructor. apply whne_rel. reflexivity.
  Qed.

  (** *** A cofixpoint on a coinductive copy of [I]

      No environment on [frac/eta] declares a coinductive type, so [co_Σ] declares
      [CoInductive CoI (A : Prop) : Prop := c : CoI A]: the declaration of [si_Σ] with
      [ind_finite := CoFinite], under another name. Its well-formedness proof is
      [si_wf]'s, step by step. *)

  Definition co_kn : kername := (MPfile ["SInst"], "CoI").
  Definition co_ind : inductive := {| inductive_mind := co_kn; inductive_ind := 0 |}.
  Definition co_mdecl : mutual_inductive_body :=
    {| ind_finite := CoFinite; ind_npars := 1; ind_params := SI.si_params;
       ind_bodies := [SI.si_idecl]; ind_universes := Monomorphic_ctx; ind_variance := None |}.
  Definition co_env : global_env :=
    {| universes := ContextSet.empty; declarations := [(co_kn, InductiveDecl co_mdecl)];
       retroknowledge := Retroknowledge.empty |}.
  Definition co_Σ : global_env_ext := (co_env, Monomorphic_ctx).

  Lemma co_on_constructor :
    on_constructor cumulSpec0 (lift_typing typing) SI.si_Σ0 co_mdecl 0 SI.si_idecl []
      SI.si_cdecl [].
  Proof.
    unshelve econstructor.
    - reflexivity.
    - reflexivity.
    - exact (SI.si_vass _ (mkBindAnn nAnon Relevant) _ _ SI.si_ctype_typed eq_refl).
    - exact tt.
    - constructor.
    - cbn. eapply pos_ass.
      + apply pos_arg_closed. reflexivity.
      + exact (pos_concl _ _ _ [vass SI.si_na SI.si_P] [tRel 0]
          (All_cons (x := tRel 0) (eq_refl : is_true (closedn 1 (tRel 0))) All_nil)).
    - intros v e. discriminate e.
    - destruct lets_in_constructor_types; [exact I|reflexivity].
  Qed.

  Lemma co_on_ind_body :
    on_ind_body cumulSpec0 (lift_typing typing) SI.si_Σ0 co_kn co_mdecl 0 SI.si_idecl.
  Proof.
    unshelve econstructor.
    - exact [[]].
    - exists (tSort sProp). split; [reflexivity|].
      apply arity_red_sort. apply whd_stop. reflexivity.
    - exact (SI.si_vass _ (mkBindAnn nAnon rel_of_Type) _ _
        (SI.si_arity_typed [] SI.si_wf_nil) eq_refl).
    - exact (SI.si_vass _ (mkBindAnn nAnon rel_of_Type) _ _
        (SI.si_arity_typed [] SI.si_wf_nil) eq_refl).
    - constructor; [exact co_on_constructor|constructor].
    - exact I.
    - reflexivity.
    - reflexivity.
    - exact I.
  Qed.

  Lemma co_on_inductive : on_inductive cumulSpec0 (lift_typing typing) SI.si_Σ0 co_kn co_mdecl.
  Proof.
    constructor.
    - constructor; [exact co_on_ind_body|constructor].
    - exact (SI.si_wf_P [] SI.si_wf_nil).
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma co_wf : wf co_env.
  Proof.
    split.
    - split; [|split].
      + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
      + intros x Hx.
        change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                              (LevelSet.singleton Level.lzero))) in Hx.
        apply LevelSet.union_spec in Hx as [Hx|Hx].
        * exfalso. eapply LevelSet.empty_spec. exact Hx.
        * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
      + exists SI.si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    - split.
      { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                          |intros i h; discriminate h]. }
      apply globenv_decl; [constructor|].
      constructor.
      + constructor.
      + exact SI.si_on_udecl.
      + exact co_on_inductive.
      + cbn. intros i h; discriminate h.
  Qed.

  Lemma co_wf_ext : wf_ext co_Σ.
  Proof. split; [exact co_wf|exact SI.si_on_udecl]. Qed.

  Lemma co_wf_extE : wf_extE co_Σ.
  Proof. exact (wf_ext_incl_E co_wf_ext). Qed.

  Lemma co_declared_inductive : declared_inductive co_Σ co_ind co_mdecl SI.si_idecl.
  Proof. split; [left; reflexivity|reflexivity]. Qed.

  Lemma co_declared_constructor :
    declared_constructor co_Σ (co_ind, 0) co_mdecl SI.si_idecl SI.si_cdecl.
  Proof. split; [exact co_declared_inductive|reflexivity]. Qed.

  Definition co_I : term := tApp (tInd co_ind []) fx_P.
  Definition co_c : term := tApp (tConstruct co_ind 0 []) fx_P.
  Definition co_def : def term := {| dname := SI.si_na; dtype := co_I; dbody := co_c; rarg := 0 |}.
  Definition co_mfix : mfixpoint term := [co_def].
  Definition co_ctor_ty : term :=
    tProd SI.si_na (tSort sProp) (tApp (tInd co_ind []) (tRel 0)).

  Lemma co_I_typed Γ : wf_local co_Σ Γ -> co_Σ ;;; Γ |- co_I : tSort sProp.
  Proof.
    intros h.
    exact (type_App _ _ (tInd co_ind []) SI.si_na (tSort sProp) (tSort sProp) _ fx_P
      (si_arity_typed Γ h)
      (type_Ind _ _ co_ind [] co_mdecl SI.si_idecl h co_declared_inductive eq_refl)
      (fx_P_typed Γ h)).
  Qed.

  Lemma co_ctor_ty_typed Γ : wf_local co_Σ Γ -> co_Σ ;;; Γ |- co_ctor_ty : tSort sProp.
  Proof.
    intros h.
    assert (h' : wf_local co_Σ (Γ ,, vass SI.si_na (tSort sProp)))
      by (apply (si_wf_cons _ _ _ (Sort.super sProp) h (si_Prop_typed _ h)); reflexivity).
    exact (type_Prod _ _ SI.si_na (tSort sProp) (tApp (tInd co_ind []) (tRel 0))
      (Sort.super sProp) sProp
      (si_vass_s_gen _ SI.si_na _ _ (si_Prop_typed _ h) eq_refl)
      (type_App _ _ (tInd co_ind []) SI.si_na (tSort sProp) (tSort sProp) _ (tRel 0)
        (si_arity_typed _ h')
        (type_Ind _ _ co_ind [] co_mdecl SI.si_idecl h' co_declared_inductive eq_refl)
        (type_Rel _ _ 0 (vass SI.si_na (tSort sProp)) h' eq_refl))).
  Qed.

  Lemma co_c_typed Γ : wf_local co_Σ Γ -> co_Σ ;;; Γ |- co_c : co_I.
  Proof.
    intros h.
    exact (type_App _ _ (tConstruct co_ind 0 []) SI.si_na (tSort sProp)
      (tApp (tInd co_ind []) (tRel 0)) sProp fx_P
      (co_ctor_ty_typed _ h)
      (type_Construct _ _ co_ind 0 [] co_mdecl SI.si_idecl SI.si_cdecl h
        co_declared_constructor eq_refl)
      (fx_P_typed _ h)).
  Qed.

  Lemma co_guard : cofix_guard co_Σ [] co_mfix.
  Proof.
    unfold cofix_guard. cbn. apply gc_check. split; [vm_compute; reflexivity|].
    exists 100. vm_compute. reflexivity.
  Qed.

  Lemma co_wf_cofixpoint : wf_cofixpoint co_Σ [] co_mfix.
  Proof.
    exists co_kn. split; [discriminate|]. split.
    - constructor; [|constructor].
      exists co_I. split; [reflexivity|]. split; [reflexivity|apply cumul_Refl].
    - vm_compute. reflexivity.
  Qed.

  Lemma co_cofix_typed : co_Σ ;;; [] |- tCoFix co_mfix 0 : co_I.
  Proof.
    assert (h0 : wf_local co_Σ []) by constructor.
    eapply (type_CoFix _ _ co_mfix 0 co_def).
    - exact h0.
    - exact co_guard.
    - reflexivity.
    - constructor; [|constructor].
      exact (si_typrel _ _ sProp Relevant (co_I_typed _ h0) eq_refl).
    - constructor; [|constructor].
      assert (h1 : wf_local co_Σ ([] ,, vass SI.si_na co_I))
        by (apply (si_wf_cons _ _ _ sProp h0 (co_I_typed _ h0)); reflexivity).
      exact (si_termtyp ([] ,, vass SI.si_na co_I) co_c co_I sProp Relevant
        (co_c_typed _ h1) (co_I_typed _ h1) eq_refl).
    - exact co_wf_cofixpoint.
  Qed.

  (** [rtf_cofix] (T6): [cofix f : CoI P := c P]. *)
  Lemma rtf_cofix_inst :
    wf_extE co_Σ × welltypedE co_Σ [] (tCoFix co_mfix 0) × nth_error co_mfix 0 <> None.
  Proof.
    split; [exact co_wf_extE|]. split.
    - econstructor. exact (typing_incl_E (Σ := co_Σ) co_wf co_cofix_typed).
    - discriminate.
  Qed.

  (** *** Projections out of a one-field record

      No environment on [frac/eta] declares a record with projections, so [rec_Σ]
      declares [Record R (A : Prop) : Prop := mk { r : A }] (one parameter, one field,
      primitive projection [r], singleton elimination). The proof of [rec_wf] follows
      [si_wf], with the field's sort, positivity and projection added. *)

  Definition rec_kn : kername := (MPfile ["SInst"], "R").
  Definition rec_ind : inductive := {| inductive_mind := rec_kn; inductive_ind := 0 |}.
  Definition rec_r_na : aname := mkBindAnn (nNamed "r") Relevant.
  Definition rec_cdecl : constructor_body :=
    {| cstr_name := "mk"; cstr_args := [vass rec_r_na (tRel 0)]; cstr_indices := [];
       cstr_type := tProd SI.si_na SI.si_P (tProd rec_r_na (tRel 0) (tApp (tRel 2) (tRel 1)));
       cstr_arity := 1 |}.
  Definition rec_pdecl : projection_body :=
    {| proj_name := "r"; proj_relevance := Relevant; proj_type := tRel 1 |}.
  Definition rec_idecl : one_inductive_body :=
    {| ind_name := "I"; ind_indices := []; ind_sort := sProp; ind_type := SI.si_arity;
       ind_kelim := IntoAny; ind_ctors := [rec_cdecl]; ind_projs := [rec_pdecl];
       ind_relevance := Relevant |}.
  Definition rec_mdecl : mutual_inductive_body :=
    {| ind_finite := BiFinite; ind_npars := 1; ind_params := SI.si_params;
       ind_bodies := [rec_idecl]; ind_universes := Monomorphic_ctx; ind_variance := None |}.
  Definition rec_env : global_env :=
    {| universes := ContextSet.empty; declarations := [(rec_kn, InductiveDecl rec_mdecl)];
       retroknowledge := Retroknowledge.empty |}.
  Definition rec_Σ : global_env_ext := (rec_env, Monomorphic_ctx).
  Definition rec_proj : projection := {| proj_ind := rec_ind; proj_npars := 1; proj_arg := 0 |}.

  (** The constructor type [Π A : Prop. Π r : A. R A], in the arities context. *)
  Lemma rec_ctype_typed : SI.si_Σ0 ;;; SI.si_Γi |- cstr_type rec_cdecl : tSort sProp.
  Proof.
    pose proof (SI.si_wf_P SI.si_Γi SI.si_wf_Γi) as w2.
    assert (w3 : wf_local SI.si_Σ0 (SI.si_Γi ,, vass SI.si_na SI.si_P ,, vass rec_r_na (tRel 0)))
      by (apply (si_wf_cons _ _ _ sProp w2 (type_Rel _ _ 0 (vass SI.si_na SI.si_P) w2 eq_refl));
          reflexivity).
    exact (type_Prod _ _ SI.si_na SI.si_P _ (Sort.super sProp) sProp
      (si_vass_s_gen _ SI.si_na _ (Sort.super sProp) (SI.si_P_typed _ SI.si_wf_Γi) eq_refl)
      (type_Prod _ _ rec_r_na (tRel 0) _ sProp sProp
        (si_vass_s_gen _ rec_r_na _ sProp (type_Rel _ _ 0 (vass SI.si_na SI.si_P) w2 eq_refl) eq_refl)
        (type_App _ _ (tRel 2) SI.si_na SI.si_P (tSort sProp)
          (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 1)
          (si_arity_typed _ w3)
          (type_Rel _ _ 2 (vass (mkBindAnn (nNamed "I") rel_of_Type) SI.si_arity) w3 eq_refl)
          (type_Rel _ _ 1 (vass SI.si_na SI.si_P) w3 eq_refl)))).
  Qed.

  Lemma rec_on_constructor :
    on_constructor cumulSpec0 (lift_typing typing) SI.si_Σ0 rec_mdecl 0 rec_idecl []
      rec_cdecl [sProp].
  Proof.
    unshelve econstructor.
    - reflexivity.
    - reflexivity.
    - exact (si_vass_gen _ (mkBindAnn nAnon Relevant) _ sProp rec_ctype_typed eq_refl).
    - split; [exact tt|].
      exact (si_vass_s_gen _ rec_r_na _ sProp
        (type_Rel _ _ 0 (vass SI.si_na SI.si_P) (SI.si_wf_P SI.si_Γi SI.si_wf_Γi) eq_refl) eq_refl).
    - constructor.
    - cbn. eapply pos_ass.
      + apply pos_arg_closed. reflexivity.
      + eapply pos_ass.
        * apply pos_arg_closed. reflexivity.
        * exact (pos_concl _ _ _ [vass rec_r_na (tRel 0); vass SI.si_na SI.si_P] [tRel 1]
            (All_cons (x := tRel 1) (eq_refl : is_true (closedn 2 (tRel 1))) All_nil)).
    - intros v e. discriminate e.
    - destruct lets_in_constructor_types; [exact I|reflexivity].
  Qed.

  Lemma rec_on_ind_body :
    on_ind_body cumulSpec0 (lift_typing typing) SI.si_Σ0 rec_kn rec_mdecl 0 rec_idecl.
  Proof.
    unshelve econstructor.
    - exact [[sProp]].
    - exists (tSort sProp). split; [reflexivity|].
      apply arity_red_sort. apply whd_stop. reflexivity.
    - exact (SI.si_vass _ (mkBindAnn nAnon rel_of_Type) _ _
        (SI.si_arity_typed [] SI.si_wf_nil) eq_refl).
    - exact (SI.si_vass _ (mkBindAnn nAnon rel_of_Type) _ _
        (SI.si_arity_typed [] SI.si_wf_nil) eq_refl).
    - constructor; [exact rec_on_constructor|constructor].
    - cbn. econstructor; [reflexivity|reflexivity|reflexivity|reflexivity|].
      constructor; [|constructor]. cbn. constructor; reflexivity.
    - reflexivity.
    - reflexivity.
    - exact I.
  Qed.

  Lemma rec_on_inductive : on_inductive cumulSpec0 (lift_typing typing) SI.si_Σ0 rec_kn rec_mdecl.
  Proof.
    constructor.
    - constructor; [exact rec_on_ind_body|constructor].
    - exact (SI.si_wf_P [] SI.si_wf_nil).
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma rec_wf : wf rec_env.
  Proof.
    split.
    - split; [|split].
      + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
      + intros x Hx.
        change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                              (LevelSet.singleton Level.lzero))) in Hx.
        apply LevelSet.union_spec in Hx as [Hx|Hx].
        * exfalso. eapply LevelSet.empty_spec. exact Hx.
        * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
      + exists SI.si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    - split.
      { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                          |intros i h; discriminate h]. }
      apply globenv_decl; [constructor|].
      constructor.
      + constructor.
      + exact SI.si_on_udecl.
      + exact rec_on_inductive.
      + cbn. intros i h; discriminate h.
  Qed.

  Lemma rec_wf_ext : wf_ext rec_Σ.
  Proof. split; [exact rec_wf|exact SI.si_on_udecl]. Qed.

  Lemma rec_wf_extE : wf_extE rec_Σ.
  Proof. exact (wf_ext_incl_E rec_wf_ext). Qed.

  Lemma rec_declared_inductive : declared_inductive rec_Σ rec_ind rec_mdecl rec_idecl.
  Proof. split; [left; reflexivity|reflexivity]. Qed.

  Lemma rec_declared_constructor :
    declared_constructor rec_Σ (rec_ind, 0) rec_mdecl rec_idecl rec_cdecl.
  Proof. split; [exact rec_declared_inductive|reflexivity]. Qed.

  Lemma rec_declared_projection :
    declared_projection rec_Σ rec_proj rec_mdecl rec_idecl rec_cdecl rec_pdecl.
  Proof. split; [exact rec_declared_constructor|split; reflexivity]. Qed.

  Definition rec_I : term := tApp (tInd rec_ind []) fx_P.
  Definition rec_ctor_ty : term :=
    tProd SI.si_na (tSort sProp) (tProd rec_r_na (tRel 0) (tApp (tInd rec_ind []) (tRel 1))).

  Lemma rec_I_typed Γ : wf_local rec_Σ Γ -> rec_Σ ;;; Γ |- rec_I : tSort sProp.
  Proof.
    intros h.
    exact (type_App _ _ (tInd rec_ind []) SI.si_na (tSort sProp) (tSort sProp) _ fx_P
      (si_arity_typed Γ h)
      (type_Ind _ _ rec_ind [] rec_mdecl rec_idecl h rec_declared_inductive eq_refl)
      (fx_P_typed Γ h)).
  Qed.

  Lemma rec_ctor_ty_typed Γ : wf_local rec_Σ Γ -> rec_Σ ;;; Γ |- rec_ctor_ty : tSort sProp.
  Proof.
    intros h.
    assert (h1 : wf_local rec_Σ (Γ ,, vass SI.si_na (tSort sProp)))
      by (apply (si_wf_cons _ _ _ (Sort.super sProp) h (si_Prop_typed _ h)); reflexivity).
    assert (h2 : wf_local rec_Σ (Γ ,, vass SI.si_na (tSort sProp) ,, vass rec_r_na (tRel 0)))
      by (apply (si_wf_cons _ _ _ sProp h1
            (type_Rel _ _ 0 (vass SI.si_na (tSort sProp)) h1 eq_refl)); reflexivity).
    exact (type_Prod _ _ SI.si_na (tSort sProp) _ (Sort.super sProp) sProp
      (si_vass_s_gen _ SI.si_na _ (Sort.super sProp) (si_Prop_typed _ h) eq_refl)
      (type_Prod _ _ rec_r_na (tRel 0) _ sProp sProp
        (si_vass_s_gen _ rec_r_na _ sProp
          (type_Rel _ _ 0 (vass SI.si_na (tSort sProp)) h1 eq_refl) eq_refl)
        (type_App _ _ (tInd rec_ind []) SI.si_na (tSort sProp) (tSort sProp) _ (tRel 1)
          (si_arity_typed _ h2)
          (type_Ind _ _ rec_ind [] rec_mdecl rec_idecl h2 rec_declared_inductive eq_refl)
          (type_Rel _ _ 1 (vass SI.si_na (tSort sProp)) h2 eq_refl)))).
  Qed.

  (** [mk P t : R P] for [t : P]. *)
  Lemma rec_mk_typed Γ t : wf_local rec_Σ Γ -> rec_Σ ;;; Γ |- t : fx_P ->
    rec_Σ ;;; Γ |- mkApps (tConstruct rec_ind 0 []) [fx_P; t] : rec_I.
  Proof.
    intros h ht. cbn [mkApps].
    assert (h1 : wf_local rec_Σ (Γ ,, vass rec_r_na fx_P))
      by (apply (si_wf_cons _ _ _ sProp h (fx_P_typed _ h)); reflexivity).
    assert (hP : rec_Σ ;;; Γ |- tProd rec_r_na fx_P rec_I : tSort sProp)
      by exact (type_Prod _ _ rec_r_na fx_P rec_I sProp sProp
        (si_vass_s_gen _ rec_r_na _ sProp (fx_P_typed _ h) eq_refl) (rec_I_typed _ h1)).
    refine (type_App _ _ _ rec_r_na fx_P rec_I sProp t hP _ ht).
    exact (type_App _ _ (tConstruct rec_ind 0 []) SI.si_na (tSort sProp)
      (tProd rec_r_na (tRel 0) (tApp (tInd rec_ind []) (tRel 1))) sProp fx_P
      (rec_ctor_ty_typed _ h)
      (type_Construct _ _ rec_ind 0 [] rec_mdecl rec_idecl rec_cdecl h
        rec_declared_constructor eq_refl)
      (fx_P_typed _ h)).
  Qed.

  (** [c.(r) : P] for [c : R P]. *)
  Lemma rec_proj_typed Γ c : rec_Σ ;;; Γ |- c : rec_I -> rec_Σ ;;; Γ |- tProj rec_proj c : fx_P.
  Proof.
    intros hc.
    exact (type_Proj _ _ rec_proj c [] rec_mdecl rec_idecl rec_cdecl rec_pdecl [fx_P]
      rec_declared_projection hc eq_refl).
  Qed.

  Definition rec_x_na : aname := mkBindAnn (nNamed "x") Relevant.

  (** [rtf_proj_construct] (T6): [(mk P x).(r)] in [x : P]. *)
  Lemma rtf_proj_construct_inst :
    wf_extE rec_Σ ×
    welltypedE rec_Σ [vass rec_x_na fx_P]
      (tProj rec_proj (mkApps (tConstruct rec_ind 0 []) [fx_P; tRel 0])) ×
    (rec_proj.(proj_ind) = rec_ind /\ 0 = 0 /\
     (rec_proj.(proj_npars) + rec_proj.(proj_arg) < #|[fx_P; tRel 0]|)%nat).
  Proof.
    assert (h0 : wf_local rec_Σ []) by constructor.
    assert (h1 : wf_local rec_Σ [vass rec_x_na fx_P])
      by (apply (si_wf_cons [] _ _ sProp h0 (fx_P_typed _ h0)); reflexivity).
    split; [exact rec_wf_extE|]. split.
    - econstructor. apply (typing_incl_E (Σ := rec_Σ) rec_wf).
      apply rec_proj_typed. apply rec_mk_typed; [exact h1|].
      exact (type_Rel _ _ 0 (vass rec_x_na fx_P) h1 eq_refl).
    - split; [reflexivity|split; [reflexivity|cbn; repeat constructor]].
  Qed.

  (** [rtf_proj_arg_whne] (T6): [x.(r)] in [x : R P]; the projected term is a
      weak-head normal variable, so it is neutral. *)
  Lemma rtf_proj_arg_whne_inst :
    wf_extE rec_Σ ×
    whnf RedFlags.default rec_Σ [vass rec_x_na rec_I] (mkApps (tRel 0) []) ×
    welltypedE rec_Σ [vass rec_x_na rec_I] (tProj rec_proj (mkApps (tRel 0) [])) ×
    ∥ whne RedFlags.default rec_Σ [vass rec_x_na rec_I] (mkApps (tRel 0) []) ∥.
  Proof.
    assert (h0 : wf_local rec_Σ []) by constructor.
    assert (h1 : wf_local rec_Σ [vass rec_x_na rec_I])
      by (apply (si_wf_cons [] _ _ sProp h0 (rec_I_typed _ h0)); reflexivity).
    split; [exact rec_wf_extE|]. split; [apply whnf_ne; apply whne_rel; reflexivity|]. split.
    - econstructor. apply (typing_incl_E (Σ := rec_Σ) rec_wf).
      apply rec_proj_typed.
      exact (type_Rel _ _ 0 (vass rec_x_na rec_I) h1 eq_refl).
    - constructor. apply whne_rel. reflexivity.
  Qed.

End FracInstancesE.

(** ** The same concrete instances, for the fields of the small class [ReduceTypedFactsE]

    EtaK7 (2026-10-29, merge of [c66d5e4e] into the K7 line, lane lead): EtaIntegrate9 restructured the E
    hypothesis into the small Prop class [ReduceTypedFactsE] (fields [rtf_<f>E]), whose fields are the
    statements of [ReduceTypedFacts welltypedE wf_extE]'s fields [rtf_<f>], so each concrete instance above
    (a point where the field's premises hold, with its conclusion proved there) is also an instance of the
    small field of the same name. [rtf_prim_overappliedE] has none by design (its premise is unsatisfiable;
    argument at [PCUICSafeReduceEta.ReduceTypedFacts]). *)
Section FracInstancesSmallE.
  #[local] Existing Instance default_checker_flags.
  Definition rtf_wt_redE_inst := rtf_wt_red_inst.
  Definition rtf_contextE_inst := rtf_context_inst.
  Definition rtf_case_constructE_inst := rtf_case_construct_inst.
  Definition rtf_proj_constructE_inst := rtf_proj_construct_inst.
  Definition rtf_fix_arg_whneE_inst := rtf_fix_arg_whne_inst.
  Definition rtf_case_arg_whneE_inst := rtf_case_arg_whne_inst.
  Definition rtf_proj_arg_whneE_inst := rtf_proj_arg_whne_inst.
  Definition rtf_whnf_red_invE_inst := rtf_whnf_red_inv_inst.
End FracInstancesSmallE.
