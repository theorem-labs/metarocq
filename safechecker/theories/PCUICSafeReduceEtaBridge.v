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
  - [ReduceTypedFacts welltypedE wf_extE] is the ONE named hypothesis,
    [reduce_factsE], of the section [BridgeE] below.
  The positions of the two stack files are different types ([PCUICPositionEta] has
  its own [choice]); [stack_position_appstack_bridge] relates their orders. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICPosition
     PCUICNormal PCUICReduction PCUICSafeLemmata PCUICWellScopedCumulativity
     PCUICConversion PCUICClosedBodies PCUICTypingEta PCUICSNEta PCUICClosedTypEta.
From MetaRocq.PCUIC Require PCUICPositionEta.
From MetaRocq.SafeChecker Require Import PCUICWfReductionEta PCUICSafeReduceEta PCUICWfEnvEta.

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

(** The two cases of the machine's order [R] ([PCUICSafeReduceEta.R]), without the
    dependent pair: a strict reduction of the zipped term, or the same term and a
    deeper position. *)
Lemma dlexprod_posR_cases {A} {B : A -> Type} (leA : A -> A -> Prop)
  (f : forall x, B x -> PCUICPosition.position) (p q : sigT B) :
  dlexprod leA (fun x (a b : B x) => PCUICPosition.positionR (f x a) (f x b)) p q ->
  leA (projT1 p) (projT1 q) \/
  (projT1 p = projT1 q /\ PCUICPosition.positionR (f _ (projT2 p)) (f _ (projT2 q))).
Proof.
  intros h. destruct h as [x x' y y' h|x y y' h].
  - left. exact h.
  - right. split; [reflexivity|exact h].
Qed.

Lemma R_cases {cf : checker_flags} Σ Γ u v : R Σ Γ u v ->
  cored Σ Γ (zip u) (zip v) \/
  (zip u = zip v /\
   PCUICPosition.positionR (PCUICPosition.stack_position (snd u))
                           (PCUICPosition.stack_position (snd v))).
Proof.
  unfold R, R_aux. intros h.
  exact (dlexprod_posR_cases (cored Σ Γ) (fun t (p : pos t) => proj1_sig p) _ _ h).
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

(** ** The machine at [welltypedE], and the bridge facts *)

Section BridgeE.
  Context {cf : checker_flags} {no : normalizing_flags}.

  (** THE NAMED HYPOTHESIS of the E instantiation: the typed facts of the machine at
      [welltypedE] and [wf_extE] (field by field, with the plan row each waits on:
      [PCUICSafeReduceEta.ReduceTypedFacts]). Its satisfying instance is
      [PCUICSafeReduceEta.reduce_typed_facts_base], at base [welltyped] and [wf_ext].
      (1) That instance shows the hypothesis is consistent and the machine is about
      something real: at [welltyped] it is the base machine. (2) It does NOT discharge
      this instantiation: subject reduction over [typingE] (plan row T1), the inversion
      and classification facts over [typingE] (rows T0/T6) and the [ClosedBodies] port
      of [whnf_red_inv] (row W-c) remain this hypothesis until those rows land.
      Not a known-false form: no field states a fixpoint or cofixpoint witness obtained
      from [conv_witnessE] (or any E-conversion witness of a head shape) under
      closedness premises only, the form refuted by ArityLane's η-expanded-domain
      witness. Every field is either a typed form (its premise is [welltypedE] of the
      term it inverts or classifies, e.g. [rtf_fix_arg_whne] assumes the fixpoint
      application is [welltypedE]) or untyped ([rtf_whnf_red_inv], about base [red]
      only). *)
  Context {reduce_factsE : ReduceTypedFacts welltypedE wf_extE}.

  Context (flags : RedFlags.t) (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context {normalization_in : forall Σ, wf_extE Σ -> Σ ∼_ext X -> NormalizationInE Σ}.

  (** [NormalizationInE Σ] and [NormalizationInWt welltypedE Σ] are the same
      proposition (both unfold to [forall Γ t, welltypedE Σ Γ t -> Acc (cored Σ Γ) t]). *)
  Local Definition normalization_in_wt :
    forall Σ, wf_extE Σ -> Σ ∼_ext X -> NormalizationInWt welltypedE Σ := normalization_in.

  (** [PCUICSafeReduceEta.reduce_stack] at [welltypedE]. *)
  Definition reduce_stack_E (Γ : context) (t : term) (π : PCUICPosition.stack)
    (h : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ (PCUICPosition.zip (t, π)))
    : term × PCUICPosition.stack :=
    reduce_stack (wt := welltypedE) (wfP := wf_extE) (EF := reduce_env_facts_E)
      (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Γ t π h.

  (** The facts of [PCUICSafeReduceEta] at [welltypedE], stated over [reduce_stack_E]. *)
  Lemma reduce_stack_E_decompose Γ t π h :
    snd (PCUICPosition.decompose_stack (snd (reduce_stack_E Γ t π h))) =
    snd (PCUICPosition.decompose_stack π).
  Proof using Type.
    exact (reduce_stack_decompose (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Γ t π h).
  Qed.

  Lemma reduce_stack_E_sound Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h :
    ∥ Σ ;;; Γ ⊢ PCUICPosition.zip (t, π) ⇝ PCUICPosition.zip (reduce_stack_E Γ t π h) ∥.
  Proof using Type.
    exact (reduce_stack_sound (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Σ wfΣ Γ t π h).
  Qed.

  Lemma reduce_stack_E_whnf Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ) :
    let '(u, ρ) := reduce_stack_E Γ t π h in
    ∥ whnf flags Σ (Γ ,,, PCUICPosition.stack_context ρ) (PCUICPosition.zipp u ρ) ∥.
  Proof using Type.
    exact (reduce_stack_whnf (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Γ t π h Σ wfΣ).
  Qed.

  Lemma reduce_stack_E_isred Γ t π h :
    RedFlags.beta flags -> isred (reduce_stack_E Γ t π h).
  Proof using Type.
    exact (reduce_stack_isred (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Γ t π h).
  Qed.

  Lemma reduce_stack_E_Req Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h :
    Req Σ Γ (reduce_stack_E Γ t π h) (t, π).
  Proof using Type.
    exact (reduce_stack_Req (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Σ wfΣ Γ t π h).
  Qed.

  Lemma reduce_stack_app_only Γ t args h :
    app_only (snd (reduce_stack_E Γ t (PCUICPosition.appstack args []) h)).
  Proof using Type.
    unfold app_only. rewrite reduce_stack_E_decompose.
    rewrite PCUICPosition.decompose_stack_appstack. reflexivity.
  Qed.

  Definition reduce_args_E (Γ : context) (t : term) (args : list term)
    (h : forall Σ, abstract_env_ext_rel X Σ ->
           welltypedE Σ Γ (PCUICPosition.zip (t, PCUICPosition.appstack args [])))
    : term × list term :=
    let '(t', π') := reduce_stack_E Γ t (PCUICPosition.appstack args []) h in
    (t', fst (PCUICPosition.decompose_stack π')).

  (** The machine's output on an [App_l]-only input, through [reduce_args_E]. *)
  Lemma reduce_args_E_spec Γ t args h :
    reduce_stack_E Γ t (PCUICPosition.appstack args []) h =
    (fst (reduce_args_E Γ t args h), PCUICPosition.appstack (snd (reduce_args_E Γ t args h)) []).
  Proof using Type.
    pose proof (reduce_stack_app_only Γ t args h) as ho. revert ho.
    unfold reduce_args_E.
    destruct (reduce_stack_E Γ t (PCUICPosition.appstack args []) h) as [t' π'].
    unfold app_only. cbn [fst snd]. intros ho.
    destruct (PCUICPosition.decompose_stack π') as [l ρ] eqn:ed. cbn [fst snd] in ho |- *.
    subst ρ. apply PCUICPosition.decompose_stack_eq in ed. now subst π'.
  Qed.

  Lemma reduce_args_E_sound Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t args h :
    ∥ Σ ;;; Γ ⊢ mkApps t args ⇝ mkApps (fst (reduce_args_E Γ t args h)) (snd (reduce_args_E Γ t args h)) ∥.
  Proof using Type.
    pose proof (reduce_stack_E_sound Σ wfΣ Γ t _ h) as s.
    rewrite reduce_args_E_spec in s.
    set (ra := reduce_args_E Γ t args h) in *. clearbody ra. destruct ra as [t' args'].
    unfold PCUICPosition.zip in s. cbn [fst snd] in s |- *.
    rewrite !PCUICPosition.zipc_appstack in s. exact s.
  Qed.

  Lemma reduce_args_E_whnf Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t args h :
    ∥ whnf flags Σ Γ (mkApps (fst (reduce_args_E Γ t args h)) (snd (reduce_args_E Γ t args h))) ∥.
  Proof using Type.
    pose proof (reduce_stack_E_whnf Γ t _ h Σ wfΣ) as w.
    rewrite reduce_args_E_spec in w.
    set (ra := reduce_args_E Γ t args h) in *. clearbody ra. destruct ra as [t' args'].
    cbn [fst snd] in w |- *.
    rewrite PCUICPosition.stack_context_appstack in w.
    unfold PCUICPosition.zipp in w.
    rewrite PCUICPosition.decompose_stack_appstack in w. cbn [fst snd app] in w.
    rewrite app_nil_r in w. exact w.
  Qed.

  Lemma reduce_args_E_isred Γ t args h : RedFlags.beta flags ->
    isApp (fst (reduce_args_E Γ t args h)) = false /\
    (isLambda (fst (reduce_args_E Γ t args h)) -> snd (reduce_args_E Γ t args h) = []).
  Proof using Type.
    intros hb.
    pose proof (reduce_stack_E_isred Γ t _ h hb) as hi.
    rewrite reduce_args_E_spec in hi.
    set (ra := reduce_args_E Γ t args h) in *. clearbody ra. destruct ra as [t' args'].
    destruct hi as [hna hl]. cbn [fst snd] in hna, hl |- *.
    split; [exact hna|].
    intros hlam. specialize (hl hlam).
    destruct args'; [reflexivity|discriminate hl].
  Qed.

  Lemma reduce_args_E_Req Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t args h :
    reduce_args_E Γ t args h = (t, args) \/
    cored Σ Γ (mkApps (fst (reduce_args_E Γ t args h)) (snd (reduce_args_E Γ t args h))) (mkApps t args) \/
    (mkApps (fst (reduce_args_E Γ t args h)) (snd (reduce_args_E Γ t args h)) = mkApps t args /\
     PCUICPositionEta.positionR
       (PCUICPositionEta.stack_position (PCUICPositionEta.appstack (snd (reduce_args_E Γ t args h)) []))
       (PCUICPositionEta.stack_position (PCUICPositionEta.appstack args []))).
  Proof using Type.
    pose proof (reduce_stack_E_Req Σ wfΣ Γ t _ h) as hr.
    rewrite reduce_args_E_spec in hr.
    set (ra := reduce_args_E Γ t args h) in *. clearbody ra. destruct ra as [t' args'].
    cbn [fst snd] in hr |- *.
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

  Lemma reduce_stack_vass Γ n decl h :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    reduce_stack_E Γ (tRel n) [] h = (tRel n, []).
  Proof using Type.
    intros hn hb. unfold reduce_stack_E.
    exact (reduce_stack_Rel_assum (wt := welltypedE) (wfP := wf_extE)
      (EF := reduce_env_facts_E) (TF := reduce_factsE) (hX := abstract_env_wfP_E X_type X)
      (normalization_in := normalization_in_wt) flags X_type X Γ n decl h hn hb).
  Qed.

  Lemma reduce_args_E_vass Γ n decl h :
    nth_error Γ n = Some decl -> decl_body decl = None ->
    reduce_args_E Γ (tRel n) [] h = (tRel n, []).
  Proof using Type.
    intros hn hb. unfold reduce_args_E.
    change (PCUICPosition.appstack [] []) with (@nil PCUICPosition.stack_entry).
    rewrite (reduce_stack_vass Γ n decl h hn hb). reflexivity.
  Qed.

End BridgeE.
