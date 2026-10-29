(* Distributed under the terms of the MIT license. *)
(** * The universe facts of a well-formed environment, for any conversion relation

  [wf_global_uctx_invariants], [wf_ext_global_uctx_invariants], [wf_consistent] and
  [global_ext_uctx_consistent] ([PCUICGlobalEnv]) are stated for
  [on_global_env cumulSpec0 P]; [levels_global_constraint]
  ([Conversion/PCUICUnivSubstitutionConv]), [wf_env_non_var_levels] and
  [wf_ext_consistent] ([PCUICTyping]) for [wf]/[wf_ext]. Their proofs read only the
  universe part of the environment. Here they have the same names and the same proofs,
  stated for [on_global_env Pcmp P] / [on_global_env_ext Pcmp P] with ANY conversion
  relation [Pcmp]. They therefore apply to [wfE]/[wf_extE] ([PCUICTypingEta],
  [Pcmp := cumulSpecE0]), and still to [wf]/[wf_ext]: a file that imports this one after
  the base files gets these versions under the base names, and its base uses still
  type-check.

  [wf_extE_wfE] is the η copy of [wf_ext_wf] ([PCUICTyping]): an instance, a coercion and a
  [core] hint, as there.

  No hypothesis: every statement is proved. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReflect PCUICTyping
     PCUICGlobalEnv PCUICTypingEta.

Section UnivFacts.
  Context {cf : checker_flags}.
  Context {Pcmp : global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P : global_env_ext -> context -> judgment -> Type}.

  Definition wf_global_uctx_invariants Σ :
    on_global_env Pcmp P Σ ->
    global_uctx_invariants (global_uctx Σ).
  Proof.
   intros HΣ. split.
   - cbn. apply global_levels_InSet.
   - unfold global_uctx.
     simpl. intros [[l ct] l'] Hctr. simpl in *.
     induction Σ in HΣ, l, ct, l', Hctr |- *.
     destruct HΣ. cbn in *.
     destruct o as [decls cu].
     now specialize (decls _ Hctr).
  Qed.

  Definition wf_ext_global_uctx_invariants Σ :
    on_global_env_ext Pcmp P Σ ->
    global_uctx_invariants (global_ext_uctx Σ).
  Proof.
   intros HΣ. split.
   - apply global_ext_levels_InSet.
   - destruct Σ as [Σ φ]. destruct HΣ as [HΣ Hφ].
     destruct (wf_global_uctx_invariants _ HΣ) as [_ XX].
     unfold global_ext_uctx, global_ext_levels, global_ext_constraints.
     simpl. intros [[l ct] l'] Hctr. simpl in *. apply ConstraintSet.union_spec in Hctr.
     destruct Hctr as [Hctr|Hctr].
     + destruct Hφ as [_ [HH _]]. specialize (HH _ Hctr). cbn in HH.
       intuition auto using LevelSet_in_union_global.
     + specialize (XX _ Hctr).
       split; apply LevelSet.union_spec; right; apply XX.
  Qed.

  Lemma wf_consistent Σ :
    on_global_env Pcmp P Σ -> consistent (global_constraints Σ).
  Proof.
    destruct Σ.
    intros [cu ong]. apply cu.
  Qed.

  Definition global_ext_uctx_consistent Σ
   : on_global_env_ext Pcmp P Σ -> consistent (global_ext_uctx Σ).2.
  Proof.
    intros HΣ. cbn. unfold global_ext_constraints.
    destruct HΣ as (_ & _ & _ & HH & _). apply HH.
  Qed.

  Lemma levels_global_constraint Σ (hΣ : on_global_env Pcmp P Σ) c :
    CS.In c (global_constraints Σ)
    -> LS.In c.1.1 (global_levels Σ)
      /\ LS.In c.2 (global_levels Σ).
  Proof.
    intros inc.
    destruct hΣ. destruct o. specialize (H c inc).
    destruct c as [[l eq] r]; apply H.
  Qed.

  Lemma wf_env_non_var_levels (Σ : global_env) (hΣ : ∥ on_global_env Pcmp P Σ ∥) :
    LS.For_all (negb ∘ Level.is_var) (PCUICLookup.global_levels Σ).
  Proof. now destruct hΣ as [[[_ [? _]] _]]. Qed.

  Lemma wf_ext_consistent (Σ : global_env_ext) :
    on_global_env_ext Pcmp P Σ -> consistent Σ.
  Proof. intros [_ [_ [_ [? _]]]]; assumption. Qed.

End UnivFacts.

#[global]
Hint Resolve wf_ext_consistent : core.

(** The η copy of [wf_ext_wf]. *)
Lemma wf_extE_wfE {cf:checker_flags} (Σ : global_env_ext) : wf_extE Σ -> wfE Σ.
Proof. intro H; apply H. Qed.
#[global]
Existing Instance wf_extE_wfE.
Coercion wf_extE_wfE : wf_extE >-> wfE.
#[global]
Hint Resolve wf_extE_wfE : core.
