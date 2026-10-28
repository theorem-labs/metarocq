(* Distributed under the terms of the MIT license. *)
(** * Instances of the erasure premises about primitive operations

    The premises below were added to erasure lemmas when environments started to
    register primitive operations.  Each lemma here shows one satisfiable at the
    concrete environments of [MetaRocq.PCUIC.PCUICPrimInstances], which register
    [Int63land].  [Σ_po_int] is the prefix of [Σ_po0] before [land] is declared. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICPrimInstances.
From MetaRocq.Erasure Require Import ErasureFunction ErasureFunctionProperties.

Import ListNotations.

(** [erases_deps_cons] (EDeps) is stated under [extraction_checker_flags]; the
    environments of [PCUICPrimInstances] are well formed under every flags. *)
Local Existing Instance extraction_checker_flags.

(** Satisfying instance of the premises of [erases_deps_cons] (EDeps): the
    universes, the [Retroknowledge.wf_retro] premise added for registered
    operations, and the declarations of [add_global_decl Σ (kn, decl)], at
    [Σ := Σ_po_int] and [(kn, decl) := (po_land_kn, ConstantDecl po_land_body)].
    The extended environment is [Σ_po0], so all three come from [Σ_po_wf_ext]. *)
Lemma Σ_po_erases_deps_cons_premises :
  on_global_univs (universes Σ_po_int) ×
  Retroknowledge.wf_retro (retroknowledge Σ_po_int) ×
  on_global_decls cumulSpec0 (lift_typing typing) (universes Σ_po_int) (retroknowledge Σ_po_int)
    ((po_land_kn, ConstantDecl po_land_body) :: declarations Σ_po_int).
Proof.
  destruct Σ_po_wf_ext as [[hu [hr hd]] _]. split; [exact hu|]. split; [exact hr|exact hd].
Qed.

(** Satisfying instance of [extends_global_env] (ErasureFunction), whose
    agreement conjuncts on [primitive_constant], [prim_op_of] and [primitive_bool]
    were added for registered operations: the prefix [Σ_po_int] and [Σ_po0], which
    differ by the declaration of [land] and share their retroknowledge. *)
Lemma Σ_po_extends_global_env : extends_global_env Σ_po_int Σ_po0.
Proof.
  split; [|split; [|split]]; try reflexivity.
  intros kn decl. rewrite /lookup_env /=.
  destruct (kn == po_int_kn) eqn:e => // h.
  apply ReflectEq.eqb_eq in e. subst kn. exact h.
Qed.

(** Satisfying instance of [equiv_env_inter] (ErasureFunction), with the same
    added conjuncts, at the same two environments, through its caller
    [extends_global_env_equiv_env] (ErasureFunctionProperties). *)
Lemma Σ_po_equiv_env_inter : equiv_env_inter Σ_po_int Σ_po0.
Proof. exact (extends_global_env_equiv_env _ _ Σ_po_extends_global_env). Qed.
