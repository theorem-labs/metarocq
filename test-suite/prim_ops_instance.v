(** * The assumptions of the primitive-operation instances

    The instances are proved in the libraries:
    - [MetaRocq.PCUIC.PCUICPrimInstances]: well-formed environments that register
      an operation (integer, boolean and string-tagged operations), for every
      checker flags, and each per-declaration and per-predicate fact of the
      environment condition as its own lemma;
    - [MetaRocq.PCUIC.PCUICPrimInstanceRules]: on those environments, a firing step
      and its subject reduction, a stuck neutral, the typing of an operation head,
      the premises of [typing_spine_prim_type], and a well-typed case on a stuck
      application;
    - [MetaRocq.SafeChecker.PCUICPrimInstanceChecker]: the checker's lemmas about
      the environment condition, at a concrete abstract environment built from
      those environments, and the [wty]/[ond] arguments of its checks;
    - [MetaRocq.Erasure.EPrimInstances]: the erasure premises.
    The translation premises are instantiated in [MetaRocq.PCUIC.PCUICPrimInstanceTrans]
    and [prim_ops_instance_trans.v].  This file prints what each instance rests on;
    [check_assumptions.sh], run by the test-suite Makefile, fails if any axiom
    outside the allowed list appears. *)

From MetaRocq.PCUIC Require Import PCUICPrimInstances PCUICPrimInstanceRules PCUICPrimInstanceTrans.
From MetaRocq.SafeChecker Require Import PCUICPrimInstanceChecker.
From MetaRocq.Erasure Require Import EPrimInstances.

(** Well-formedness (premise [wf]: [on_global_univs], [wf_retro],
    [on_global_decls] with [on_prim_decl_d]). *)
Print Assumptions Σ_po_wf_ext.
Print Assumptions Σ_po_bool_wf_ext.
Print Assumptions Σ_po_str_wf_ext.

(** [on_prim_decl] per declaration, and the predicates it is made of. *)
Print Assumptions Σ_po_land_on_prim_decl.
Print Assumptions Σ_po_bool_ind_on_prim_decl.
Print Assumptions Σ_po_bool_eqb_on_prim_decl.
Print Assumptions Σ_po_str_len_on_prim_decl.
Print Assumptions Σ_po_str_get_on_prim_decl.
Print Assumptions Σ_po_tag_int.
Print Assumptions Σ_po_str_get_tag_string.
Print Assumptions Σ_po_result_SInt.
Print Assumptions Σ_po_bool_result_SBool.
Print Assumptions Σ_po_land_on_prim_op_constant.
Print Assumptions po_bool_on_prim_bool_decl.

(** [prim_op_of Σ c = None] beside a declared bodiless constant, and the
    section [BelowAxiom] of PCUICPrimCanonical. *)
Print Assumptions po_int_not_op.
Print Assumptions Σ_po_sort_not_below_int.

(** The premises of [typing_spine_prim_type]. *)
Print Assumptions Σ_po_typing_spine_prim_type.

(** The firing bundle of [red_prim_op], and [sr_prim_op]. *)
Print Assumptions Σ_po_fires.
Print Assumptions Σ_po_fires_sr.
Print Assumptions Σ_po_bool_fires.
Print Assumptions Σ_po_bool_fires_sr.

(** The weak-head bundle ([whne_primapp_stuck]). *)
Print Assumptions Σ_po_stuck.

(** The typing bundle of an operation head. *)
Print Assumptions Σ_po_stuck_typed.
Print Assumptions Σ_po_land_head_type.
Print Assumptions Σ_po_stuck_typing_inv.

(** The [welltyped] premise of [reduced_case_discriminee_whne]. *)
Print Assumptions Σ_po_bool_case_welltyped.

(** The checker's lemmas at a concrete abstract environment, and the [wty] and
    [ond] arguments of [check_prim_op_constant]/[check_prim_op_decl]. *)
Print Assumptions inst_abstract_prim_op_of_spec.
Print Assumptions inst_abstract_prim_op_type_spec.
Print Assumptions inst_prim_op_tag_declared_of_lookup.
Print Assumptions inst_on_prim_op_result_bool_of_lookup.
Print Assumptions inst_prim_op_type_welltyped.
Print Assumptions inst_on_prim_op_constant_of_checks.
Print Assumptions inst_on_prim_decl_const_none.
Print Assumptions inst_on_prim_decl_const_some.
Print Assumptions inst_on_prim_decl_ind.
Print Assumptions inst_abstract_readback_correct.
Print Assumptions inst_check_prim_op_constant_wty.
Print Assumptions inst_check_prim_op_decl_ond.

(** The erasure premises. *)
Print Assumptions Σ_po_erases_deps_cons_premises.
Print Assumptions Σ_po_extends_global_env.
Print Assumptions Σ_po_equiv_env_inter.

(** The expand-lets translation's premises ([trans_on_prim_decl]). *)
Print Assumptions trans_Σ_po_land_on_prim_decl.
