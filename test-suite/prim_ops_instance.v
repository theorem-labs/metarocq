(** * The assumptions of the primitive-operation instances

    The instances are proved in the library: [MetaRocq.PCUIC.PCUICPrimInstances]
    (well-formed environments that register an operation, for integer, boolean
    and string-tagged operations) and [MetaRocq.PCUIC.PCUICPrimInstanceRules]
    (a firing step, its subject reduction, a stuck neutral, and the typing of an
    operation head, on those environments).  This file prints what each rests
    on; [check_assumptions.sh], run by the test-suite Makefile, fails if any
    axiom outside the allowed list appears. *)

From MetaRocq.PCUIC Require Import PCUICPrimInstances PCUICPrimInstanceRules.

(** Well-formedness (premise [wf]: [on_global_univs], [wf_retro],
    [on_global_decls] with [on_prim_decl_d]). *)
Print Assumptions Σ_po_wf_ext.
Print Assumptions Σ_po_bool_wf_ext.
Print Assumptions Σ_po_str_wf_ext.

(** [prim_op_of Σ c = None] beside a declared bodiless constant, and the
    section [BelowAxiom] of PCUICPrimCanonical. *)
Print Assumptions po_int_not_op.
Print Assumptions Σ_po_sort_not_below_int.

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
