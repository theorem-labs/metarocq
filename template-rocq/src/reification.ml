
(** The primitive operations the quoted environment registers: the quoter-side
    image of [MetaRocq.Common.PrimitiveOps.prim_op].  It is the same type for
    every quoter, so the kernel operations are classified once
    ([Quoter.prim_op_of_kernel]) and each quoter only maps a case to its own
    representation of the constructor. *)
type prim_op =
  | POInt63eq | POInt63lt | POInt63le
  | POInt63land | POInt63lor | POInt63lsl | POInt63lsr | POInt63sub
  | POStringlength | POStringget

module type Reification =
sig
  type t (* this represented quoted Gallina terms *)

  type quoted_ident
  type quoted_int
  type quoted_bool
  type quoted_name
  type quoted_aname
  type quoted_relevance
  type quoted_sort
  type quoted_cast_kind
  type quoted_kernel_name
  type quoted_inductive
  type quoted_proj
  type quoted_int63
  type quoted_float64
  type quoted_pstring

  type quoted_global_reference

  type quoted_sort_quality_or_set
  type quoted_constraint_type
  type quoted_univ_constraint
  type quoted_univ_constraints
  type quoted_univ_level
  type quoted_univ_instance
  type quoted_univ_context
  type quoted_contextset
  type quoted_abstract_univ_context
  type quoted_variance
  type quoted_universes_decl

  type quoted_universes_entry
  type quoted_ind_entry = quoted_ident * t * quoted_ident list * t list
  type quoted_definition_entry
  type quoted_parameter_entry
  type quoted_constant_entry
  type quoted_mind_entry
  type quoted_mind_finiteness
  type quoted_entry

  (* Local contexts *)
  type quoted_context_decl
  type quoted_context

  type quoted_one_inductive_body
  type quoted_mutual_inductive_body
  type quoted_constant_body
  type quoted_global_decl
  type quoted_global_declarations
  type quoted_retroknowledge
  type quoted_global_env
  type quoted_program  (* the return type of quote_recursively *)

end
