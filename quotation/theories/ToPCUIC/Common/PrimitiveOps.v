From MetaRocq.Quotation.ToPCUIC Require Import Stdlib.Init.
From MetaRocq.Common Require Import PrimitiveOps.

(** BET-319: [Retroknowledge.t] gained the operation table
    [retro_ops : list (kername * prim_op)], so quoting a retroknowledge record
    needs the operations themselves quotable.  [prim_op] is an enumeration, so
    the standard structural instance applies, exactly as for [prim_tag] in the
    sibling [Primitive.v]. *)
#[export] Instance quote_prim_op : ground_quotable prim_op := ltac:(destruct 1; exact _).
