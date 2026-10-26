From MetaRocq.TestPlugin Require Import Loader.

(* The quoter caches the quoted value of each kernel subterm by physical
   equality. Both commands build their kernel terms in OCaml and fail with an
   error if the cache contract does not hold. *)

(* A term with 2^60 tree nodes and 61 distinct nodes. Without sharing,
   quotation does not return. *)
MetaRocq Test Quotation Sharing.

(* More distinct subterms than the cache keeps, so the table resizes and
   evicts. Quotations through one cache and through a fresh one are equal. *)
MetaRocq Test Quotation Cache.
