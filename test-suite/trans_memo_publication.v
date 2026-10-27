(* The translation memo (safechecker-plugin/src/trans_memo.ml) publishes its
   table once, after both arrays exist: an exception between the two
   allocations leaves no table.  Fails if that fix is undone. *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

MetaRocq Test Memo Publication.
