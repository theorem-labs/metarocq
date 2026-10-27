(* Every command that runs the checker or the translation empties the memo's
   table on entry, so it never starts with a table it did not build.  Fails if
   that fix is undone. *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

MetaRocq Test Memo Reset On Entry.
