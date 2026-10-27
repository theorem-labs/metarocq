(* MetaRocq Test SafeCheck Rejects runs inside the memo's reset wrapper: when
   its translation raises after the table is published, the table does not
   outlive the command.  The command below arms the memo, runs the rejection
   test, requires that the memo's own error was the one raised, disarms, and
   then checks the table from outside that wrapper.  Fails if that fix is
   undone. *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

MetaRocq Test Memo Rejects Leak nat.
