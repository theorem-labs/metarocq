(* SafeCheck on a term that depends on an opaque constant whose body cannot be
   read must stop with the quoter's error, not return a verdict: it cannot
   check a proof it was not given.  (Quoting with [~bypass:false] would drop
   the body and SafeCheck would accept the statement alone; see
   [quote_safecheck_program] in safechecker-plugin/src/g_metarocq_safechecker.mlg.)

   check_opaque_unreadable.sh, which the test-suite Makefile runs, compiles
   opaque_unreadable_lib.v with -vos, so its .vos file holds no opaque proof,
   and this file with -vok, which loads a library from its .vos file when that
   file is not empty.  Neither file is in _RocqProject.in: a normal build would
   give the library a .vo, with its proofs. *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From MetaRocq.TestSuite Require Import opaque_unreadable_lib.

(* Controls: a constant of the library with no opaque dependency is accepted,
   and so is an opaque constant of this file, whose body is available. *)
MetaRocq SafeCheck readable_definition.
Lemma readable_proof : True.
Proof. exact I. Qed.
MetaRocq SafeCheck readable_proof.

(* The opaque constant of the library, and a transparent constant whose body
   cites it.  [Fail] fails if SafeCheck accepts; [MetaRocq Test SafeCheck
   Aborts] fails if SafeCheck returns any verdict, or stops with an error whose
   message does not contain the quoter's. *)
Fail MetaRocq SafeCheck unreadable_proof.
MetaRocq Test SafeCheck Aborts "Cannot access opaque delayed proof" unreadable_proof.
Fail MetaRocq SafeCheck cites_unreadable.
MetaRocq Test SafeCheck Aborts "Cannot access opaque delayed proof" cites_unreadable.
