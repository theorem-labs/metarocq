(* The contract of the two trusted extraction directives of
   safechecker-plugin/theories/Extraction.v:

     Extract Constant TemplateToPCUICShared.memo_trans         => "Trans_memo.memo".
     Extract Constant TemplateToPCUICShared.trans_memo_release => "Trans_memo.release".

   In Rocq, [memo_trans Σ t k] is [k tt] and [trans_memo_release p] is [p]
   (template-pcuic/theories/TemplateToPCUICShared.v).  At extraction, both are
   replaced by hand-written OCaml (safechecker-plugin/src/trans_memo.ml), and
   the shipped checker is correct only if that OCaml keeps the same two
   equations.

   [Print Assumptions] cannot see an extraction directive: it replaces the
   EXTRACTED code, while the Rocq constant it replaces stays closed under the
   global context.  So the root assumption report of the checker is the same
   with the directives and without them, and this test -- with
   test-suite/check_extraction_directives.sh, which refuses any unlisted
   directive -- is what stands in its place.

   [MetaRocq Test Memo Contract] checks four things, and fails on any of them:
   a miss returns the continuation's own value; a hit on the physically same
   key returns [k ()] (confirmed a hit by the memo's hit counter); a key in the
   slot of a stored, physically different key gets its own [k ()] and not the
   stored value (the colliding pair is searched for, so the part cannot pass
   vacuously); and [release p] returns [p] itself. *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

MetaRocq Test Memo Contract nat.
