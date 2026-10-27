(* The memo behind [TemplateToPCUICShared.memo_trans] (BET-294): a Template subterm that the
   quoter shares, and whose translation reads no environment, is translated to PCUIC once,
   and its PCUIC value is shared too.

   [memo_trans => Trans_memo.memo] and [trans_memo_release => Trans_memo.release] are the
   first safechecker extraction directives that replace a computation inside the checker;
   [Print Assumptions] cannot show them; the shipped checker is correct only if
   [memo Σ t k] returns [k ()] and [release p] returns [p].

   Why it is sound.  In Rocq, [memo_trans Σ t k] is [k tt], so [trans_shared] is [trans]
   ([TemplateToPCUICShared.trans_shared_eq]).  [trans] is a pure function of [Σ] and the
   term over immutable OCaml values, and it reads [Σ] only in its [tCase] branch.  This memo
   stores only values whose computation read no environment: the computation of [t] is
   flagged when [t] is an [Ast0.Coq_tCase] node, or when any memo call made during it (a
   child computed in it or found in the table) reported a read; a flagged value is returned,
   not stored, and flags the caller.  So every stored value is the translation of a
   case-free term, which by [TemplateToPCUICShared.trans_case_free] is the same under every
   environment, and a hit on the physically same key returns what [k ()] would return.

   Shape: like the quoter's cache (quoter.ml:1077-1114), a direct-mapped table, the key
   compared with [==], a collision evicting; unlike it, a fixed 2^22 slots, allocated at the
   first store of each command (the quoter's starts at 2^10 and doubles).  The two arrays are created full of the
   first stored entry, which is valid in every slot, and the table is published by one
   assignment after both exist, so an exception (also an asynchronous one) cannot leave a
   table with keys and no values.  Until [release] or [reset], the table keeps up to 2^22
   Template keys and their PCUIC values alive (two arrays of 2^22 x 8 B = 32 MiB each,
   64 MiB, plus those nodes).  [SafeTemplateChecker.trans_program] releases it as soon as
   the program is translated.  Every plugin command that runs the checker or the
   translation calls [reset] on entry and in a [Fun.protect] finally, so no command starts
   with a table it did not build, and an exception does not keep the table alive after the
   command. *)

let size = 1 lsl 22

type table = { keys : Ast0.term array; vals : PCUICAst.term array }

let table : table option ref = ref None

(* Whether the computation in progress has read the environment so far. *)
let reads_env = ref false

let hit_count = ref 0
let hits () = !hit_count

let store slot (t : Ast0.term) (v : PCUICAst.term) =
  match !table with
  | None ->
    let keys = Array.make size t in
    let vals = Array.make size v in
    table := Some { keys; vals }
  | Some tb ->
    (* Two writes with no allocation between them, so no signal handler or callback runs
       between them: a slot that holds [t] holds the value stored with [t]. *)
    Array.unsafe_set tb.keys slot t;
    Array.unsafe_set tb.vals slot v

let memo (_ : PCUICProgram.global_env_map) (t : Ast0.term) (k : unit -> PCUICAst.term)
    : PCUICAst.term =
  let slot = Hashtbl.hash t land (size - 1) in
  match !table with
  | Some tb when Array.unsafe_get tb.keys slot == t ->
    (* A stored value read no environment, so a hit does not flag the caller. *)
    incr hit_count;
    Array.unsafe_get tb.vals slot
  | _ ->
    (* No [Fun.protect] here: a heavy object makes about 750 M memo calls, and a closure per
       call is costly.  The translation can raise [Stack_overflow] or [Out_of_memory], and
       an asynchronous exception ([Control.Timeout] from SIGALRM, [Sys.Break], or one from a
       finaliser or memprof callback) at any allocation.  It has no exception handler, so
       after an exception no memo computation of that command goes on, and a stale
       [reads_env] has no caller to mislead; it also never decides a store, because each
       miss sets its own flag from scratch.  Every plugin caller of the checker or the
       translation is wrapped in [with_trans_memo_reset], which calls [reset] on entry and
       in its finally. *)
    let outer = !reads_env in
    reads_env := (match t with Ast0.Coq_tCase _ -> true | _ -> false);
    let v = k () in
    let read = !reads_env in
    reads_env := outer || read;
    if not read then store slot t v;
    v

(* Empty the table and clear the flag. *)
let reset () =
  table := None;
  reads_env := false

let release p =
  reset ();
  p
