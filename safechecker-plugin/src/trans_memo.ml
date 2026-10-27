(* The memo behind [TemplateToPCUICShared.memo_trans] (BET-294): a Template subterm that the
   quoter shares, and whose translation reads no environment, is translated to PCUIC once,
   and its PCUIC value is shared too.

   [memo_trans => Trans_memo.memo] and [trans_memo_release => Trans_memo.release] are the
   first safechecker extraction directives that replace a computation inside the checker;
   [Print Assumptions] cannot show them; the shipped checker is correct only if
   [memo Σ t k] returns [k ()] and [release p] returns [p].  With a test hook armed (see
   below), [memo] can instead raise the user error "trans_memo test"; it never returns
   another value, and no hook writes a key or a value.

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
   command.

   The [test_*] functions exist only for the regression tests
   test-suite/trans_memo_{publication,reset,rejects}.v.  They are inert unless armed, and
   armed they can only raise.  Their cost on the hot path: a miss that stores pays one
   boolean test ([test_armed]), the first store of a table one more, and a hit pays
   nothing.  [memo] is [@inline], so the split into [memo_core] costs no call. *)

let size = 1 lsl 22

type table = { keys : Ast0.term array; vals : PCUICAst.term array }

let table : table option ref = ref None

(* Whether the computation in progress has read the environment so far. *)
let reads_env = ref false

let hit_count = ref 0
let hits () = !hit_count

(* Regression-test hooks; see the header.  An arm is live from the moment the test command
   sets it until that command's [Fun.protect] finally disarms it.  [reset] does not disarm:
   test (c) arms the memo and then runs [MetaRocq Test SafeCheck Rejects], whose own entry
   [reset] must not drop the arm.  Only the [MetaRocq Test Memo …] commands arm, and each
   disarms in its finally, so no arm outlives its command. *)
let test_armed = ref false
let test_raise_between = ref false
let test_stores_left = ref 0
let test_rearm () = test_armed := !test_raise_between || !test_stores_left > 0
let test_error () = CErrors.user_err (Pp.str "trans_memo test")

let store slot (t : Ast0.term) (v : PCUICAst.term) =
  match !table with
  | None ->
    let keys = Array.make size t in
    if !test_armed && !test_raise_between then begin
      test_raise_between := false; test_rearm (); test_error ()
    end;
    let vals = Array.make size v in
    table := Some { keys; vals }
  | Some tb ->
    (* Two writes with no allocation between them, so no signal handler or callback runs
       between them: a slot that holds [t] holds the value stored with [t]. *)
    Array.unsafe_set tb.keys slot t;
    Array.unsafe_set tb.vals slot v

let test_after_store () =
  if !test_stores_left > 0 then begin
    decr test_stores_left;
    if !test_stores_left = 0 then begin test_rearm (); test_error () end
  end

let memo_core (t : Ast0.term) (k : unit -> PCUICAst.term) : PCUICAst.term =
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
    if not read then begin
      store slot t v;
      if !test_armed then test_after_store ()
    end;
    v

let[@inline] memo (_ : PCUICProgram.global_env_map) (t : Ast0.term) (k : unit -> PCUICAst.term)
    : PCUICAst.term =
  memo_core t k

(* Empty the table and the read flag.  Test arms are left alone; the test command that set
   one disarms it in its finally. *)
let reset () =
  table := None;
  reads_env := false

let release p =
  reset ();
  p

let test_arm_raise_between_allocations () =
  test_raise_between := true; test_rearm ()

let test_arm_raise_after_stores n =
  test_stores_left := max n 0; test_rearm ()

let test_disarm () =
  test_raise_between := false;
  test_stores_left := 0;
  test_rearm ()

let test_pending () = !test_armed

(* [`Torn] is a table whose keys were published without their values: unreachable with the
   single publication, reachable with the old two-reference table. *)
let test_state () =
  match !table with
  | None -> `Empty
  | Some tb ->
    if Array.length tb.keys > 0 && Array.length tb.vals <> Array.length tb.keys then `Torn
    else `Consistent

(* One case-free entry: [tRel 0] translates to [tRel 0] under every environment. *)
let test_populate () =
  ignore (memo_core (Ast0.Coq_tRel Datatypes.O) (fun () -> PCUICAst.Coq_tRel Datatypes.O))
