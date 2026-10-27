(* The memo behind [TemplateToPCUICShared.memo_trans] (BET-294): a Template subterm that the
   quoter shares, and whose translation reads no environment, is translated to PCUIC once,
   and its PCUIC value is shared too.

   This is the first safechecker extraction directive that replaces a computation inside the
   checker; [Print Assumptions] cannot show it; the shipped checker is correct only if
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

   Shape: as the quoter's cache (quoter.ml:1077-1114), a direct-mapped table of 2^22 slots,
   the key compared with [==], a collision evicting.  The arrays are created full of the
   first stored entry, which is valid in every slot.  Until [release] or [reset], the table
   keeps up to 2^22 Template keys and their PCUIC values alive (two arrays of 2^22 x 8 B =
   32 MiB each, 64 MiB, plus those nodes); [SafeTemplateChecker.trans_program] releases it
   as soon as the program is translated, and the plugin calls [reset] in a [Fun.protect]
   finally around SafeCheck and the sharing test, so an exception cannot leave it alive. *)

let size = 1 lsl 22

let keys : Ast0.term array ref = ref [||]
let vals : PCUICAst.term array ref = ref [||]

(* Whether the computation in progress has read the environment so far. *)
let reads_env = ref false

let hit_count = ref 0
let hits () = !hit_count

let store slot (t : Ast0.term) (v : PCUICAst.term) =
  if Array.length !keys = 0 then begin
    keys := Array.make size t;
    vals := Array.make size v
  end else begin
    Array.unsafe_set !keys slot t;
    Array.unsafe_set !vals slot v
  end

let memo (_ : PCUICProgram.global_env_map) (t : Ast0.term) (k : unit -> PCUICAst.term)
    : PCUICAst.term =
  let slot = Hashtbl.hash t land (size - 1) in
  let ks = !keys in
  if Array.length ks <> 0 && Array.unsafe_get ks slot == t then begin
    (* A stored value read no environment, so a hit does not flag the caller. *)
    incr hit_count;
    Array.unsafe_get !vals slot
  end else begin
    (* No [Fun.protect] here: a heavy object makes about 750 M memo calls, and a closure per
       call is costly.  The translation raises nothing but [Stack_overflow] or
       [Out_of_memory], and it has no exception handler, so after an exception no memo
       computation goes on: the exception reaches the plugin, whose [Fun.protect] finally
       calls [reset].  A stale [reads_env] therefore has no caller to mislead, and [reset]
       clears it with the table. *)
    let outer = !reads_env in
    reads_env := (match t with Ast0.Coq_tCase _ -> true | _ -> false);
    let v = k () in
    let read = !reads_env in
    reads_env := outer || read;
    if not read then store slot t v;
    v
  end

(* Empty the table and clear the flag. *)
let reset () =
  keys := [||];
  vals := [||];
  reads_env := false

let release p =
  reset ();
  p
