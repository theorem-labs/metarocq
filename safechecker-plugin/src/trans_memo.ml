(* The memo behind [TemplateToPCUICShared.memo_trans] (BET-294): a Template subterm that the
   quoter shares is translated to PCUIC once, and its PCUIC value is shared too.

   Why it is sound.  In Rocq, [memo_trans Σ t k] is [k tt], so [trans_shared] is [trans]
   ([TemplateToPCUICShared.trans_shared_eq]) and no statement of the checker changes.  This
   memo returns, for [t] under [Σ], the value that an earlier call computed for the
   physically same [t], and [trans Σ t] is a pure function of [Σ] and [t] over immutable
   OCaml values, so a hit under the physically same [Σ] is the value [trans] computes.
   [trans] reads [Σ] only in its [tCase] branch, so an entry whose computation met no
   [tCase] node (its own node, a node translated under it, or a reused entry) is reused
   under any [Σ], and every other entry only under the physically same [Σ].

   Direct-mapped like the quoter's cache: one slot per bucket, the key compared with [==],
   a collision evicts.  [release] drops the table once a program is translated, so the
   table does not keep the Template program alive. *)

let size = 1 lsl 22

(* A key that no Template term is physically equal to. *)
let empty : Obj.t = Obj.repr (ref ())

let keys : Obj.t array ref = ref [||]
let sigs : Obj.t array ref = ref [||]
let vals : Obj.t array ref = ref [||]
(* '\001': the entry's computation did not read the environment; '\000': it may have. *)
let pure : Bytes.t ref = ref Bytes.empty

(* While a node is translated: no [tCase] met so far in its computation. *)
let cur_pure = ref true

let hit_count = ref 0
let hits () = !hit_count

let alloc () =
  if Array.length !keys = 0 then begin
    keys := Array.make size empty;
    sigs := Array.make size empty;
    vals := Array.make size empty;
    pure := Bytes.make size '\000'
  end

let memo (sigma : 'e) (t : Ast0.term) (f : unit -> 'b) : 'b =
  alloc ();
  let s = Hashtbl.hash t land (size - 1) in
  let entry_pure = Bytes.unsafe_get !pure s = '\001' in
  if Array.unsafe_get !keys s == Obj.repr t
     && (entry_pure || Array.unsafe_get !sigs s == Obj.repr sigma) then begin
    incr hit_count;
    if not entry_pure then cur_pure := false;
    Obj.obj (Array.unsafe_get !vals s)
  end else begin
    let outer = !cur_pure in
    cur_pure := (match t with Ast0.Coq_tCase _ -> false | _ -> true);
    let v = f () in
    let p = !cur_pure in
    cur_pure := outer && p;
    (* [f] translates only through [memo], never [release]; the check keeps the unsafe
       writes below in bounds even if that changes. *)
    if Array.length !keys = size then begin
      Array.unsafe_set !keys s (Obj.repr t);
      Array.unsafe_set !sigs s (Obj.repr sigma);
      Array.unsafe_set !vals s (Obj.repr v);
      Bytes.unsafe_set !pure s (if p then '\001' else '\000')
    end;
    v
  end

let release x =
  keys := [||];
  sigs := [||];
  vals := [||];
  pure := Bytes.empty;
  cur_pure := true;
  x
