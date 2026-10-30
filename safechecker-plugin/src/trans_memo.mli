(* The trusted memo behind [TemplateToPCUICShared.memo_trans] and
   [TemplateToPCUICShared.trans_memo_release]; see trans_memo.ml for why it is sound.  The
   plugin sees these four functions, plus the [test_*] hooks of the regression tests
   test-suite/trans_memo_{publication,reset,rejects}.v. *)

(* [memo Σ t k] returns [k ()]: computed, or the value stored for the physically same [t],
   which is stored only when its computation read no environment. *)
val memo :
  PCUICProgram.global_env_map -> Ast0.term -> (unit -> PCUICAst.term) -> PCUICAst.term

(* [release p] empties the table and returns [p]. *)
val release : PCUICAst.PCUICEnvironment.program -> PCUICAst.PCUICEnvironment.program

(* Empty the table and the read flag.  Test arms are left alone: the test command that set
   one disarms it in its finally. *)
val reset : unit -> unit

(* The number of table hits since the plugin was loaded. *)
val hits : unit -> int

(* Regression-test hooks; inert unless armed.  An armed hook raises the user error
   "trans_memo test" once and then disarms; it never returns another value, and never
   writes a key or a value. *)

(* The next first store raises after its keys array is built and before its values array
   is built, so before the table is published. *)
val test_arm_raise_between_allocations : unit -> unit

(* The memo raises right after its [n]-th successful store from now, when the table is
   published and non-empty.  The arm survives [reset], so it reaches the translation of a
   command that resets on entry. *)
val test_arm_raise_after_stores : int -> unit

(* Drop a live arm and a pending request. *)
val test_disarm : unit -> unit

(* Whether an arm is live or requested. *)
val test_pending : unit -> bool

(* [`Empty]: no table; [`Torn]: keys published without their values; [`Consistent]
   otherwise. *)
val test_state : unit -> [ `Empty | `Consistent | `Torn ]

(* Store one case-free entry ([tRel 0] for [tRel 0]) through the memo. *)
val test_populate : unit -> unit

(* The slot a key lands in; [MetaRocq Test Memo Contract] searches with it for two
   distinct keys in one slot. *)
val test_slot : Ast0.term -> int
