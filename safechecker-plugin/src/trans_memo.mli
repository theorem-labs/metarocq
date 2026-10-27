(* The trusted memo behind [TemplateToPCUICShared.memo_trans] and
   [TemplateToPCUICShared.trans_memo_release]; see trans_memo.ml for why it is sound.  Only
   these four functions are visible to the rest of the plugin. *)

(* [memo Σ t k] returns [k ()]: computed, or the value stored for the physically same [t],
   which is stored only when its computation read no environment. *)
val memo :
  PCUICProgram.global_env_map -> Ast0.term -> (unit -> PCUICAst.term) -> PCUICAst.term

(* [release p] empties the table and returns [p]. *)
val release : PCUICAst.PCUICEnvironment.program -> PCUICAst.PCUICEnvironment.program

(* Empty the table and clear the read flag. *)
val reset : unit -> unit

(* The number of table hits since the plugin was loaded. *)
val hits : unit -> int
