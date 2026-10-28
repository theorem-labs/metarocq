(** Reduction of primitive operations.

    The verified checker reduces an application of a registered primitive operation whose
    arguments are all primitive literals to the value the operation computes: for an operation
    [c] of arity [n] registered in the environment's retroknowledge,

      c l_1 … l_n  ~>  v      when every l_i is a literal of the tag the operation expects
                              and the operation's denotation returns v,

    read back as a literal for an integer or string result and as the registered constructor of
    [bool] or [comparison] otherwise. This mirrors the kernel, which fires a primitive only when
    it is saturated and every argument is a value, and leaves an unsaturated or stuck application
    alone.

    Part A reproduces the computations that occur in reflexive proofs over hexadecimal memory
    images: the byte count of a chunk, the bounds and nybble tests of a byte decoder, and the
    little-endian composition of a word. Part B pins each operation at its boundary cases, and
    separates operations of equal type from one another. Part C contains the operations that are
    *not* registered: they must stay axioms, so their [Fail] must keep holding. Part D checks the
    cases the checker must still refuse, and the ones it must still accept.

    Each [MetaRocq SafeCheck] prints "Environment is well-formed …" when it succeeds. Each
    [Fail MetaRocq SafeCheck] prints the refusal, so the expected message appears in the log. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From Stdlib Require Import ZArith.
From Corelib Require Import BinNums IntDef PrimInt63 Uint63Axioms PrimString.
Local Open Scope uint63_scope.

(** A hexadecimal chunk, the shape in which memory images store segment bytes. *)
Definition po_seg : PrimString.string := "0a1b2c"%pstring.

(** ** Part A — the computations of reflexive proofs over memory images *)

(** The byte count of a chunk: [PrimString.length], then [Uint63Axioms.to_Z], whose [is_even]
    test calls [eqb (land i 1) 0] once per bit — a redex whose arguments are not literals, so
    the checker must reduce arguments before it can fire. *)
Definition po_chunk_bytes
  : Z.eqb (Uint63Axioms.to_Z (PrimString.length po_seg)) (Zpos (xO (xI xH))) = true
  := eq_refl.
MetaRocq SafeCheck po_chunk_bytes.

(** The bounds test of a byte decoder and a nybble test: [of_Z] (which calls [lsl] and [lor]),
    [length], [ltb], [eqb], [sub], [get] and [leb]. *)
Definition po_in_bounds (s : PrimString.string) (ci1 : int) : bool :=
  orb (PrimInt63.ltb ci1 (PrimString.length s))
      (PrimInt63.eqb ci1 (PrimInt63.sub (PrimString.length s) 1)).
Definition po_is_hex (c : int) : bool :=
  orb (andb (PrimInt63.leb 48 c) (PrimInt63.leb c 57))
      (andb (PrimInt63.leb 97 c) (PrimInt63.leb c 102)).
Definition po_decode_ok
  : andb (po_in_bounds po_seg (Uint63Axioms.of_Z (Zpos (xI xH))))
         (po_is_hex (PrimString.get po_seg (Uint63Axioms.of_Z (Zpos (xI xH))))) = true
  := eq_refl.
MetaRocq SafeCheck po_decode_ok.

(** One decoded byte compared with a constant. *)
Definition po_z48 : Z := Zpos (xO (xO (xO (xO (xI xH))))).   (* 48, the character '0' *)
Definition po_nybble (c : int) : Z := Z.sub (Uint63Axioms.to_Z c) po_z48.
Definition po_byte_digit : Z.eqb (po_nybble (PrimString.get po_seg 2)) (Zpos xH) = true
  := eq_refl.
MetaRocq SafeCheck po_byte_digit.

(** A little-endian word composed from two decoded bytes, as an instruction fetch does. *)
Definition po_hexval (c : int) : Z :=
  if andb (PrimInt63.leb 48 c) (PrimInt63.leb c 57)
  then (Uint63Axioms.to_Z c - 48)%Z else (Uint63Axioms.to_Z c - 87)%Z.
Definition po_byte_at (s : PrimString.string) (i : Z) : option Z :=
  let ci  := Uint63Axioms.of_Z (2 * i)%Z in
  let ci1 := Uint63Axioms.of_Z (2 * i + 1)%Z in
  if po_in_bounds s ci1
  then Some (po_hexval (PrimString.get s ci) * 16 + po_hexval (PrimString.get s ci1))%Z
  else None.
Definition po_word2 (s : PrimString.string) : option Z :=
  match po_byte_at s 0, po_byte_at s 1 with
  | Some b0, Some b1 => Some (b0 + 256 * b1)%Z
  | _, _ => None
  end.
Definition po_fetch_word
  : (match po_word2 po_seg with Some w => Z.eqb w 6922 | None => false end) = true
  := eq_refl.   (* bytes 0x0a and 0x1b, little-endian: 10 + 256 * 27 *)
MetaRocq SafeCheck po_fetch_word.

(** ** Part B — boundary cases and separators, one per operation *)

Definition po_eq_refl_args : PrimInt63.eqb 7 7 = true := eq_refl.
Definition po_leb_equal    : PrimInt63.leb 2 2 = true := eq_refl.   (* separates leb from ltb *)
Definition po_ltb_equal    : PrimInt63.ltb 2 2 = false := eq_refl.  (* separates ltb from leb *)
Definition po_ltb_unsigned : PrimInt63.ltb 0 Uint63Axioms.max_int = true := eq_refl.
Definition po_leb_unsigned : PrimInt63.leb Uint63Axioms.max_int 0 = false := eq_refl.
Definition po_sub_wraps    : PrimInt63.eqb (PrimInt63.sub 0 1) Uint63Axioms.max_int = true
  := eq_refl.
Definition po_land_masks   : PrimInt63.eqb (PrimInt63.land 6 3) 2 = true := eq_refl.
Definition po_lor_sets     : PrimInt63.eqb (PrimInt63.lor 6 3) 7 = true := eq_refl.
Definition po_lsl_63       : PrimInt63.eqb (PrimInt63.lsl 1 63) 0 = true := eq_refl.
Definition po_lsr_63       : PrimInt63.eqb (PrimInt63.lsr Uint63Axioms.max_int 63) 0 = true
  := eq_refl.
(* The two shift-by-63 cases hold of both shifts, so they do not separate lsl from lsr; these do. *)
Definition po_lsl_shifts   : PrimInt63.eqb (PrimInt63.lsl 1 1) 2 = true := eq_refl.
Definition po_lsr_shifts   : PrimInt63.eqb (PrimInt63.lsr 2 1) 1 = true := eq_refl.
Definition po_get_out_of_range : PrimInt63.eqb (PrimString.get po_seg 100) 0 = true := eq_refl.
Definition po_length_empty : PrimInt63.eqb (PrimString.length ""%pstring) 0 = true := eq_refl.
MetaRocq SafeCheck po_eq_refl_args.
MetaRocq SafeCheck po_leb_equal.
MetaRocq SafeCheck po_ltb_equal.
MetaRocq SafeCheck po_ltb_unsigned.
MetaRocq SafeCheck po_leb_unsigned.
MetaRocq SafeCheck po_sub_wraps.
MetaRocq SafeCheck po_land_masks.
MetaRocq SafeCheck po_lor_sets.
MetaRocq SafeCheck po_lsl_63.
MetaRocq SafeCheck po_lsr_63.
MetaRocq SafeCheck po_get_out_of_range.
MetaRocq SafeCheck po_lsl_shifts.
MetaRocq SafeCheck po_lsr_shifts.
MetaRocq SafeCheck po_length_empty.

(** ** Part C — operations that are not registered must stay axioms

    [lxor], [ltsb] and [asr] are outside the operation table, so the checker must refuse these,
    exactly as it refuses every primitive application today. An acceptance here means an entry
    of the table maps a kernel operation that the table does not contain. Expected message:
    "Type error: Types are not convertible". *)

Definition po_unregistered_lxor : PrimInt63.eqb (PrimInt63.lxor 6 3) 5 = true := eq_refl.
Definition po_unregistered_ltsb : PrimInt63.ltsb Uint63Axioms.max_int 0 = true := eq_refl.
Definition po_unregistered_asr
  : PrimInt63.eqb (PrimInt63.asr Uint63Axioms.max_int 1) Uint63Axioms.max_int = true := eq_refl.
(* expect: Types are not convertible *)
Fail MetaRocq SafeCheck po_unregistered_lxor.
(* expect: Types are not convertible *)
Fail MetaRocq SafeCheck po_unregistered_ltsb.
(* expect: Types are not convertible *)
Fail MetaRocq SafeCheck po_unregistered_asr.

(** ** Part D — conversion, saturation and stuck applications *)

(** Two applications of operations that are not syntactically equal, which conversion must
    decide by firing both sides. *)
Definition po_conv_same_op : PrimInt63.eqb 1 2 = PrimInt63.eqb 2 1 := eq_refl.
Definition po_conv_diff_op : PrimInt63.eqb 1 1 = PrimInt63.leb 1 1 := eq_refl.
MetaRocq SafeCheck po_conv_same_op.
MetaRocq SafeCheck po_conv_diff_op.

(** An application that beta-reduction makes saturated. *)
Definition po_saturated_by_beta : (fun f : int -> bool => f 2) (PrimInt63.eqb 1) = false
  := eq_refl.
MetaRocq SafeCheck po_saturated_by_beta.

(** A saturated application one of whose arguments is a beta redex.  The
    argument is neither neutral nor a literal, so the machine must reduce it
    before the operation can fire: a weak-head normal form here would make the
    whole term stuck although it computes to [false]. *)
Definition po_beta_arg : PrimInt63.eqb ((fun x : int => x) 1) 2 = false := eq_refl.
MetaRocq SafeCheck po_beta_arg.

(** An application stuck on a variable stays convertible to itself, and to nothing else. *)
Definition po_stuck_reflexive : forall x : int, PrimInt63.eqb x 1 = PrimInt63.eqb x 1
  := fun x => eq_refl.
MetaRocq SafeCheck po_stuck_reflexive.

(** No computation at all: accepted before and after the rule exists. *)
Definition po_no_computation (x : int) : PrimInt63.eqb x x = PrimInt63.eqb x x := eq_refl.
MetaRocq SafeCheck po_no_computation.

(** ** Part E — a known completeness gap: positivity through a primitive operation

    The positivity checker reduces a constructor argument type with its own weak-head
    machine, [whd_fuel] (safechecker/theories/PCUICPositivityCheck.v), and that machine
    *refuses* when it meets a registered primitive operation instead of firing it. That
    is sound and costs only completeness: positivity is refused for a constructor argument
    whose weak-head reduction has to pass through an operation, although Rocq's kernel,
    which fires the operation inside [whd_all], accepts the same declaration.

    The two inductives below differ in one thing only. Both use the shape that
    test-suite/positivity_red.v already accepts as [pr_iota]: an argument type that
    reaches the block by reducing a match. In [po_pos_ctl] the scrutinee is the
    constructor [true]; in [po_pos_gap] it is [eqb 1 1], which is [true] only once the
    operation fires. So the control's acceptance shows that positivity reduces this
    shape, and the gap's refusal is then due to the operation and nothing else. Rocq's
    kernel accepts both.

    The [Fail] is expected. It must keep holding until someone makes [whd_fuel] fire
    registered operations. When it stops holding, that change has landed, and this case
    must be moved to the accepted side on purpose, not silently. *)

Definition po_pos_sel (b : bool) (X : Set) : Set := if b then X else nat.

Inductive po_pos_ctl : Set := po_pos_ctl_c : po_pos_sel true po_pos_ctl -> po_pos_ctl.
MetaRocq SafeCheck po_pos_ctl.

Inductive po_pos_gap : Set :=
  po_pos_gap_c : po_pos_sel (PrimInt63.eqb 1 1) po_pos_gap -> po_pos_gap.
(* expect: Positivity: *)
Fail MetaRocq SafeCheck po_pos_gap.
