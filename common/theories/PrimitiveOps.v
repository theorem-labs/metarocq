(* Distributed under the terms of the MIT license. *)
(** * Primitive operations: the one interface used by reduction and the checker

  Every computation on primitive values goes through [prim_op_denote].  This
  file proves two facts about it, [prim_op_denote_args] and
  [prim_op_denote_shape], and the satisfying instance [prim_op_denote_total]
  (see its comment); other files prove more, e.g. [prim_op_denote_length]
  (PCUICParallelReductionConfluence) and [prim_op_denote_nil] (PCUICNormal).
  [prim_op] is the set of registered operations,
  [prim_lit] the literal arguments they consume and [prim_result] the values they
  produce.  The readback of a result into a term, and the reader turning a term's
  payload into a literal, are per-language and live beside each language's
  payload construction (PCUIC: [PCUICPrimitiveRed]; Template: [Typing]).

  This file is deliberately the only place in [common] that inspects a
  [PrimInt63.int] or a [PrimString.string] payload. *)

From Stdlib Require Import Uint63 PString.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Primitive.
From Equations.Prop Require Import Classes EqDecInstances.

(** The registered operations. *)
Variant prim_op :=
  | Int63eq | Int63lt | Int63le
  | Int63land | Int63lor | Int63lsl | Int63lsr | Int63sub
  | Stringlength | Stringget.
Derive NoConfusion EqDec for prim_op.

#[global] Instance prim_op_reflect : ReflectEq prim_op := EqDec_ReflectEq prim_op.

(** The shape of a result: which kind of term it is read back to. *)
Variant prim_shape := SInt | SBool.
Derive NoConfusion EqDec for prim_shape.

Record prim_op_info := { po_args : list prim_tag; po_shape : prim_shape }.

Definition info (op : prim_op) : prim_op_info :=
  match op with
  | Int63eq | Int63lt | Int63le =>
      {| po_args := [primInt; primInt]; po_shape := SBool |}
  | Int63land | Int63lor | Int63lsl | Int63lsr | Int63sub =>
      {| po_args := [primInt; primInt]; po_shape := SInt |}
  | Stringlength => {| po_args := [primString]; po_shape := SInt |}
  | Stringget => {| po_args := [primString; primInt]; po_shape := SInt |}
  end.

(** The operation fires only on an application of exactly this many arguments. *)
Definition arity (op : prim_op) : nat := #|po_args (info op)|.

(** Raw payloads: the same types as Template's [tInt]/[tString] and PCUIC's
    [prim_model]. *)
Variant prim_lit := LInt (i : PrimInt63.int) | LString (s : PrimString.string).
Variant prim_result := RInt (i : PrimInt63.int) | RBool (b : bool).

Definition lit_tag (l : prim_lit) : prim_tag :=
  match l with
  | LInt _ => primInt
  | LString _ => primString
  end.

Definition result_has_shape (r : prim_result) (s : prim_shape) : Prop :=
  match r, s with
  | RInt _, SInt => True
  | RBool _, SBool => True
  | _, _ => False
  end.

(** ** The interface

  Option 1 realises every operation by Rocq's own primitive, the very function
  the kernel calls (see the lane's design, §10.1). *)
Definition prim_op_denote (op : prim_op) (ls : list prim_lit) : option prim_result :=
  match op, ls with
  | Int63eq, [LInt i; LInt j] => Some (RBool (PrimInt63.eqb i j))
  | Int63lt, [LInt i; LInt j] => Some (RBool (PrimInt63.ltb i j))
  | Int63le, [LInt i; LInt j] => Some (RBool (PrimInt63.leb i j))
  | Int63land, [LInt i; LInt j] => Some (RInt (PrimInt63.land i j))
  | Int63lor, [LInt i; LInt j] => Some (RInt (PrimInt63.lor i j))
  | Int63lsl, [LInt i; LInt j] => Some (RInt (PrimInt63.lsl i j))
  | Int63lsr, [LInt i; LInt j] => Some (RInt (PrimInt63.lsr i j))
  | Int63sub, [LInt i; LInt j] => Some (RInt (PrimInt63.sub i j))
  | Stringlength, [LString s] => Some (RInt (PrimString.length s))
  | Stringget, [LString s; LInt i] => Some (RInt (PrimString.get s i))
  | _, _ => None
  end.

(** The tactic that decides every clause of [prim_op_denote]: a slice-1
    operation takes at most two arguments, so three case splits on the argument
    list and one on each literal exhaust the match. *)
Local Ltac prim_op_cases op ls :=
  destruct op; destruct ls as [|l1 [|l2 [|l3 ls']]];
  try destruct l1; try destruct l2; cbn.

(** Arity and argument tags: [prim_op_denote] fires only on the literals
    [info op] announces. *)
Lemma prim_op_denote_args op ls r :
  prim_op_denote op ls = Some r -> map lit_tag ls = po_args (info op).
Proof.
  prim_op_cases op ls; intros H; try discriminate H; reflexivity.
Qed.

(** The result has the shape [info op] announces. *)
Lemma prim_op_denote_shape op ls r :
  prim_op_denote op ls = Some r -> result_has_shape r (po_shape (info op)).
Proof.
  prim_op_cases op ls; intros H; try discriminate H;
    injection H as <-; exact I.
Qed.

(** Satisfying instance of the reduction rule's premise
    [prim_op_denote op ls = Some r] (PCUIC [red_prim_op], Template [red_prim_op]):
    the premise holds for every argument list whose tags are the ones the
    operation expects.  No proof uses it. *)
Lemma prim_op_denote_total op ls :
  map lit_tag ls = po_args (info op) -> exists r, prim_op_denote op ls = Some r.
Proof.
  prim_op_cases op ls; intros H; try discriminate H; eexists; reflexivity.
Qed.
