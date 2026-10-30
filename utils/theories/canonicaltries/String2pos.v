(** Convert strings to positive numbers.
    The encoding used is the trivial one (8 bits per character). *)

From Stdlib Require Import String Ascii ZArith Extraction.
From Equations Require Import Equations.

Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Derive NoConfusion EqDec for positive.

Definition bool_cons_pos (b: bool) (n: positive) : positive :=
  if b then xI n else xO n.

Definition ascii_cons_pos (c: ascii) (n: positive) : positive :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      bool_cons_pos b0 (
      bool_cons_pos b1 (
      bool_cons_pos b2 (
      bool_cons_pos b3 (
      bool_cons_pos b4 (
      bool_cons_pos b5 (
      bool_cons_pos b6 (
      bool_cons_pos b7 n)))))))
  end.

(* This REPLACES A COMPUTATION: the OCaml must return
   [bool_cons_pos b0 (... (bool_cons_pos b7 n))] for [c = Ascii b0 ... b7], with b_i bit i
   of [Char.code c] and b0 the least significant.  [Print Assumptions] cannot show it.
   This module is in [safechecker-plugin/src/metarocq_safechecker_plugin.mlpack], so the
   directive is kept out of the shipped checker only by REACHABILITY: [ascii_cons_pos] is
   not reached from the roots of the safechecker's [Separate Extraction], and in the built
   1a92b56c tree [safechecker-plugin/src/string2pos.ml] holds the [positive] datatype and
   nothing else.  A new extraction root can change that without touching this line.  See
   test-suite/extraction_directives.allowed. *)
Extract Constant ascii_cons_pos =>
  "(fun c n ->
      let c = Char.code c in
      let n1 = if c land 1 = 0 then Coq_xO n else Coq_xI n in
      let n2 = if c land 2 = 0 then Coq_xO n1 else Coq_xI n1 in
      let n3 = if c land 4 = 0 then Coq_xO n2 else Coq_xI n2 in
      let n4 = if c land 8 = 0 then Coq_xO n3 else Coq_xI n3 in
      let n5 = if c land 16 = 0 then Coq_xO n4 else Coq_xI n4 in
      let n6 = if c land 32 = 0 then Coq_xO n5 else Coq_xI n5 in
      let n7 = if c land 64 = 0 then Coq_xO n6 else Coq_xI n6 in
      if c land 128 = 0 then Coq_xO n7 else Coq_xI n7)".

Fixpoint pos_of_string (s: string) : positive :=
  match s with
  | EmptyString => xH
  | String c s => ascii_cons_pos c (pos_of_string s)
  end.