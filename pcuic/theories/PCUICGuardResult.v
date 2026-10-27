(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.

Local Open Scope bs_scope.

(** * Results of the executable guard checker

  Shared by the fixpoint and cofixpoint checkers.  [OutOfFuel] is never
  turned into [Reject]: running out of fuel is not a refusal of the rule. *)

Inductive FixCoFix : Type := Fix | CoFix.

Inductive guard_result :=
| Accept
| Reject (msg : string)
| OutOfFuel.

(** [OutOfFuel] dominates, so that a refusal never hides an exhaustion. *)
Definition gr_and (r1 r2 : guard_result) : guard_result :=
  match r1, r2 with
  | OutOfFuel, _ => OutOfFuel
  | _, OutOfFuel => OutOfFuel
  | Reject m, _ => Reject m
  | Accept, r => r
  end.

Fixpoint gr_list {A} (f : A -> guard_result) (l : list A) : guard_result :=
  match l with
  | [] => Accept
  | a :: l => gr_and (f a) (gr_list f l)
  end.
