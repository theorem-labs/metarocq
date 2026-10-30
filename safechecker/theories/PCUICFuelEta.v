(* Distributed under the terms of the MIT license. *)
(** * Fuel for the η checker's recursions (BET-64 ETAK, option B FUEL)

  The η checker has three recursions that used to terminate by the strong-normalisation premise
  [normalization_in] (an [Acc] proof built from [NormalizationInE]): the reduction machine
  ([PCUICSafeReduceEta.reduce_stack_fuel]), the conversion ([PCUICSafeConversionEta.isconv_full]) and
  the cofixpoint codomain walk ([PCUICTypeCheckerEta.check_codomain_ind]). Each now recurses
  structurally on a [fuel] and gives a distinct out-of-fuel outcome when the fuel is spent, so no
  normalisation premise is needed.

  [fuel] is the shape of the call-by-need machine's [PCUICCallByNeedEta.cbn_fuel]: [FuelS k] produces
  the next unit on demand, so a large bound costs no memory. [fuel_of_N n] is [n] units, built in
  O(log n) closures. Every recursion entry starts from [checker_fuel] = 2^62 units, far above what a
  graded run can consume before the wall clock or the memory cap ends it. *)
From Stdlib Require Import BinNums BinPos BinNat.

Inductive fuel := FuelO | FuelS (k : unit -> fuel).

(** [fuel_of_pos p k] is [p] units followed by [k tt]. *)
Fixpoint fuel_of_pos (p : positive) (k : unit -> fuel) : fuel :=
  match p with
  | xH => FuelS k
  | xO p => fuel_of_pos p (fun _ => fuel_of_pos p k)
  | xI p => FuelS (fun _ => fuel_of_pos p (fun _ => fuel_of_pos p k))
  end.

Definition fuel_of_N (n : N) : fuel :=
  match n with
  | N0 => FuelO
  | Npos p => fuel_of_pos p (fun _ => FuelO)
  end.

(** The fuel of one recursion entry: 2^62 units. *)
Definition checker_fuel : N := 4611686018427387904%N.

Definition default_fuel : fuel := fuel_of_N checker_fuel.

(** [simpl]/[cbn] never unfold the default fuel: under the binder of [FuelS] a reduction strategy
    that normalises would unfold all 2^62 units. *)
#[global] Arguments default_fuel : simpl never.

(** The number of units of a fuel, for the unit lemmas below. *)
Fixpoint fuel_units (bound : nat) (f : fuel) : nat :=
  match bound with
  | O => O
  | S bound =>
    match f with
    | FuelO => O
    | FuelS k => S (fuel_units bound (k tt))
    end
  end.

Lemma fuel_of_N_1024 : fuel_units 2000 (fuel_of_N 1024%N) = 1024.
Proof. vm_compute. reflexivity. Qed.

Lemma fuel_of_N_1000 : fuel_units 2000 (fuel_of_N 1000%N) = 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma fuel_of_N_1 : fuel_units 10 (fuel_of_N 1%N) = 1.
Proof. vm_compute. reflexivity. Qed.

(** The default fuel is not empty: every recursion entry can take at least one step. Stated with a
    [match], so checking it evaluates [default_fuel] to weak-head normal form only (62 unfoldings); a
    comparison of two [FuelS] closures could unfold all 2^62 units. *)
Lemma default_fuel_step : match default_fuel with FuelS _ => True | FuelO => False end.
Proof. exact I. Qed.
