(* F1 tests of the E (eta) checker at the SafeCheck level, on the FORECAST tree (EtaK7, 2026-10-29).

   Sources: the F1 pairs of lanes/eta/etak/kf-table.md section D, their Rocq text from plan section 0.3
   (P9), lanes/eta/k3_eta_witnesses.v and lanes/eta/etak/kf_unfold_first.v. Each test is a constant that
   Rocq's kernel accepts; [MetaRocq SafeCheck] runs the E checker on it (the FORECAST tree's extraction
   puts the E checker behind this command). Expected E verdicts are the table's:
   - accept: a plain [MetaRocq SafeCheck];
   - refuse: [Fail MetaRocq SafeCheck] (only where the kernel accepts and the E checker is expected to refuse:
     kf_unfold_first, the recorded completeness gap B1 — a PERMANENT test: if the eta step is ever moved
     ahead of head reduction, this line flips and fails visibly).
   The table's other "refuse" rows (bad, t5_inst, fg, fa_bad, fgz_bad, nested_bad, nested2_drop/swap,
   b1_ref, kf_lam_lam) are pairs the KERNEL refuses: no Rocq constant poses them, so SafeCheck cannot be
   run on them here; their refusal is tested at the kernel level (k3_eta_witnesses.v, kf_unfold_first.v). *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

(** * Accepted by the kernel; expected E verdict: accept *)

Definition e3 (f : nat -> nat) : (fun x => f x) = f := eq_refl.
MetaRocq SafeCheck e3.

Definition fa (A B : Type) (a : A) (f : A -> A -> B) : (fun x => f a x) = f a := eq_refl.
MetaRocq SafeCheck fa.

Definition fgz (A B : Type) (f : A -> B) (P : (A -> B) -> Prop) (h : P f)
  : P (fun x : A => f ((fun z : A => z) x)) := h.
MetaRocq SafeCheck fgz.

Definition nested (A B : Type) (g : (A -> A) -> (A -> A) -> B) (p q : A -> A)
  : g (fun x => p x) (fun y => q y) = g p q := eq_refl.
MetaRocq SafeCheck nested.

Definition nested2 (A B : Type) (h : A -> A -> B)
  : (fun x : A => (fun y : A => h x y)) = h := eq_refl.
MetaRocq SafeCheck nested2.

Definition dB (A B C : Type) (f : (A -> B) -> C)
  : (fun x : A -> B => f (fun y : A => x y)) = f := eq_refl.
MetaRocq SafeCheck dB.

Definition b1_acc (A D : Type) (g : (A -> A) -> A -> D)
  : (fun x : A => g (fun z : A => z) x) = g (fun z : A => z) := eq_refl.
MetaRocq SafeCheck b1_acc.

Definition nb1 (A B X D : Type) (g : (A -> B) -> X -> D) (k : A -> B)
  : g (fun w : A => k w) = (fun x : X => g k x) := eq_refl.
MetaRocq SafeCheck nb1.

Definition nb2a (A B : Type) (f : A -> A -> B) (a : A)
  : f a = (fun x : A => f a x) := eq_refl.
MetaRocq SafeCheck nb2a.

Definition nb2b (A B : Type) (h : A -> A -> A -> B) (a : A)
  : h a = (fun x y : A => h a x y) := eq_refl.
MetaRocq SafeCheck nb2b.

Set Universe Polymorphism.
Cumulative Inductive I@{*u} (A : Type@{u}) : Prop := ci.
Cumulative Inductive J@{*u} (P : Type@{u} -> Prop) : Prop := k.
Cumulative Inductive K@{*w} (F : Type@{w} -> Prop) : Prop := ck.

Definition b2b@{u v|} (x : K@{u} (fun A : Type@{u} => I@{u} A)) : K@{v} I@{v} := x.
MetaRocq SafeCheck b2b.

(* jmust and kf_var need [u < w]. [MetaRocq SafeCheck] of a universe-polymorphic constant with a strict
   constraint fails at the toplevel instantiation ("ctrs not satisfiable, while checking toplevel term"),
   after the declaration itself is checked: a property of the command, not of the checker (the plain
   control [poly_lt_ctrl] below, with no eta, fails the same way; out/t2.log). So they are stated over global
   universes with the constraint. *)
#[universes(polymorphic=no)] Universe uj wj.
#[universes(polymorphic=no)] Constraint uj < wj.
#[universes(polymorphic=no)] Definition jmust (Z : Type@{wj} -> Prop)
  (x : J@{uj} (fun A : Type@{uj} => Z A)) : J@{wj} Z := x.
MetaRocq SafeCheck jmust.

Cumulative Inductive I1@{*u} (A : Set) : Set := c1 : I1 A.
(* plan 0.3 writes [eq_refl (fun A => I1@{u} A)], which Rocq rejects ([eq_refl]'s arguments are implicit);
   the intended term is the explicit [@eq_refl]. *)
Definition d@{u v|} : @eq (Set -> Set) I1@{u} I1@{v} := @eq_refl (Set -> Set) (fun A => I1@{u} A).
MetaRocq SafeCheck d.

(* kf_var: the B1 control with a variable in place of the constant. *)
#[universes(polymorphic=no)] Definition kf_var (Z : Type@{wj} -> Prop) (x : J@{uj} (fun A : Type@{uj} => Z A)) : J@{wj} Z := x.
MetaRocq SafeCheck kf_var.

(** * Accepted by the kernel; expected E verdict: REFUSED (completeness gap B1, recorded) *)

(* A constant whose body is a lambda: the E checker unfolds it first (plan I7, S2) and then compares the
   two lambda domains Type@{u} / Type@{w} at Conv, which fails; the kernel tries eta first and accepts. *)
Definition Zc@{w} : Type@{w} -> Prop := fun A : Type@{w} => True.
#[universes(polymorphic=no)] Definition kf_unfold_first (x : J@{uj} (fun A : Type@{uj} => Zc@{wj} A)) : J@{wj} Zc@{wj} := x.
(* expect: Types are not convertible *)
Fail MetaRocq SafeCheck kf_unfold_first.
