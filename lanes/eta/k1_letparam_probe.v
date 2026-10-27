(* C3Falsifier K1/F-8 probe v6: the LIVE-binder case (b), expressed with plain
   domain/codomain universes to dodge the w+1 algebra limitation. *)
Set Printing Universes.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Cumulative Inductive BoxWb@{u w} (A : Type@{u}) (C := Type@{w} : Type@{w+1})
  (E : C) : Type@{max(u,w+1)} := boxwb (a : A).

(* b1: with w1=w2 declared, the two 1-under-applied heads share a type -> accept *)
Definition b_eqw@{u w1 w2 Wd W | u <= W, w1 <= Wd, w2 <= Wd, w1 < W, w2 < W, w1 = w2}
  (A : Type@{u}) :
  @eq (Type@{Wd} -> Type@{W}) (BoxWb@{u w1} A) (BoxWb@{u w2} A) := eq_refl.

(* b2: WITHOUT w1=w2, elaborator. Expect a universe-constraint error forcing w1=w2
   (because the shared eq type Type@{Wd}->Type@{W} needs domain Type@{w1}=Type@{Wd}=Type@{w2};
   Pi domain is invariant under conversion). That error = the two heads differ in type. *)
Definition b_diffw@{u w1 w2 Wd W | u <= W, w1 <= Wd, w2 <= Wd, w1 < W, w2 < W}
  (A : Type@{u}) :
  @eq (Type@{Wd} -> Type@{W}) (BoxWb@{u w1} A) (BoxWb@{u w2} A) := eq_refl.

(* b3: WITHOUT w1=w2, straight to the kernel via exact_no_check. If the kernel also
   needs the type to be well-formed (both heads at Type@{Wd}->Type@{W}), it cannot
   accept with w1<>w2 either -> no unsound accept is expressible. *)
Definition b_diffw_k@{u w1 w2 Wd W | u <= W, w1 <= Wd, w2 <= Wd, w1 < W, w2 < W}
  (A : Type@{u}) :
  @eq (Type@{Wd} -> Type@{W}) (BoxWb@{u w1} A) (BoxWb@{u w2} A)
  := ltac:(exact_no_check (@eq_refl (Type@{Wd} -> Type@{W}) (BoxWb@{u w1} A))).
