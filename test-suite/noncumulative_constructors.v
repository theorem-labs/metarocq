From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

Set Universe Polymorphism.

(* Fully applied constructors of a non-cumulative inductive are compared by instance equality. *)
NonCumulative Inductive P1@{u} (A : Set) : Set := p1 : P1 A.
Cumulative Inductive Q1@{*w} (x : P1@{w} unit) : Prop := q1 : Q1 x.
Unset Universe Checking.
Definition t1@{u v|} : @eq Prop (Q1@{u} (p1@{u} unit)) (Q1@{v} (p1@{v} unit)).
Proof. exact_no_check (@eq_refl Prop (Q1@{u} (p1@{u} unit))). Defined.
Set Universe Checking.
Fail MetaRocq SafeCheck t1.

Cumulative Inductive P2@{=u} (A : Set) : Set := p2 : P2 A.
Cumulative Inductive Q2@{*w} (x : P2@{w} unit) : Prop := q2 : Q2 x.
Definition t2@{u v|} : @eq Prop (Q2@{u} (p2@{u} unit)) (Q2@{v} (p2@{v} unit)).
Proof. exact_no_check (@eq_refl Prop (Q2@{u} (p2@{u} unit))). Defined.
MetaRocq SafeCheck t2.
