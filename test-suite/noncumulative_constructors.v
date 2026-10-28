From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

Set Universe Polymorphism.

(* Q1 ignores its universe, so t1 only compares p1@{u} with p1@{v}. Rocq's kernel rejects t1; universe checking is off only to add it. *)
NonCumulative Inductive P1@{u} (A : Set) : Set := p1 : P1 A.
Cumulative Inductive Q1@{*w} (x : P1@{w} unit) : Prop := q1 : Q1 x.
(* Control: the same term at a single instance is accepted, so the Fail below is about p1's instances. *)
Definition t1_refl@{u|} : @eq Prop (Q1@{u} (p1@{u} unit)) (Q1@{u} (p1@{u} unit)) := eq_refl.
MetaRocq SafeCheck t1_refl.
Unset Universe Checking.
Definition t1@{u v|} : @eq Prop (Q1@{u} (p1@{u} unit)) (Q1@{v} (p1@{v} unit)).
Proof. exact_no_check (@eq_refl Prop (Q1@{u} (p1@{u} unit))). Defined.
Set Universe Checking.
Fail MetaRocq SafeCheck t1.

(* Control: constructors of a cumulative inductive, even an invariant one, are accepted. *)
Cumulative Inductive P2@{=u} (A : Set) : Set := p2 : P2 A.
Cumulative Inductive Q2@{*w} (x : P2@{w} unit) : Prop := q2 : Q2 x.
Definition t2@{u v|} : @eq Prop (Q2@{u} (p2@{u} unit)) (Q2@{v} (p2@{v} unit)).
Proof. exact_no_check (@eq_refl Prop (Q2@{u} (p2@{u} unit))). Defined.
MetaRocq SafeCheck t2.
