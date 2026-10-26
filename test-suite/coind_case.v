(* Case analysis on coinductive types.

   A [match] on a coinductive type is accepted when its return type does not
   mention the matched value: unfolding a cofixpoint under it then leaves the
   type of the [match] unchanged. A [match] whose return type mentions the
   matched value is refused, with "Dependent case on coinductive": unfolding a
   cofixpoint under it would change its type, which breaks subject reduction
   (the standard counterexample is the second one below).

   [Fail] accepts any error, so when adding a refused case, check the message it
   prints rather than relying on [Fail] alone. The types are declared here,
   without template polymorphism, so that nothing but the case rule is
   exercised. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

#[universes(template=no)]
Inductive cc_list (A : Type) : Type := cc_nil | cc_cons (a : A) (l : cc_list A).
Arguments cc_nil {A}.
Arguments cc_cons {A}.

(** * Accepted *)

(* A1: a non-dependent match on a coinductive with two constructors, under a
   fixpoint on [nat]: the shape of a function that takes the first [n] elements of
   a possibly finite stream. *)
#[universes(template=no)]
CoInductive cc_stream (A : Type) : Type :=
| cc_eof
| cc_more (a : A) (rest : cc_stream A).
Arguments cc_eof {A}.
Arguments cc_more {A}.

Fixpoint cc_take {A} (n : nat) (s : cc_stream A) : cc_list A :=
  match n with
  | 0 => cc_nil
  | S n => match s with
           | cc_eof => cc_nil
           | cc_more a s => cc_cons a (cc_take n s)
           end
  end.
MetaRocq SafeCheck @cc_take.

(* A2: an indexed coinductive, matched with a return type that mentions the
   indices but not the matched value. *)
#[universes(template=no)]
CoInductive cc_vstream : nat -> Type :=
| cc_vmore (n : nat) (rest : cc_vstream (S n)) : cc_vstream n.

Definition cc_vnext (n : nat) (s : cc_vstream n) : cc_vstream (S n) :=
  match s in cc_vstream k return cc_vstream (S k) with
  | cc_vmore _ rest => rest
  end.
MetaRocq SafeCheck @cc_vnext.

(* A3: an indexed coinductive whose indices contain a let, so that the
   predicate context of the match has a local definition. *)
#[universes(template=no)]
CoInductive cc_lstream : forall (n : nat) (m := S n) (k : nat), Type :=
| cc_lmore (n k : nat) (rest : cc_lstream n k) : cc_lstream n k.

Definition cc_lindex (n k : nat) (s : cc_lstream n k) : nat :=
  match s in cc_lstream n' k' return nat with
  | cc_lmore n' k' _ => n' + k'
  end.
MetaRocq SafeCheck @cc_lindex.

(* A4: a cofixpoint whose body matches on another stream non-dependently. *)
CoFixpoint cc_copy {A} (s : cc_stream A) : cc_stream A :=
  match s with
  | cc_eof => cc_eof
  | cc_more a rest => cc_more a (cc_copy rest)
  end.
MetaRocq SafeCheck @cc_copy.

(** * Refused *)

#[universes(template=no)]
CoInductive cc_nstream : Type := cc_ncons (a : nat) (rest : cc_nstream).

(* R1: a proof by [destruct] on a coinductive: its match returns
   [exists a r, s = cc_ncons a r], which mentions [s]. *)
Lemma cc_ncases (s : cc_nstream) : exists a r, s = cc_ncons a r.
Proof. destruct s as [a r]. exists a, r. reflexivity. Qed.
Fail MetaRocq SafeCheck cc_ncases.

(* R2: the counterexample to subject reduction. [cc_eq_force s] is a match whose
   return type, [s = cc_force s], mentions [s]. For [s] a cofixpoint, unfolding
   [s] under the match would give it a type that is not convertible to the old
   one. *)
Definition cc_force (s : cc_nstream) : cc_nstream :=
  match s with cc_ncons a r => cc_ncons a r end.
Definition cc_eq_force (s : cc_nstream) : s = cc_force s :=
  match s return s = cc_force s with cc_ncons a r => eq_refl end.
Fail MetaRocq SafeCheck cc_eq_force.
