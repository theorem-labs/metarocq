(* Case analysis on coinductive types.

   A [match] on a coinductive type is accepted whether or not its return type
   mentions the matched value. The quotation of a [match] marks, in the case
   information, whether the return type mentions the matched value. A cofixpoint
   unfolds under a [match] that does not mention it, which leaves the type of the
   [match] unchanged; under a [match] that mentions it the cofixpoint does not
   unfold, since unfolding would change the type of the [match] and break subject
   reduction (the Rocq reference manual, "Coinductive types", section "Caveat":
   dependent pattern matching on a positive coinductive type breaks subject
   reduction).

   The types are declared here, without template polymorphism, so that nothing but
   the case rule is exercised. *)

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

(** * Dependent return types *)

#[universes(template=no)]
CoInductive cc_nstream : Type := cc_ncons (a : nat) (rest : cc_nstream).

(* R1: a proof by [destruct] on a coinductive: its match returns
   [exists a r, s = cc_ncons a r], which mentions [s]. The quotation marks the
   match as dependent, and a cofixpoint does not unfold under it. *)
Lemma cc_ncases (s : cc_nstream) : exists a r, s = cc_ncons a r.
Proof. destruct s as [a r]. exists a, r. reflexivity. Qed.
MetaRocq SafeCheck cc_ncases.

(* R2: the term behind the counterexample to subject reduction. [cc_eq_force s] is
   a match whose return type, [s = cc_force s], mentions [s]. The quotation marks
   the match as dependent, so no cofixpoint unfolds under it, and its type stays
   the same. *)
Definition cc_force (s : cc_nstream) : cc_nstream :=
  match s with cc_ncons a r => cc_ncons a r end.
Definition cc_eq_force (s : cc_nstream) : s = cc_force s :=
  match s return s = cc_force s with cc_ncons a r => eq_refl end.
MetaRocq SafeCheck cc_eq_force.

(* A5: a cofixpoint under a match whose return type does not mention the matched
   value still unfolds: this equation holds by computation alone, so checking it
   needs the unfolding. *)
CoFixpoint cc_zeros : cc_nstream := cc_ncons 0 cc_zeros.
Definition cc_head (s : cc_nstream) : nat := match s with cc_ncons a _ => a end.
Definition cc_head_zeros : cc_head cc_zeros = 0 := eq_refl.
MetaRocq SafeCheck cc_head_zeros.

(** * Refused

   The refusal is pinned so that a reduction site that stops testing the flag, and
   so unfolds a cofixpoint under a dependent match again, is caught here: such a
   reduction would accept R3, which must fail. The expect comment is matched against
   the message by [check_fail_messages.sh], which the test-suite Makefile runs on
   this file. *)

(* R3: a conversion that needs a cofixpoint unfolded under a DEPENDENT match. The
   return type [dep_ty s] is a match on the matched value, so the quotation marks the
   match dependent and no cofixpoint unfolds under it. Rocq accepts [dep_head_zeros]:
   its conversion unfolds [cc_zeros] under the match. SafeCheck must refuse it, since
   unfolding there breaks subject reduction. *)
Definition dep_ty (s : cc_nstream) : Type := match s with cc_ncons _ _ => nat end.
Definition dep_head (s : cc_nstream) : dep_ty s :=
  match s return dep_ty s with cc_ncons a _ => a end.
Definition dep_head_zeros : @eq (dep_ty cc_zeros) (dep_head cc_zeros) 0 := eq_refl.
(* expect: Types are not convertible *)
Fail MetaRocq SafeCheck dep_head_zeros.
