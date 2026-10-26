(* Fixpoints and cofixpoints whose (co)inductive type is reached by reduction.

   Rocq's kernel finds the inductive type of a fixpoint's recursive argument
   after weak-head reduction ([Inductive.inductive_of_mutfix] calls
   [find_inductive], which calls [whd_all]); for a cofixpoint it reduces the
   codomain ([codomain_is_coind]).  PCUIC must accept the same fixpoints, and
   must still reject a recursive argument whose type does not reduce to an
   inductive type, and mutual fixpoints over different inductive blocks.

   The first part must be accepted.  The second part must stay rejected; each
   [Fail] there must fail with the "Ill-formed (co)fixpoint" message, not with
   some other error.  The inductive types are declared here, without template
   polymorphism, so that nothing but the (co)fixpoint rule is exercised. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From Ltac2 Require Ltac2.

#[universes(template=no)]
Inductive fd_nlist : Set := fd_nnil | fd_ncons (n : nat) (l : fd_nlist).
#[universes(template=no)]
Inductive fd_plist (A : Type) : Type := fd_pnil | fd_pcons (a : A) (l : fd_plist A).
Arguments fd_pnil {A}.
Arguments fd_pcons {A}.

(** * Accepted *)

(* A1: an alias with no parameters (the minimal control). *)
Definition fd_alias := fd_nlist.
Fixpoint fd_len (l : fd_alias) : nat :=
  match l with fd_nnil => 0 | fd_ncons _ t => S (fd_len t) end.
MetaRocq SafeCheck @fd_len.

(* A2: a parametric alias (delta, then beta), the shape of
   [Stdlib.micromega.Tauto.cnf], which is [fun Term' Annot => list (clause Term' Annot)]. *)
Definition fd_palias (A : Type) := fd_plist A.
Fixpoint fd_plen {A} (l : fd_palias A) : nat :=
  match l with fd_pnil => 0 | fd_pcons _ t => S (fd_plen t) end.
MetaRocq SafeCheck @fd_plen.

(* A3: an alias of an alias. *)
Definition fd_alias2 := fd_alias.
Fixpoint fd_len2 (l : fd_alias2) : nat :=
  match l with fd_nnil => 0 | fd_ncons _ t => S (fd_len2 t) end.
MetaRocq SafeCheck @fd_len2.

(* A4: the type is a let-bound variable of the local context. *)
Definition fd_letlen :=
  let T := fd_nlist in
  fix f (l : T) : nat := match l with fd_nnil => 0 | fd_ncons _ t => S (f t) end.
MetaRocq SafeCheck @fd_letlen.

(* A5: the type reduces by iota. *)
Definition fd_sel (b : bool) : Set := if b then fd_nlist else nat.
Fixpoint fd_sellen (l : fd_sel true) : nat :=
  match l with fd_nnil => 0 | fd_ncons _ t => S (fd_sellen t) end.
MetaRocq SafeCheck @fd_sellen.

(* A6: the recursive argument is not the first one, and its type depends on
   an earlier argument. *)
Fixpoint fd_plen2 (A : Type) (n : nat) (l : fd_palias A) : nat :=
  match l with fd_pnil => n | fd_pcons _ t => S (fd_plen2 A n t) end.
MetaRocq SafeCheck @fd_plen2.

(* A7: mutual fixpoints over one mutual block, through two aliases. *)
Inductive fd_even : Set := fd_ez : fd_even | fd_es : fd_odd -> fd_even
with fd_odd : Set := fd_os : fd_even -> fd_odd.
Definition fd_even' := fd_even.
Definition fd_odd' := fd_odd.
Fixpoint fd_esize (e : fd_even') : nat :=
  match e with fd_ez => 0 | fd_es o => S (fd_osize o) end
with fd_osize (o : fd_odd') : nat :=
  match o with fd_os e => S (fd_esize e) end.
MetaRocq SafeCheck @fd_esize.

(* A8: a cofixpoint whose codomain is an alias of a coinductive type. *)
CoInductive fd_str : Set := fd_scons : nat -> fd_str -> fd_str.
Definition fd_str' := fd_str.
CoFixpoint fd_ones : fd_str' := fd_scons 1 fd_ones.
MetaRocq SafeCheck @fd_ones.

(* A9: a cofixpoint whose codomain is a parametric alias, under a product. *)
#[universes(template=no)]
CoInductive fd_pstr (A : Type) : Type := fd_pscons : A -> fd_pstr A -> fd_pstr A.
Arguments fd_pscons {A}.
Definition fd_pstr' (A : Type) := fd_pstr A.
CoFixpoint fd_rep {A} (a : A) : fd_pstr' A := fd_pscons a (fd_rep a).
MetaRocq SafeCheck @fd_rep.

(** * Rejected *)

(* Rocq's elaborator and [Typing] reject a [fix] whose recursive argument is
   not of an inductive type, even with guard checking off
   ([Inductive.inductive_of_mutfix] runs unconditionally), so R1-R3, R6 and R7
   build the term with Ltac2's unsafe constructors and give it to SafeCheck
   with [exact_no_check], under a type ascription.  The kernel never sees a
   term given to SafeCheck; MetaRocq checks the term itself. *)
Module FdUnsafe.
Import Ltac2.Ltac2.
Ltac2 bnd (n : ident) (t : constr) := Constr.Binder.unsafe_make (Some n) Constr.Binder.Relevant t.
(* [fix f (x : ty) {struct x} : nat := 0], for a closed [ty]. *)
Ltac2 fix1 (ty : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Fix [| 0 |] 0
    [| bnd @f (Constr.Unsafe.make (Constr.Unsafe.Prod (bnd @x ty) 'nat)) |]
    [| Constr.Unsafe.make (Constr.Unsafe.Lambda (bnd @x ty) '0) |]).
(* [let T := nat -> nat in fix f (x : T) {struct x} : nat := 0]. *)
Ltac2 letfix () : constr :=
  let rel n := Constr.Unsafe.make (Constr.Unsafe.Rel n) in
  Constr.Unsafe.make (Constr.Unsafe.LetIn (bnd @T 'Set) '(nat -> nat)
    (Constr.Unsafe.make (Constr.Unsafe.Fix [| 0 |] 0
      [| bnd @f (Constr.Unsafe.make (Constr.Unsafe.Prod (bnd @x (rel 1)) 'nat)) |]
      [| Constr.Unsafe.make (Constr.Unsafe.Lambda (bnd @x (rel 2)) '0) |]))).
(* [fix f : ty := fun x : nat => 0], whose declared type [ty] is a constant
   that unfolds to a product: the products are hidden. *)
Ltac2 fixhidden (ty : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Fix [| 0 |] 0 [| bnd @f ty |]
    [| Constr.Unsafe.make (Constr.Unsafe.Lambda (bnd @x 'nat) '0) |]).
Ltac2 unchecked (c : constr) := ltac1:(t |- exact_no_check t) (Ltac1.of_constr c).
End FdUnsafe.
Import FdUnsafe.

Definition fd_fun := nat -> nat.
Axiom fd_ax : Type.

(* With guard checking off, the kernel does not check a cofixpoint's codomain
   (R8-R10), and nothing here relies on a guard check. *)
Unset Guard Checking.

(* R1: the recursive argument is a sort. *)
Fail MetaRocq SafeCheck (ltac2:(unchecked (fix1 'Type)) : Type -> nat).

(* R2: an alias of a function type. *)
Fail MetaRocq SafeCheck (ltac2:(unchecked (fix1 'fd_fun)) : fd_fun -> nat).

(* R3: an axiom. *)
Fail MetaRocq SafeCheck (ltac2:(unchecked (fix1 'fd_ax)) : fd_ax -> nat).

(* R4: mutual fixpoints over two different inductive blocks. *)
Fail MetaRocq SafeCheck
  (fix f (n : nat) {struct n} : nat := 0 with g (b : bool) {struct b} : nat := 0 for f).

(* R5: the same through aliases: both reduce, to different blocks. *)
Definition fd_nat' := nat.
Definition fd_bool' := bool.
Fail MetaRocq SafeCheck
  (fix f (n : fd_nat') {struct n} : nat := 0 with g (b : fd_bool') {struct b} : nat := 0 for f).

(* R6: a fixpoint on a coinductive type, directly and through an alias. *)
Fail MetaRocq SafeCheck (ltac2:(unchecked (fix1 'fd_str)) : fd_str -> nat).
Fail MetaRocq SafeCheck (ltac2:(unchecked (fix1 'fd_str')) : fd_str' -> nat).

(* R7: the recursive argument's type is a let-bound variable whose value is
   not an inductive type. *)
Fail MetaRocq SafeCheck (ltac2:(unchecked (letfix ())) : (nat -> nat) -> nat).

(* R8-R10: cofixpoints that do not produce a coinductive type.  These enter
   the environment, because guard checking is off. *)
CoFixpoint fd_cbad_nat : nat := fd_cbad_nat.
Fail MetaRocq SafeCheck @fd_cbad_nat.
CoFixpoint fd_cbad_alias : fd_nat' := fd_cbad_alias.
Fail MetaRocq SafeCheck @fd_cbad_alias.
CoFixpoint fd_cbad_sort : Type := fd_cbad_sort.
Fail MetaRocq SafeCheck @fd_cbad_sort.
(* R11: a fixpoint whose declared type hides its products behind a definition.
   The kernel finds the lambdas by reducing the body and accepts this; PCUIC
   reads the recursive argument from the syntactic products of the declared
   type, which [EtaExpand.wf_fixpoint_rarg] relies on, so it must stay
   rejected.  Rocq's own syntax never builds such a fixpoint: [Fixpoint] and
   [fix] spell the products out, and the [fix] tactic on a goal [fd_natfun]
   fails with "Not enough products". *)
Definition fd_natfun := nat -> nat.
Fail MetaRocq SafeCheck (ltac2:(unchecked (fixhidden 'fd_natfun)) : fd_natfun).

Set Guard Checking.
