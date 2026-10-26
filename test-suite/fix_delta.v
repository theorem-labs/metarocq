(* Fixpoints and cofixpoints whose (co)inductive type is reached by reduction.

   Rocq's kernel finds the inductive type of a fixpoint's recursive argument
   after weak-head reduction ([Inductive.inductive_of_mutfix] calls
   [find_inductive], which calls [whd_all]); for a cofixpoint it reduces the
   codomain ([codomain_is_coind]).  PCUIC must accept the same fixpoints, and
   must still reject a recursive argument whose type does not reduce to an
   inductive type, and mutual fixpoints over different inductive blocks.

   The first part must be accepted.  The second part must stay rejected; each
   [Fail] there must fail with the message that [run-fix-delta-tests.sh]
   expects, not with some other error. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From Stdlib Require Import micromega.Tauto.

(** * Accepted *)

(* A1: the r188 obstacle.  [cnf_checker] recurses on [cnf Term' Annot], and
   [cnf] is a definition: [fun Term' Annot => list (clause Term' Annot)]. *)
MetaRocq SafeCheck @Tauto.cnf_checker.

(* A2: the minimal control: an alias with no parameters. *)
Definition fd_natlist := list nat.
Fixpoint fd_len (l : fd_natlist) : nat :=
  match l with nil => 0 | cons _ t => S (fd_len t) end.
MetaRocq SafeCheck @fd_len.

(* A3: a parametric alias (delta, then beta). *)
Definition fd_alist (A : Type) := list A.
Fixpoint fd_alen {A} (l : fd_alist A) : nat :=
  match l with nil => 0 | cons _ t => S (fd_alen t) end.
MetaRocq SafeCheck @fd_alen.

(* A4: an alias of an alias. *)
Definition fd_natlist2 := fd_natlist.
Fixpoint fd_len2 (l : fd_natlist2) : nat :=
  match l with nil => 0 | cons _ t => S (fd_len2 t) end.
MetaRocq SafeCheck @fd_len2.

(* A5: the type is a local let-bound variable of the context. *)
Definition fd_letlen :=
  let T := list nat in
  fix f (l : T) : nat := match l with nil => 0 | cons _ t => S (f t) end.
MetaRocq SafeCheck @fd_letlen.

(* A6: the type reduces by iota. *)
Definition fd_sel (b : bool) : Type := if b then list nat else nat.
Fixpoint fd_sellen (l : fd_sel true) : nat :=
  match l with nil => 0 | cons _ t => S (fd_sellen t) end.
MetaRocq SafeCheck @fd_sellen.

(* A7: the recursive argument is not the first one, and the type depends on
   an earlier argument. *)
Fixpoint fd_alen2 (A : Type) (n : nat) (l : fd_alist A) : nat :=
  match l with nil => n | cons _ t => S (fd_alen2 A n t) end.
MetaRocq SafeCheck @fd_alen2.

(* A8: mutual fixpoints over one mutual block, through two aliases. *)
Inductive fd_even : Set := fd_ez : fd_even | fd_es : fd_odd -> fd_even
with fd_odd : Set := fd_os : fd_even -> fd_odd.
Definition fd_even' := fd_even.
Definition fd_odd' := fd_odd.
Fixpoint fd_esize (e : fd_even') : nat :=
  match e with fd_ez => 0 | fd_es o => S (fd_osize o) end
with fd_osize (o : fd_odd') : nat :=
  match o with fd_os e => S (fd_esize e) end.
MetaRocq SafeCheck @fd_esize.

(* A9: a cofixpoint whose codomain is an alias of a coinductive type. *)
CoInductive fd_str : Set := fd_cons : nat -> fd_str -> fd_str.
Definition fd_str' := fd_str.
CoFixpoint fd_ones : fd_str' := fd_cons 1 fd_ones.
MetaRocq SafeCheck @fd_ones.

(* A10: a cofixpoint whose codomain is a parametric alias, under a product. *)
CoInductive fd_pstr (A : Type) : Type := fd_pcons : A -> fd_pstr A -> fd_pstr A.
Arguments fd_pcons {A}.
Definition fd_pstr' (A : Type) := fd_pstr A.
CoFixpoint fd_rep {A} (a : A) : fd_pstr' A := fd_pcons a (fd_rep a).
MetaRocq SafeCheck @fd_rep.

(** * Rejected *)

(* With guard checking off, the elaborator does not look for the inductive
   type of a [fix], and the kernel does not see a term given to SafeCheck, so
   these terms reach MetaRocq unchecked.  The kernel would reject R1-R7.
   (SafeCheck quotes the bodies of opaque constants, and PCUIC has no opaque
   constants, so an opaque alias is not a control here.) *)
Unset Guard Checking.

(* R1: the recursive argument is a sort. *)
Fail MetaRocq SafeCheck (fix f (A : Type) {struct A} : nat := 0).

(* R2: an alias of a function type. *)
Definition fd_fun := nat -> nat.
Fail MetaRocq SafeCheck (fix f (g : fd_fun) {struct g} : nat := 0).

(* R3: an axiom. *)
Axiom fd_ax : Type.
Fail MetaRocq SafeCheck (fix f (x : fd_ax) {struct x} : nat := 0).

(* R4: mutual fixpoints over two different inductive blocks. *)
Fail MetaRocq SafeCheck
  (fix f (n : nat) {struct n} : nat := 0 with g (b : bool) {struct b} : nat := 0 for f).

(* R5: the same through aliases: both reduce, to different blocks. *)
Definition fd_nat' := nat.
Definition fd_bool' := bool.
Fail MetaRocq SafeCheck
  (fix f (n : fd_nat') {struct n} : nat := 0 with g (b : fd_bool') {struct b} : nat := 0 for f).

(* R6: a fixpoint on a coinductive type, directly and through an alias. *)
Fail MetaRocq SafeCheck (fix f (s : fd_str) {struct s} : nat := 0).
Fail MetaRocq SafeCheck (fix f (s : fd_str') {struct s} : nat := 0).

(* R7: a fixpoint whose recursive argument is a let-bound variable whose value
   is not an inductive type. *)
Fail MetaRocq SafeCheck (let T := nat -> nat in fix f (g : T) {struct g} : nat := 0).

(* R8-R10: cofixpoints that do not produce a coinductive type.  With guard
   checking off the kernel does not check the codomain, so these enter the
   environment. *)
CoFixpoint fd_cbad_nat : nat := fd_cbad_nat.
Fail MetaRocq SafeCheck @fd_cbad_nat.
CoFixpoint fd_cbad_alias : fd_nat' := fd_cbad_alias.
Fail MetaRocq SafeCheck @fd_cbad_alias.
CoFixpoint fd_cbad_sort : Type := fd_cbad_sort.
Fail MetaRocq SafeCheck @fd_cbad_sort.

Set Guard Checking.

(** * Still rejected, although the kernel accepts it *)

(* K1: the products of the fixpoint's type are hidden behind a definition.
   The kernel reduces the body to find its lambdas; PCUIC reads the recursive
   argument from the syntactic products of the type, which [EtaExpand] relies
   on.  This change does not cover it. *)
Definition fd_natfun := nat -> nat.
Definition fd_hidden : fd_natfun.
Proof. fix f 1. intros n. destruct n as [|n]. exact 0. exact (S (f n)). Defined.
Fail MetaRocq SafeCheck @fd_hidden.
