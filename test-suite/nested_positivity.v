(* Nested inductive types: positivity in the safe checker.

   Accepted cases: Rocq's kernel accepts each of them, and so must the checker.
   Rejected cases: each is defined with Rocq's positivity check bypassed, and the
   checker must still reject it; a [Fail Inductive] beside each one shows that Rocq's
   kernel rejects the same definition. Nestings that need reduction to be seen, such
   as a nesting reached through a constant, are tested in [positivity_red.v].

   Every type nested here is defined in this file, monomorphic, so the file does not
   depend on how SafeCheck handles template-polymorphic types such as [list] and
   [prod]; [nested_positivity_check.v] runs the positivity check alone on both kinds. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

Inductive mlist (A : Set) : Set := mnil : mlist A | mcons : A -> mlist A -> mlist A.
Inductive mpair (A B : Set) : Set := mp : A -> B -> mpair A B.
Inductive moption (A : Set) : Set := mNone : moption A | mSome : A -> moption A.

(** * Accepted *)

(* The rose tree: the shape of [Stdlib.micromega.ZMicromega.ZArithProof]'s
   [EnumProof] constructor. *)
Inductive mrose : Set := MNode : mlist mrose -> mrose.
MetaRocq SafeCheck mrose.

(* Nested through an option type, beside a non-recursive argument. *)
Inductive opt_tree : Set := OptNode : moption opt_tree -> nat -> opt_tree.
MetaRocq SafeCheck opt_tree.

(* Nesting inside nesting: [mpair] inside [mlist]. *)
Inductive rose_pair : Set := NodeP : mlist (mpair nat rose_pair) -> rose_pair.
MetaRocq SafeCheck rose_pair.

(* The nested occurrence mentions a parameter of the block being defined. *)
Inductive mprose (A : Set) : Set := MPNode : A -> mlist (mprose A) -> mprose A.
MetaRocq SafeCheck mprose.

(* The outer type has a non-uniform parameter [n]; the block occurs only in its
   uniform parameter [A]. Recursive occurrences of [NU] change [n], which stays
   free of the block. *)
Inductive NU (A : Type) (n : nat) :=
| nu0 : NU A n
| nu1 : A -> NU A (S n) -> NU A n.
Inductive use_nu := UseNU : NU use_nu 0 -> use_nu.
MetaRocq SafeCheck use_nu.

(* The outer type is an indexed family. *)
Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Inductive vtree := VNode : forall n, vec vtree n -> vtree.
MetaRocq SafeCheck vtree.

(* A mutual block with a nested occurrence of its other member. *)
Inductive mt1 : Set := M1 : mlist mt2 -> mt1
with mt2 : Set := M2 : mt1 -> mt2.
MetaRocq SafeCheck mt1.

(* The outer type is itself nested ([mW] occurs inside [mpair] in its own
   constructor), so the check of [use_mw] nests twice and must recognise [mW]'s
   own recursive occurrence two levels down. *)
Inductive mW (A : Set) : Set := mw : mpair nat (mW A) -> mW A | mleaf : A -> mW A.
Inductive use_mw : Set := UseMW : mW use_mw -> use_mw.
MetaRocq SafeCheck use_mw.

(* The outer type has a let-in parameter, and a recursive occurrence after it.
   [to_extended_list] skips the let, and so does the kernel's [compute_rec_par], so
   the two must agree on which parameters the first [k] are. *)
Inductive mlet (A : Set) (B := mpair A A) : Set :=
| mlc : B -> mlet A -> mlet A
| mln : mlet A.
Inductive use_mlet : Set := UseMLet : mlet use_mlet -> use_mlet.
MetaRocq SafeCheck use_mlet.

(* The outer type has more parameters than the block needs: [k] is 1, the kernel's
   uniform count is 2, and [mpair2] has 3 parameters, the third of which the
   recursive occurrence changes. *)
Inductive mpair2 (A B : Set) (C : Set) : Set :=
| mp2 : A -> B -> mpair2 A B C
| mp2' : mpair2 A B (C -> C) -> mpair2 A B C.
Inductive use_mpair2 : Set := UseMP2 : mpair2 use_mpair2 nat bool -> use_mpair2.
MetaRocq SafeCheck use_mpair2.

(** * Rejected *)

(* Each refused case is preceded by an [expect:] comment. The message of the
   [Fail MetaRocq SafeCheck] that follows must contain that text, since [Fail]
   alone passes on any error. [check_fail_messages.sh], which the test-suite
   Makefile runs on this file, checks this. *)

(* Not nested: the existing negative case. *)
Fail Inductive bad_plain := BadPlain : (bad_plain -> nat) -> bad_plain.
#[bypass_check(positivity)]
Inductive bad_plain := BadPlain : (bad_plain -> nat) -> bad_plain.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_plain.

(* Nested, with the block to the left of an arrow inside the nesting type's
   argument: [mcons]'s first argument becomes [bad_nested -> nat]. *)
Fail Inductive bad_nested : Set := BadNested : mlist (bad_nested -> nat) -> bad_nested.
#[bypass_check(positivity)]
Inductive bad_nested : Set := BadNested : mlist (bad_nested -> nat) -> bad_nested.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_nested.

(* The same, two nestings deep. *)
Fail Inductive bad_nested2 : Set := BadNested2 : mlist (mpair nat (bad_nested2 -> False)) -> bad_nested2.
#[bypass_check(positivity)]
Inductive bad_nested2 : Set := BadNested2 : mlist (mpair nat (bad_nested2 -> False)) -> bad_nested2.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_nested2.

(* The block in a parameter that is not uniform in the outer type: [TD]'s
   recursive occurrence changes [A] to [A -> False], so [T bad_nonunif] contains
   [bad_nonunif -> False] in its constructors. *)
Inductive T (A : Type) := TC : A -> T A | TD : T (A -> False) -> T A.
Fail Inductive bad_nonunif := BadNonUnif : T bad_nonunif -> bad_nonunif.
#[bypass_check(positivity)]
Inductive bad_nonunif := BadNonUnif : T bad_nonunif -> bad_nonunif.
(* expect: Nested positivity: the block occurs in an argument that is not a uniform parameter *)
Fail MetaRocq SafeCheck bad_nonunif.

(* The block in an index of the outer type. *)
Inductive mI : Set -> Set := mic : mI nat.
Fail Inductive bad_index : Set := BadIndex : mI bad_index -> bad_index.
#[bypass_check(positivity)]
Inductive bad_index : Set := BadIndex : mI bad_index -> bad_index.
(* expect: Nested positivity: the block occurs in an argument that is not a uniform parameter *)
Fail MetaRocq SafeCheck bad_index.

(* The kernel's uniformity condition ([compute_rec_par] and [check_positivity_nested]
   in kernel/indtypes.ml): the block may
   occur only in the parameters that every recursive occurrence of the outer type
   repeats as its own parameter variables. [T2]'s recursive occurrence swaps them,
   so it has no uniform parameter, and [T2 r r] is refused even though, once
   instantiated, [T2 r r -> T2 r r] repeats the instance. *)
Inductive T2 (A B : Set) : Set := c2 : T2 B A -> T2 A B.
Fail Inductive bad_swap : Set := BadSwap : T2 bad_swap bad_swap -> bad_swap.
#[bypass_check(positivity)]
Inductive bad_swap : Set := BadSwap : T2 bad_swap bad_swap -> bad_swap.
(* expect: Nested positivity: the block occurs in an argument that is not a uniform parameter *)
Fail MetaRocq SafeCheck bad_swap.

(* [T1]'s recursive occurrence fixes its parameter to [nat], so it has no uniform
   parameter. Instantiated, [T1 nat -> T1 r] has a block-free argument; only the
   uniformity condition refuses it. *)
Inductive T1 (A : Set) : Set := c1 : T1 nat -> T1 A.
Fail Inductive bad_fixed : Set := BadFixed : T1 bad_fixed -> bad_fixed.
#[bypass_check(positivity)]
Inductive bad_fixed : Set := BadFixed : T1 bad_fixed -> bad_fixed.
(* expect: Nested positivity: the block occurs in an argument that is not a uniform parameter *)
Fail MetaRocq SafeCheck bad_fixed.

(* The block occurs under a parameter of the block, a variable that is neither a
   member of the block nor a nesting inductive. *)
Fail Inductive bad_param (F : Type -> Type) : Type := BadParam : F (bad_param F) -> bad_param F.
#[bypass_check(positivity)]
Inductive bad_param (F : Type -> Type) : Type := BadParam : F (bad_param F) -> bad_param F.
(* expect: Positivity: the block occurs in an argument of a variable that is not an inductive of the block *)
Fail MetaRocq SafeCheck bad_param.

(* Not tested here, because no Rocq declaration has them: a nesting inductive that is
   a mutual block (Rocq's kernel refuses it even with its positivity check bypassed),
   and a nesting inductive whose constructor does not conclude at that inductive.
   [nested_positivity_check.v] runs the checker on hand-built constructor types for
   both, and safechecker/theories/PCUICPositivityCheck.v checks that running out of
   fuel is a refusal ([check_positive_out_of_fuel]). *)
