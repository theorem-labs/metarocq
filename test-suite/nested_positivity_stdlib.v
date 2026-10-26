(* Nested inductive types over Stdlib's template-polymorphic types [list], [option]
   and [prod].

   These need SafeCheck to handle template-polymorphic inductives: without that, every
   accepted case below is refused at the universe check of its constructors
   ("Incorrect inductive sort"), after positivity has passed. The file is therefore
   not in this test suite's [_RocqProject.in]; it is meant for a tree that has
   template-polymorphism support.

   [ZMicromega.ZArithProof] is Stdlib's nested inductive: its [EnumProof]
   constructor takes a [list ZArithProof]. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From Stdlib Require Import ZMicromega.

(** * Accepted *)

MetaRocq SafeCheck ZMicromega.ZArithProof.

(* The rose-tree control: the shape of [ZArithProof]'s [EnumProof] constructor. *)
Inductive rose := Node : list rose -> rose.
MetaRocq SafeCheck rose.

(* Nested through [option], beside a non-recursive argument. *)
Inductive opt_tree := OptNode : option opt_tree -> nat -> opt_tree.
MetaRocq SafeCheck opt_tree.

(* A mutual block with a nested occurrence of its other member. *)
Inductive mt1 := M1 : list mt2 -> mt1
with mt2 := M2 : mt1 -> mt2.
MetaRocq SafeCheck mt1.

(* Nesting inside nesting: [prod] inside [list]. *)
Inductive rose_prod := NodeP : list (prod nat rose_prod) -> rose_prod.
MetaRocq SafeCheck rose_prod.

(* The nested occurrence mentions a parameter of the block being defined. *)
Inductive prose (A : Type) := PNode : A -> list (prose A) -> prose A.
MetaRocq SafeCheck prose.

(* The outer type is itself nested inside [prod]. *)
Inductive W (A : Type) := w : prod nat (W A) -> W A | wleaf : A -> W A.
Inductive use_w := UseW : W use_w -> use_w.
MetaRocq SafeCheck use_w.

(** * Rejected *)

(* As in nested_positivity.v, each [expect:] comment gives text that the message
   of the next [Fail MetaRocq SafeCheck] must contain. *)

(* Two nestings deep, the block to the left of an arrow. *)
Fail Inductive bad_nested2 := BadNested2 : list (prod nat (bad_nested2 -> False)) -> bad_nested2.
#[bypass_check(positivity)]
Inductive bad_nested2 := BadNested2 : list (prod nat (bad_nested2 -> False)) -> bad_nested2.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_nested2.

(* The block in an index of the outer type. *)
Inductive I : Type -> Type := ic : I nat.
Fail Inductive bad_index := BadIndex : I bad_index -> bad_index.
#[bypass_check(positivity)]
Inductive bad_index := BadIndex : I bad_index -> bad_index.
(* expect: Nested positivity: the block occurs in an argument that is not a uniform parameter *)
Fail MetaRocq SafeCheck bad_index.

(* Incompleteness, by design: nesting in a primitive array. The kernel accepts it
   (Rocq's test-suite/primitive/arrays/nested.v). *)
From Corelib Require Import PrimArray.
Inductive arr_tree := ANode : array arr_tree -> arr_tree.
(* expect: Positivity: the block occurs under a head that is neither a member of the block nor an inductive *)
Fail MetaRocq SafeCheck arr_tree.

(* A cumulative block with a covariant universe level is refused by positivity too
   (nested_positivity_check.v, [Check_cov]); through SafeCheck it does not get that
   far, so it is not tested here. *)
