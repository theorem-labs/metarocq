From MetaRocq.TestPlugin Require Import Loader.

(* Regressions for the translation of template-polymorphic inductives that
   SafeCheck runs before checking (see safechecker_test.v). *)

(* Changing impredicative Set changes the sort retyping assigns to this shared
   template argument.  The test command uses one quotation cache across both
   environments and compares the second result with a fresh quotation. *)
Universe template_cache_flags_u.
MetaRocq Test Cache Typing Flags
  (list (forall X : Type@{template_cache_flags_u}, nat)).

(* The compound product has a scope-dependent child.  The test confirms a hit
   in the same scope, a miss in another scope, and rejection outside a scope. *)
MetaRocq Test Quoter Scope Cache.

Set Universe Polymorphism.
Polymorphic Definition template_state_restore_source@{u}
  (A : Type@{u}) := list A.
(* The test hook raises after [quote_term_rec] → [quote_declaration] has
   installed name, scope, dependency root and in-progress state.  The command
   then checks that a translating quotation outside any declaration still
   rejects a bound-variable universe, as it must when no scope is installed. *)
MetaRocq Test Quoter Restores State @template_state_restore_source.

(* The upper-bound pass must let [Control.Timeout] leave its graph query. *)
MetaRocq Test Quoter Propagates Timeout.

(* This calls the extracted SafeCheck entrypoint after trusted quotation, then
   adds a quoted declaration whose [Type@{Set}] body is claimed at
   [Type@{Set}], the successor-too-low condition that Rocq rejects for
   [template_successor_too_low] in safechecker_test.v. *)
MetaRocq Test SafeCheck Rejects
  "Terms
Type([Set+1])
and
Type([Set])
do not have the same head when comparing for cumulativity"
  "while checking Regression.MetaRocq.successor_too_low" nat.

(* Input-side negative fixtures: the obligation each one breaks exists in the
   environment before quotation, and each goes through the production
   SafeCheck path.  Each asserts the part of the checker's message that names
   the failing check and its two sorts, and the subject of the rejection. *)

(* [Set : Type@{Set+1}], so this declaration's claimed type is wrong.  The
   quoter must hand the checker this declared type, not a type inferred from
   the body, which would be the type of a repaired declaration. *)
Unset Universe Checking.
Definition template_declared_type_is_checked : Set := Set.
Set Universe Checking.
MetaRocq Test SafeCheck Rejects Source
  "Terms
Type([Set+1])
and
Type([Set])
do not have the same head when comparing for cumulativity"
  "template_declared_type_is_checked"
  template_declared_type_is_checked.

(* A bound universe [u] has no lower bound, so a cast from
   [Type@{max(Set+1,u)}] to [Type@{u}] is not justified.  Dropping the [Set+1]
   component would make that cast reflexive and erase the obligation.  Rocq
   cannot write an algebraic sort in a binder, so the command builds the
   declaration in the kernel environment the quoter reads.  The checker sees
   [max(Set+1,u)] as the fresh bound level [lvar1] and [u] as [lvar0]. *)
MetaRocq Test Quoter Set Successor Cast
  "Terms
Type([lvar1])
and
Type([lvar0])
do not have the same head when comparing for cumulativity"
  "while checking Regression.MetaRocq.set_successor_cast".

(* [bad : Type@{d} := list Type@{d}], where [d] is [list]'s own template
   default universe.  [Type@{d} : Type@{d+1}], so the declaration needs
   [d+1 <= d] and must be rejected.  Its body is headed by a template
   inductive, so it reaches the path where a substitution keyed on the body's
   instance could replace the declared [d] by the body's larger
   representative and repair the declaration.  The default is read from the
   inductive's metadata, not named here; the checker's message names it
   ([Corelib.Init.Datatypes.190] in Rocq 9.2), next to the body's sort,
   which the quoter names [Template.MetaRocq.algebraic.1]. *)
MetaRocq Test Quoter Declared Default
  "Terms
Type([Template.MetaRocq.algebraic.1])
and
Type([Corelib.Init.Datatypes.190])
do not have the same head when comparing for cumulativity"
  "while checking Regression.MetaRocq.declared_type_successor" list.

Unset Universe Polymorphism.
