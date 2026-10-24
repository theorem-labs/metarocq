From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From MetaRocq Require Import SafeCheckerPlugin.SafeTemplateChecker.

Local Open Scope string_scope.

MetaRocq SafeCheck nat.
(*
Environment is well-formed and Ind(Stdlib.Init.Datatypes.nat,0,[]) has type: Sort([Set])
*)

MetaRocq SafeCheck (3 + 1).

Definition bool_list := List.map negb (cons true (cons false nil)).
(* was working a bit by accident *)
(* MetaRocq SafeCheck bool_list. *)
MetaRocq RocqCheck bool_list.

Record template_list_record := { template_list_field : list nat }.
MetaRocq SafeCheck template_list_record.
MetaRocq SafeCheck (list nat).

Definition template_list_to_nat : list nat -> nat := fun _ => 0.
MetaRocq SafeCheck template_list_to_nat.

Definition template_list_match (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | cons x _ => x
  end.
MetaRocq SafeCheck template_list_match.

From Stdlib Require Import Ring_theory.
MetaRocq SafeCheck (prod nat nat).
MetaRocq SafeCheck (prod True True).
MetaRocq SafeCheck @Stdlib.setoid_ring.Ring_theory.div_theory.
From Corelib Require Import CRelationClasses.

(* [iffT] applies template [prod] at [max(i,j)] inside a polymorphic
   declaration.  It therefore covers scoped algebraic instances, their
   explicit sort annotations, and the extended universe instance at use. *)
Definition template_iffT_nat := iffT nat nat.
MetaRocq SafeCheck template_iffT_nat.

(* [sigT]'s second template parameter is a family [A -> Type@{u}], not a sort;
   the kernel binds [u] from the arity's conclusion (make_param_univs). *)
Definition template_sigT_nat := {n : nat & nat}.
MetaRocq SafeCheck template_sigT_nat.

(* One kernel match on template [prod] reached in two contexts.  The kernel
   stores no instance on it, so the translated case instance must not depend
   on the context.  Typing [f h] converts [template_case_eq nat p] with
   [template_case_eq_nat p]; both unfold to the stuck match on [p], quoted
   once with [C : Type@{template_case_u}] and once with [nat : Set]
   (LemmaPin_23: Ring_polynom's [cdiv] match, at [Ring_polynom.22] and
   [Ring_theory.98]).  The quoter types a constant by retyping its body, so
   the conversion has to occur inside the body.  A named universe keeps
   minimization from turning [template_case_u] into [Set]. *)
Universe template_case_u.
Definition template_case_eq (C : Type@{template_case_u}) (p : C * C) : Prop :=
  match p with pair a b => a = b end.
Definition template_case_eq_nat (p : nat * nat) : Prop :=
  match p with pair a b => a = b end.
Definition template_case_instance (p : nat * nat)
  (f : template_case_eq_nat p -> nat) (h : template_case_eq nat p) : nat :=
  f h.
MetaRocq SafeCheck @template_case_instance.

(* A partially applied template inductive is compared with exact instances
   in PCUIC.  Typing [g _ h] converts [template_partial_rel nat], which
   unfolds to [@eq A] quoted at [A : Type@{template_case_u}], with [@eq nat]
   (Z.eq_equiv: [eq@{RelationClasses.21} Z] against [eq@{Set} Z]). *)
Definition template_partial_rel (A : Type@{template_case_u}) : A -> A -> Prop :=
  @eq A.
Definition template_partial_instance (P : (nat -> nat -> Prop) -> Prop)
  (g : forall R, P R -> nat) (h : P (@eq nat)) : nat :=
  g (template_partial_rel nat) h.
MetaRocq SafeCheck @template_partial_instance.
Set Universe Polymorphism.

(* This nested use gives [list] the algebraic template instance [max(i,j)].
   It exercises the shared representative in both the list instance and the
   explicit result-sort annotation. *)
Polymorphic Definition template_list_prod@{i j}
  (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  list (prod A B).
Definition template_list_prod_nat := template_list_prod nat nat.
MetaRocq SafeCheck template_list_prod_nat.

(* Negative control: [list Type@{i}] lives in [Type@{i+1}], so it must not
   typecheck at [Type@{i}]. *)
Fail Polymorphic Definition template_successor_too_low@{i} : Type@{i} :=
  list Type@{i}.

Unset Universe Polymorphism.




(* Time MetaRocq SafeCheck @infer_and_print_template_program. *)
(* Uses template polymorphism:
Error:
Type error: Terms are not <= for cumulativity: Sort([Stdlib.Init.Datatypes.23,Stdlib.Init.Datatypes.24]) Sort([Set]) after reduction: Sort([Stdlib.Init.Datatypes.23,Stdlib.Init.Datatypes.24]) Sort([Set]), while checking MetaRocq.Template.Universes.Universe.Expr.t
*)

(* Unset Universe Minimization ToSet. *)

(* From Stdlib Require Import Decimal. *)
From Stdlib Require Import Decimal.
Definition bignat : nat := Nat.of_num_uint 10000%uint.
MetaRocq SafeCheck bignat.
MetaRocq RocqCheck bignat.

Set Warnings "-notation-overriden".
From MetaRocq.TestSuite Require Import hott_example.

MetaRocq SafeCheck @issect'.

MetaRocq SafeCheck @ap_pp.
MetaRocq RocqCheck ap_pp.

Set MetaRocq Timing.

From MetaRocq.TestSuite Require Import hott_example.

(* FIXME TODO Private polymorphic universes *)
MetaRocq SafeCheck @isequiv_adjointify.
MetaRocq RocqCheck isequiv_adjointify.

MetaRocq SafeCheck @IsEquiv.
MetaRocq RocqCheck IsEquiv.
