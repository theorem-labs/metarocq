(* Partial applications of template-polymorphic inductives inside template-polymorphic
   declarations.

   SafeCheck translates each template inductive into a universe-polymorphic one and
   gives each occurrence an instance. PCUIC compares the instance of a partial
   application exactly and has no eta rule, while Rocq's kernel stores no instance on a
   template occurrence and compares two occurrences by their arguments alone. The
   translation therefore eta-expands every partial application of a template inductive
   or constructor. Rocq accepts every declaration below, and so must SafeCheck, except
   in the sections that say otherwise. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

(* The shape of stdpp's gmap: [key K m] applies [key] to 2 of its 3 arguments, and
   [key]'s level has a template upper bound (through [Mono]), as [gmap_key]'s has through
   [RelDecision] and [Countable]. The variance check of [gm] compares its field under two
   unrelated instances. *)
Module Bounded.
Definition Mono (A : Type) : Type := A -> True.
#[universes(template)]
Inductive key (K : Type) (m : Mono K) (q : nat) : Prop := mkkey : (K -> True) -> key K m q.
#[universes(template)]
Inductive dep (A : Type) (P : nat -> Prop) : Type := dn : A -> dep A P.
#[universes(template)]
Record gm (K : Type) (m : Mono K) (A : Type) := GM { car : dep A (key K m) }.
MetaRocq SafeCheck gm.
End Bounded.

(* The same partial application inside an equation. *)
Module BoundedEq.
Definition Mono (A : Type) : Type := A -> True.
#[universes(template)]
Inductive key (K : Type) (m : Mono K) (q : nat) : Prop := mkkey : (K -> True) -> key K m q.
#[universes(template)]
Record gm (K : Type) (m : Mono K) := GM { f : nat -> Prop; e : f = key K m }.
MetaRocq SafeCheck gm.
End BoundedEq.

(* The missing argument binds a level of the inner inductive's conclusion. *)
Module InConclusion.
#[universes(template)]
Inductive w (A : Type) (B : Type) : Type := wc : A -> B -> w A B.
#[universes(template)]
Inductive dep2 (A : Type) (F : Type -> Type) : Type := dn2 : A -> dep2 A F.
#[universes(template)]
Record gm (A : Type) := GM { car : dep2 A (w A) }.
MetaRocq SafeCheck gm.
End InConclusion.

(* The inner level is neither bounded nor in the inner conclusion. *)
Module Unbounded.
#[universes(template)]
Record key (K : Type) (q : nat) : Prop := mkkey { kk : K -> True }.
#[universes(template)]
Inductive dep (A : Type) (P : nat -> Prop) : Type := dn : A -> dep A P.
#[universes(template)]
Record gm (K : Type) (A : Type) := GM { car : dep A (key K) }.
MetaRocq SafeCheck gm.
End Unbounded.

(* A bare template inductive ([eq A] is [eq] applied to 1 of its 3 arguments), in a
   record and in a definition that uses the record. *)
Module EqField.
#[universes(template)]
Record rel_is_eq (A : Type) := RE { r : A -> A -> Prop; h : r = @eq A }.
MetaRocq SafeCheck rel_is_eq.
Definition use : rel_is_eq nat := RE nat (@eq nat) eq_refl.
MetaRocq SafeCheck use.
End EqField.

(* Primitive records: the projection types must equal the field types exactly. *)
Module Primitive.
Definition Mono (A : Type) : Type := A -> True.
#[universes(template)]
Inductive key (K : Type) (m : Mono K) (q : nat) : Prop := mkkey : (K -> True) -> key K m q.
#[universes(template)]
Inductive dep (A : Type) (P : nat -> Prop) : Type := dn : A -> dep A P.
#[universes(template), projections(primitive)]
Record gm (K : Type) (m : Mono K) (A : Type) := GM { car : dep A (key K m) }.
MetaRocq SafeCheck gm.
#[universes(template), projections(primitive)]
Record rel_is_eq (A : Type) := RE { r : A -> A -> Prop; h : r = @eq A }.
MetaRocq SafeCheck rel_is_eq.
End Primitive.

(* A partially applied template constructor in a field. *)
Module Constructor.
#[universes(template)]
Record rc (A : Type) := RC { f1 : A -> list A -> list A; f1e : f1 = @cons A }.
MetaRocq SafeCheck rc.
End Constructor.

(* A match inside a template record. Its instance is the canonical top level, which
   needs every bound level of the record to be below top. *)
Module CaseInRecord.
#[universes(template)]
Record caseT (A : Type) := CT { cx : A * A; cy : match cx with pair _ _ => True end }.
MetaRocq SafeCheck caseT.
End CaseInRecord.

(* A match on a template inductive whose level has a template upper bound: that level
   keeps the instance inferred from the parameters, since top is above the bound. *)
Module CaseBounded.
Definition Mono (A : Type) : Type := A -> True.
#[universes(template)]
Inductive key (K : Type) (m : Mono K) (q : nat) : Prop := mkkey : (K -> True) -> key K m q.
Definition use (K : Type) (m : Mono K) (x : key K m 0) : True := match x with mkkey f => I end.
MetaRocq SafeCheck use.
End CaseBounded.

(* Let-parameters, let-bound constructor arguments, and a missing index whose type
   depends on a given parameter. *)
Module Lets.
#[universes(template)]
Inductive LP (A : Type) (n := 0) (B : Type) : Type := lp : A -> forall (x := n), B -> LP A B.
Definition l1 (X : Type) := LP X.
MetaRocq SafeCheck l1.
Definition l2 (X : Type) := @lp X.
MetaRocq SafeCheck l2.
#[universes(template)]
Inductive Ix (A : Type) : A -> Prop := ix : forall a, Ix A a.
Definition i1 (X : Type) := Ix X.
MetaRocq SafeCheck i1.
End Lets.

(* A partial application whose given argument breaks the template upper bound of the
   level it binds: [keyb Type@{kb}] needs [kb+1 <= kb]. Rocq refuses it; the declaration
   is made with universe checking off, and SafeCheck must refuse it too. *)
Module BoundBroken.
Universe kb.
Definition Bnd (A : Type@{kb}) : Prop := True.
#[universes(template)]
Inductive keyb (K : Type) (q : nat) : Prop := mkb : Bnd K -> keyb K q.
Fail Definition partial_bad : nat -> Prop := keyb Type@{kb}.
Unset Universe Checking.
Definition partial_bad : nat -> Prop := keyb Type@{kb}.
Set Universe Checking.
MetaRocq Test SafeCheck Rejects Source "ctrs not satisfiable" "partial_bad" partial_bad.
End BoundBroken.

(* Bare and partially applied template constructors and inductives in terms. *)
Module Terms.
Definition cons_nat : nat -> list nat -> list nat := @cons nat.
MetaRocq SafeCheck cons_nat.
Definition map_some : list (option nat) := List.map (@Some nat) (0 :: 1 :: nil).
MetaRocq SafeCheck map_some.
Definition pair_with : nat -> nat * bool := fun n => @pair nat bool n true.
Definition ap (F : Type -> Type) (A : Type) := F A.
Definition list_ap : ap list nat := cons 0 nil.
MetaRocq SafeCheck list_ap.
(* A bare template inductive where a function on [Set] is expected: its expansion has a
   binder at [key0]'s template level, which must be convertible with [Set]. *)
#[universes(template)]
Inductive key0 (K : Type) : Prop := k0 : key0 K.
Definition F (G : Set -> Prop) : Prop := True.
Definition at_set := F key0.
MetaRocq SafeCheck at_set.
End Terms.

(** * Refused, as Rocq's kernel refuses them

  Each is preceded by an [expect:] comment, which [check_fail_messages.sh] matches
  against the message of the [Fail MetaRocq SafeCheck] that follows. *)

(* A missing argument's binder is at the template default level, which the context
   requires to be [Set]. With universe checking on, elaborating [F1 key1] adds a
   constraint that makes [key1]'s default level equal to [Set] (as for [Terms.at_set]),
   and Rocq accepts it. Here the declaration is made with universe checking off, so the
   graph has no such constraint and the kernel would refuse the declaration in it. This
   is the test that the expansion's binders are at the defaults. *)
Module DefaultBinder.
#[universes(template)]
Inductive key1 (K : Type) : Prop := k1 : key1 K.
Definition F1 (G : Set -> Prop) : Prop := True.
Unset Universe Checking.
Definition bad_r1 := F1 key1.
Set Universe Checking.
(* expect: domains are not convertible *)
Fail MetaRocq SafeCheck bad_r1.
End DefaultBinder.

(** * Known divergences: Rocq accepts each declaration below, and SafeCheck refuses it.

  Each refused case is preceded by an [expect:] comment, which [check_fail_messages.sh]
  (run on this file by the test-suite Makefile) matches against the message of the
  [Fail MetaRocq SafeCheck] that follows. A change that makes SafeCheck accept one of
  them shows up here. *)

(* A match on a bounded template inductive inside a template record. The match's
   instance keeps the level inferred from the parameters for a bounded level (the
   program's top level is above the bound), that level is the record's own, and the
   variance check of the record compares the instance exactly. *)
Module CaseBoundedInRecord.
Definition Mono (A : Type) : Type := A -> True.
#[universes(template)]
Inductive key (K : Type) (m : Mono K) (q : nat) : Prop := mkkey : (K -> True) -> key K m q.
#[universes(template)]
Record usr (K : Type) (m : Mono K) := US { ux : key K m 0; uy : match ux with mkkey f => True end }.
(* expect: Terms are not equal *)
Fail MetaRocq SafeCheck usr.
End CaseBoundedInRecord.

(* A universe-polymorphic, cumulative declaration whose field applies a template
   inductive partially. *)
Module PolymorphicOuter.
Definition Mono (A : Type) : Type := A -> True.
#[universes(template)]
Inductive key (K : Type) (m : Mono K) (q : nat) : Prop := mkkey : (K -> True) -> key K m q.
#[universes(template)]
Inductive dep (A : Type) (P : nat -> Prop) : Type := dn : A -> dep A P.
#[universes(polymorphic, cumulative)]
Record gm (K : Type) (m : Mono K) (A : Type) := GM { car : dep A (key K m) }.
(* expect: ctrs not satisfiable *)
Fail MetaRocq SafeCheck gm.
End PolymorphicOuter.

(** * Fixpoints whose body has fewer leading lambdas than its [struct] argument needs

  Rocq's kernel refuses them, also with guard checking off, as each [Fail Definition]
  below shows. The terms are built with Ltac2's unsafe constructor, and filled in with
  [Std.exact_no_check], which does not retype them: [Control.refine] would retype, and
  the refusal would come from elaboration rather than from the checker.

  The expansion of a partial template application in a body can add a lambda, so the
  translation runs the kernel's own check on the original term before it quotes it. *)
Module FixShape.
From Ltac2 Require Import Ltac2.
Ltac2 mk_fix (rarg : int) (ty : constr) (body : constr) : constr :=
  Constr.Unsafe.make
    (Constr.Unsafe.Fix [| rarg |] 0
       [| Constr.Binder.unsafe_make (Some @f) Constr.Binder.Relevant ty |] [| body |]).
(* The body is a template constructor given 2 of its 3 arguments. *)
Fail Definition b1 : list nat -> list nat :=
  ltac2:(Std.exact_no_check (mk_fix 0 constr:(list nat -> list nat) constr:(@cons nat 0))).
(* expect: Not enough abstractions in the definition *)
Fail MetaRocq SafeCheck
  (ltac2:(Std.exact_no_check (mk_fix 0 constr:(list nat -> list nat) constr:(@cons nat 0)))
    : list nat -> list nat).
(* The body is a template inductive given 2 of its 3 arguments. *)
Fail Definition b2 : nat -> Prop :=
  ltac2:(Std.exact_no_check (mk_fix 0 constr:(nat -> Prop) constr:(@eq nat 0))).
(* expect: Not enough abstractions in the definition *)
Fail MetaRocq SafeCheck
  (ltac2:(Std.exact_no_check (mk_fix 0 constr:(nat -> Prop) constr:(@eq nat 0)))
    : nat -> Prop).
(* The struct argument is the second, and the body has one lambda. No template
   application is involved: PCUIC checked only the first lambda. *)
Axiom g : nat -> list nat -> list nat.
Fail Definition b4 : nat -> list nat -> list nat :=
  ltac2:(Std.exact_no_check
    (mk_fix 1 constr:(nat -> list nat -> list nat) constr:(fun n : nat => g n))).
(* expect: Not enough abstractions in the definition *)
Fail MetaRocq SafeCheck
  (ltac2:(Std.exact_no_check
     (mk_fix 1 constr:(nat -> list nat -> list nat) constr:(fun n : nat => g n)))
    : nat -> list nat -> list nat).
(* The same fixpoint as the first, with its lambda: accepted. *)
Definition with_lambda : list nat -> list nat :=
  ltac2:(Std.exact_no_check
    (mk_fix 0 constr:(list nat -> list nat) constr:(fun l : list nat => @cons nat 0 l))).
MetaRocq SafeCheck with_lambda.
End FixShape.

(** * Known divergence: a fixpoint that a functor application made eta-short

  The kernel checks the body of [F.d] where [X.c] is the signature's [fun m => h m], so
  it has two lambdas before its [struct] argument. A functor application is not
  retyped: it checks the argument's subtyping, which compares bodies up to eta, and
  substitutes. So [N.d]'s body has one lambda before its [struct] argument, and the
  kernel keeps it, as [Print Assumptions N.d] shows. Written directly, the kernel
  refuses that body ([Fail Definition] below). The translation's check reads the body
  alone, so it refuses [N.d] too. *)
Module FunctorShort.
From Ltac2 Require Import Ltac2.
Ltac2 mk_fix (rarg : int) (ty : constr) (body : constr) : constr :=
  Constr.Unsafe.make
    (Constr.Unsafe.Fix [| rarg |] 0
       [| Constr.Binder.unsafe_make (Some @f) Constr.Binder.Relevant ty |] [| body |]).
Module Type T.
  Parameter h : nat -> nat.
  Definition c : nat -> nat := fun m => h m.
End T.
Module M <: T.
  Axiom h : nat -> nat.
  Definition c : nat -> nat := h.
End M.
Module F (X : T).
  Definition d : nat -> nat -> nat :=
    ltac2:(Std.exact_no_check
      (mk_fix 1 constr:(nat -> nat -> nat) constr:(fun n : nat => X.c))).
End F.
Module N := F M.
Fail Definition d_direct : nat -> nat -> nat :=
  ltac2:(Std.exact_no_check (mk_fix 1 constr:(nat -> nat -> nat) constr:(fun n : nat => M.c))).
(* expect: Not enough abstractions in the definition *)
Fail MetaRocq SafeCheck N.d.
End FunctorShort.
