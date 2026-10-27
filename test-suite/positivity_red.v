(* Positivity up to weak-head reduction.

   Rocq's kernel puts every constructor argument type in weak-head normal form
   ([whd_all] at the start of [check_strict_positivity], kernel/indtypes.ml) before it
   reads its head, it reduces the arguments of a variable head, and it reduces the
   domain of a product when the domain mentions the block ([weaker_noccur_between]).
   The safe checker does the same.

   Accepted cases: Rocq's kernel accepts each of them, and so must the checker.
   Rejected cases: each is defined with Rocq's positivity check bypassed, a
   [Fail Inductive] beside it shows that Rocq's kernel refuses the same definition,
   and the checker must refuse it too. Each refused case is preceded by an [expect:]
   comment; [check_fail_messages.sh], which the test-suite Makefile runs on this file,
   checks that the message of the [Fail MetaRocq SafeCheck] that follows contains it.
   Divergences: one declaration that the kernel refuses and the checker accepts, and
   two that the kernel accepts and the checker refuses, each with the reason.

   Every type here is in [Set], [Prop] or a fixed [Type], and none is
   template-polymorphic, so the file does not depend on how SafeCheck handles
   template-polymorphic types. *)

From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

Inductive mlist (A : Set) : Set := mnil : mlist A | mcons : A -> mlist A -> mlist A.

(** * Accepted *)

(* Kernel: accepts. Checker: accepts. The shape of stdpp's [list_elem_of]: a class
   with one method, so [eof] is a constant whose body returns its instance argument.
   The second constructor's argument is [eof x l], the block under the constant
   [eof]; its declared arity is the class, which arity_delta.v tests. *)
Class EOf (A C : Set) := eof : A -> C -> Prop.
Inductive pr_elem {A : Set} : EOf A (mlist A) :=
| pr_here (x : A) l : eof x (mcons A x l)
| pr_further (x y : A) l : eof x l -> eof x (mcons A y l).
MetaRocq SafeCheck (@pr_elem).

(* Kernel: accepts. Checker: accepts. The block under a constant that unfolds to a
   nesting inductive. *)
Definition L (A : Set) : Set := mlist A.
Inductive via_const : Set := VC : L via_const -> via_const.
MetaRocq SafeCheck via_const.

(* Kernel: accepts. Checker: accepts. A product domain that mentions the block only
   before reduction: the kernel reduces it ([weaker_noccur_between]) and finds no
   occurrence. *)
Definition K (X : Set) : Set := nat.
Inductive pr_dom : Set := pr_dom_c : (K pr_dom -> nat) -> pr_dom.
MetaRocq SafeCheck pr_dom.

(* Kernel: accepts. Checker: accepts. The argument type itself reduces to a type
   that does not mention the block. *)
Inductive pc : Set := pc_c : K pc -> pc.
MetaRocq SafeCheck pc.

(* Kernel: accepts. Checker: accepts. Reduction through a match on a constructor. *)
Definition sel (b : bool) (X : Set) : Set := if b then X else nat.
Inductive pr_iota : Set := pr_iota_c : sel true pr_iota -> pr_iota.
MetaRocq SafeCheck pr_iota.

(* Kernel: accepts. Checker: accepts. Reduction through a fixpoint applied to a
   constructor. *)
Fixpoint iter (n : nat) (X : Set) : Set :=
  match n with 0 => X | S n => iter n X end.
Inductive pr_fix : Set := pr_fix_c : iter 2 pr_fix -> pr_fix.
MetaRocq SafeCheck pr_fix.

(* Kernel: accepts. Checker: accepts. Reduction through a let and a beta-redex in the
   constant's body. *)
Definition lalias (X : Set) : Set := let Y := X in (fun Z : Set => Z) Y.
Inductive pr_let : Set := pr_let_c : lalias pr_let -> pr_let.
MetaRocq SafeCheck pr_let.

(* Kernel: accepts. Checker: accepts. A reducible argument of a nesting inductive:
   [mlist (L pr_nest)]; [mcons]'s arguments, instantiated, are [L pr_nest] and
   [mlist (L pr_nest)]. This is the case that depends on keeping the instance of the
   nesting variable as written: the recursive occurrence in [mcons] is the nesting
   variable applied to [L pr_nest], which is compared with the recorded instance
   [L pr_nest] and would not match its reduct [mlist pr_nest]. *)
Inductive pr_nest : Set := pr_nest_c : mlist (L pr_nest) -> pr_nest.
MetaRocq SafeCheck pr_nest.

(* Kernel: accepts. Checker: accepts. A redex that appears only when the nesting
   inductive's constructor is instantiated: [wF]'s argument [F A] becomes
   [(fun X => mlist X) pr_wf]. *)
Inductive wrapF (F : Set -> Set) (A : Set) : Set := wF : F A -> wrapF F A.
Inductive pr_wf : Set := pr_wf_c : wrapF (fun X => mlist X) pr_wf -> pr_wf.
MetaRocq SafeCheck pr_wf.

(* Kernel: accepts. Checker: accepts. The argument of a member of the block reduces
   to a type without the block, so the occurrence is a plain recursive one. *)
Inductive T : Set -> Set := C : T ((fun _ : Set => nat) (T nat)) -> T nat.
MetaRocq SafeCheck T.

(* Kernel: accepts. Checker: accepts. The same, with a negative occurrence that the
   reduction removes. *)
Inductive T3 : Set -> Set := C3 : T3 ((fun _ : Set => nat) (T3 nat -> nat)) -> T3 nat.
MetaRocq SafeCheck T3.

(* Kernel: accepts. Checker: accepts. The argument of a parameter reduces to a type
   without the block, so the occurrence is block-free. *)
Inductive W (F : Set -> Set) : Set := Wc : F ((fun _ : Set => nat) (W F)) -> W F.
MetaRocq SafeCheck W.

(* Kernel: accepts. Checker: accepts. In the walk of the nesting inductive [V], the
   index of its own recursive occurrence, instantiated, is [(fun _ : Set => n) vt],
   which mentions the block until it is reduced. *)
Inductive V (A : Set) : nat -> Set :=
| vnil : V A 0
| vcons : forall n, A -> V A ((fun _ : Set => n) A) -> V A (S n).
Inductive vt : Set := vtc : forall n, V vt n -> vt.
MetaRocq SafeCheck vt.

(* Kernel: accepts. Checker: accepts. In the walk of the nesting inductive [D], its own
   recursive occurrence, instantiated, is the nesting variable applied to the instance
   [pr_dn] and to [(fun _ : Set => nat) pr_dn], which reduces to [nat]. *)
Inductive D (A : Set) : Set -> Set := dc : D A ((fun _ : Set => nat) A) -> D A nat.
Inductive pr_dn : Set := pr_dnc : D pr_dn nat -> pr_dn.
MetaRocq SafeCheck pr_dn.

(* Kernel: accepts. Checker: accepts. The self-occurrence of the nesting inductive [bx]
   in its constructor type is under a beta-redex, which the walk reduces. [Check bxc]
   prints the type reduced, but the constructor type that MetaRocq quotes keeps the
   redex [(fun X : Set => X) (bx A)], so this case does reach the reduction. The
   SafeCheck of [pr_bx] also checks [bx]'s own declaration, which needs the same
   reduction: without it, SafeCheck refused [bx] itself. *)
Inductive bx (A : Set) : Set := bxc : (fun X : Set => X) (bx A) -> bx A.
Inductive pr_bx : Set := pr_bxc : bx pr_bx -> pr_bx.
MetaRocq SafeCheck pr_bx.

(* Kernel: accepts. Checker: accepts. The argument type reduces to the axiom [Ax], a
   closed term whose head is neither a product, a variable nor an inductive. *)
Axiom Ax : Set.
Definition KA (X : Set) : Set := Ax.
Inductive pka : Set := pkac : KA pka -> pka.
MetaRocq SafeCheck pka.

(* Kernel: accepts. Checker: accepts. A primitive projection of a record constructor:
   [rs {| rs := prj |}] reduces to [prj], the block itself. *)
#[projections(primitive)] Record RS : Type := { rs : Set }.
Inductive prj : Set := prjc : rs {| rs := prj |} -> prj.
MetaRocq SafeCheck prj.

(* Not tested: a match on a cofixpoint, which reduces by unfolding the cofixpoint. On
   this branch SafeCheck refuses every match on a coinductive type ("Case on
   coinductives disallowed"), so the environment of such a test is refused before its
   positivity is checked. *)

(** * Rejected *)

(* Kernel: refuses. Checker: refuses. A constant that unfolds to an arrow with the
   block on its left. *)
Definition Neg (X : Set) : Set := X -> nat.
Fail Inductive bad_neg : Set := BadNeg : Neg bad_neg -> bad_neg.
#[bypass_check(positivity)]
Inductive bad_neg : Set := BadNeg : Neg bad_neg -> bad_neg.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_neg.

(* Kernel: refuses. Checker: refuses. A product domain that still mentions the block
   after reduction. *)
Definition Id (X : Set) : Set := X.
Fail Inductive bad_dom : Set := BadDom : (Id bad_dom -> nat) -> bad_dom.
#[bypass_check(positivity)]
Inductive bad_dom : Set := BadDom : (Id bad_dom -> nat) -> bad_dom.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_dom.

(* Kernel: refuses. Checker: refuses. An axiom does not reduce: the block stays under
   a head that is not an inductive. *)
Axiom F : Set -> Set.
Fail Inductive bad_ax : Set := BadAx : F bad_ax -> bad_ax.
#[bypass_check(positivity)]
Inductive bad_ax : Set := BadAx : F bad_ax -> bad_ax.
(* expect: Positivity: the block occurs under a head that is neither a member of the block nor an inductive *)
Fail MetaRocq SafeCheck bad_ax.

(* Kernel: refuses. Checker: refuses. A match on a variable does not reduce. *)
Definition selv (b : bool) (X : Set) : Set := if b then X else (X -> nat).
Fail Inductive bad_stuck (b : bool) : Set := BadStuck : selv b (bad_stuck b) -> bad_stuck b.
#[bypass_check(positivity)]
Inductive bad_stuck (b : bool) : Set := BadStuck : selv b (bad_stuck b) -> bad_stuck b.
(* expect: Positivity: the block occurs under a head that is neither a member of the block nor an inductive *)
Fail MetaRocq SafeCheck bad_stuck.

(* Kernel: refuses. Checker: refuses. A redex that appears only when the nesting
   inductive's constructor is instantiated, and reduces to an arrow with the block on
   its left: [wF]'s argument [F A] becomes [(fun X => X -> nat) bad_wf]. *)
Fail Inductive bad_wf : Set := BadWf : wrapF (fun X => X -> nat) bad_wf -> bad_wf.
#[bypass_check(positivity)]
Inductive bad_wf : Set := BadWf : wrapF (fun X => X -> nat) bad_wf -> bad_wf.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_wf.

(* Kernel: refuses. Checker: refuses. A constant that unfolds to a nesting inductive
   whose argument has the block on the left of an arrow. *)
Fail Inductive bad_L : Set := BadL : L (bad_L -> nat) -> bad_L.
#[bypass_check(positivity)]
Inductive bad_L : Set := BadL : L (bad_L -> nat) -> bad_L.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck bad_L.

(** * Divergences *)

(* Kernel: refuses. Checker: accepts. The kernel does not unfold the opaque [OpId], so
   it refuses the declaration. SafeCheck quotes the environment with the bodies of
   opaque constants, so it unfolds [OpId] and finds the block as the whole argument
   type. This is sound: SafeCheck checks the environment in which [OpId] is
   transparent, and in that environment the declaration is positive. *)
Definition OpId (X : Set) : Set.
Proof. exact X. Qed.
Fail Inductive bad_opaque : Set := BadOp : OpId bad_opaque -> bad_opaque.
#[bypass_check(positivity)]
Inductive bad_opaque : Set := BadOp : OpId bad_opaque -> bad_opaque.
MetaRocq SafeCheck bad_opaque.

(* Kernel: accepts. Checker: refuses. The kernel tests the instance of a nesting
   inductive only through the constructor types it substitutes it into, and [ph] has no
   argument, so [I -> nat] is never tested. The rules require the instance itself to be
   positive, and [I] is on the left of an arrow. *)
Inductive Ph (A : Set) : Set := ph : Ph A.
Inductive I : Set := Ic : Ph (I -> nat) -> I.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck I.

(* Kernel: accepts. Checker: refuses. The kernel reduces with call-by-need sharing:
   the argument [(fun _ : Set => true) S] of [H] is reduced once, to [true], when the
   match reads it, and the other occurrences of that argument become [true] too, so the
   reduct [true = true -> nat] does not mention [S]. The reduction relation of the
   checker has no sharing: its reduct is [(fun _ => true) S = (fun _ => true) S -> nat],
   whose domain mentions [S]. This declaration is last because it hides the successor
   function [S]. *)
Definition H (b : bool) (X : Set) : Set := if b then (b = b -> X) else nat.
Inductive S : Set := Sc : H ((fun _ : Set => true) S) nat -> S.
(* expect: Non-positive occurrence. *)
Fail MetaRocq SafeCheck S.
