From MetaRocq.SafeCheckerPlugin Require Import Loader.

(** SafeCheck must refuse every fixpoint and cofixpoint that Rocq's kernel
    refuses.  Each refused definition below is made with the kernel's guard
    checking turned off, and each [Fail] asserts that SafeCheck refuses it.
    Each refused shape has a twin that the kernel accepts, and SafeCheck must
    accept the twin. *)

(** The recursive parameter itself is not a structural subterm. *)
Unset Guard Checking.
Fixpoint loop (n : nat) : False := loop n.
Set Guard Checking.

Fail MetaRocq SafeCheck loop.
Definition loop_false : False := loop 0.
Fail MetaRocq SafeCheck loop_false.

(** A non-recursive constructor argument is not a structural subterm, even
    when its type is the same inductive at another parameter instance. *)
Inductive W (A : Type) : Type := w : A -> W A | e : W A.

Unset Guard Checking.
Fixpoint w_f (x : W (W nat)) : nat :=
  match x with w _ a => w_g a | e _ => 0 end
with w_g (y : W nat) : nat := 0.
Set Guard Checking.

Fail MetaRocq SafeCheck w_f.

(** Twin: the argument of a recursive constructor is a structural subterm. *)
Inductive R (A : Type) : Type := r : R A -> R A | z : R A.

Fixpoint r_f (x : R nat) : nat :=
  match x with r _ a => r_f a | z _ => 0 end.

MetaRocq SafeCheck r_f.

(** Uniform parameters of a nested fixpoint are counted as Rocq's kernel
    counts them ([find_uniform_parameters]): at an application whose head is
    a variable, an argument that is a call of the nested block counts as an
    occurrence of that function with no arguments, so no parameter is
    uniform; an argument of any other shape is visited subterm by subterm.
    In [u_f], [g u m' acc] is such an argument of [g u m' _], so [u] is not
    uniform and [u_f u] is a call on a variable that is not a subterm.
    (In [u_h] below the call is reached one application deeper, through the
    argument [h (g u m')], and [u] stays uniform.) *)
Inductive lst : Set := nl : lst | cs : nat -> lst -> lst.

Unset Guard Checking.
Fixpoint u_f (l : lst) {struct l} : nat :=
  match l with
  | nl => 0
  | cs x t =>
    (fix g (u : lst) (m : nat) (acc : nat) {struct m} : nat :=
       match m with
       | O => u_f u
       | S m' => g u m' (g u m' acc)
       end) t x 0
  end.
Set Guard Checking.

Fail MetaRocq SafeCheck u_f.

(** Twin: the nested call is under a constructor, so [u] is uniform and is
    the subterm [t]. *)
Fixpoint u_g (l : lst) {struct l} : nat :=
  match l with
  | nl => 0
  | cs x t =>
    (fix g (u : lst) (m : nat) (acc : nat) {struct m} : nat :=
       match m with
       | O => u_g u
       | S m' => S (g u m' acc)
       end) t x 0
  end.

MetaRocq SafeCheck u_g.

(** The nested call [g u m'] sits under two applications of a variable,
    [h (h (g u m'))]: as in Rocq's kernel, the count reaches [g u m'] and
    [u] stays uniform. *)
Fixpoint u_h (h : nat -> nat) (l : lst) {struct l} : nat :=
  match l with
  | nl => 0
  | cs x t =>
    (fix g (u : lst) (m : nat) {struct m} : nat :=
       match m with
       | O => u_h h u
       | S m' => h (h (g u m'))
       end) t x
  end.

MetaRocq SafeCheck u_h.

(** A cofixpoint may produce a call to its block only in a recursive argument
    of the constructor, never in a non-recursive one. *)
CoInductive Stream (A : Type) : Type := Cons : A -> Stream A -> Stream A.

Unset Guard Checking.
CoFixpoint s_f : Stream (Stream nat) := Cons _ s_g s_f
with s_g : Stream nat := Cons _ 0 s_g.
Set Guard Checking.

Fail MetaRocq SafeCheck s_f.

(** Twin: the call in the recursive argument. *)
CoFixpoint ones : Stream nat := Cons _ 1 ones.

MetaRocq SafeCheck ones.

(** An inductive nested through a coinductive.  The argument of a
    coinductive constructor is not a subterm, and a cofixpoint cannot put a
    call to its block in a non-recursive argument: together these two would
    let [t_f (C t_s)] reduce to itself.  The types live in [Set], so that no
    template universe is instantiated.  While PCUIC has no nested inductive
    types, SafeCheck refuses the declaration of [T] itself, before any guard
    check; these lines then hold trivially, and they test the guard once
    nested inductives are allowed.  The guard rules themselves are tested on
    this pair without SafeCheck, in [guard_cases_test.v] and in
    [PCUICGuardCheckerRegress]. *)
CoInductive SStream (A : Set) : Set := SCons : A -> SStream A -> SStream A.
Inductive T : Set := C : SStream T -> T.

Unset Guard Checking.
CoFixpoint t_s : SStream T := SCons T (C t_s) t_s.
Fixpoint t_f (x : T) : nat :=
  match x with C y => match y with SCons _ t _ => t_f t end end.
Set Guard Checking.

Fail MetaRocq SafeCheck t_s.
Fail MetaRocq SafeCheck t_f.
Definition t_loop := t_f (C t_s).
Fail MetaRocq SafeCheck t_loop.
