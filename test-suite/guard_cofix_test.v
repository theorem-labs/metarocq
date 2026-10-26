(** Tests of the cofixpoint guard check [check_guard_gen _ _ _ CoFix]
    ([check_cofix_block] of [PCUICGuardCoFix]), on quoted blocks.

    A block that Rocq accepts is quoted as a [cofix].  A block that Rocq
    refuses is quoted as an abstraction [fun g : A => body] (after the same
    leading [let]s): the body of that abstraction is exactly the body of
    [cofix g : A := body], and Rocq checks no guard condition on an
    abstraction.  A mutual block [cofix f : A := bf with g : B := bg] is
    quoted as [fun (f : A) (g : B) => (bf, bg)].

    The test runs the check on the quoted block, stripped as SafeCheck strips
    it, with SafeCheck's fuel, and asserts the answer, with the reason of each
    refusal.  The check runs directly, without the case well-formedness test
    of [check_guard_impl], because PCUIC's typing refuses every [match] on a
    coinductive type: several shapes below would be refused for that reason
    alone, and the guard check must refuse them on its own as well.  Every
    assertion is an [Example] proved by [vm_compute; reflexivity]. *)
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Template Require Ast.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICProgram
     PCUICGuardCoFix PCUICGuardChecker.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.

Local Open Scope bs_scope.

(** The block of a quoted term, under its leading [let]s, with the number of
    [let]s: a [cofix], an abstraction [fun g : A => body] (one function), or
    [fun (f : A) (g : B) => (bf, bg)] (two functions). *)
Fixpoint block_of (n : nat) (t : term) : nat * mfixpoint term :=
  match t with
  | tLetIn _ _ _ b => block_of (S n) b
  | tCoFix m _ => (n, m)
  | tLambda na1 A1 (tLambda na2 A2 b) =>
    match decompose_app b with
    | (tConstruct _ 0 _, [_; _; b1; b2]) =>
      (n, [{| dname := na1; dtype := A1; dbody := b1; rarg := 0 |};
           {| dname := na2; dtype := A2; dbody := b2; rarg := 0 |}])
    | _ => (n, [{| dname := na1; dtype := A1; dbody := tLambda na2 A2 b; rarg := 0 |}])
    end
  | tLambda na A b => (n, [{| dname := na; dtype := A; dbody := b; rarg := 0 |}])
  | _ => (n, [])
  end.

Definition err_no_block := "test: no block in the quoted term".

(** The check on the block of a quoted program, in its local context. *)
Definition run (p : Ast.Env.program) : guard_result :=
  let Σ0 := trans_global_env p.1 in
  let Σ := trans_env_env Σ0 in
  let '(n, m) := block_of 0 (trans Σ0 p.2) in
  match m with
  | [] => Reject err_no_block
  | _ => check_guard_gen (lookup_env Σ) Σ.(retroknowledge) guard_fuel CoFix n (strip_mfix m)
  end.

CoInductive Stream := Cons : nat -> Stream -> Stream.
CoFixpoint zeros : Stream := Cons 0 zeros.
Definition mkS (n : nat) (s : Stream) : Stream := Cons n s.
Definition tlS (s : Stream) : Stream := match s with Cons _ t => t end.

(** ** Accepted: productive cofixpoints *)

MetaRocq Quote Recursively Definition q_zeros := (cofix z : Stream := Cons 0 z).
Example zeros_accepted : run q_zeros = Accept.
Proof. vm_compute. reflexivity. Qed.

(** A δ step and two β steps before the constructor; every argument is read. *)
MetaRocq Quote Recursively Definition q_twos := (cofix z : Stream := mkS 2 z).
Example twos_accepted : run q_twos = Accept.
Proof. vm_compute. reflexivity. Qed.

(** A [match] on the argument, a call in the recursive argument. *)
MetaRocq Quote Recursively Definition q_map :=
  (cofix mapS (f : nat -> nat) (s : Stream) : Stream :=
     match s with Cons n t => Cons (f n) (mapS f t) end).
Example map_accepted : run q_map = Accept.
Proof. vm_compute. reflexivity. Qed.

(** Discarded parts that mention no function of the block. *)
MetaRocq Quote Recursively Definition q_deadlet :=
  (cofix z : Stream := let dead := 1 + 1 in Cons 3 z).
Example deadlet_accepted : run q_deadlet = Accept.
Proof. vm_compute. reflexivity. Qed.
MetaRocq Quote Recursively Definition q_deadbeta :=
  (cofix z : Stream := (fun _ : nat => Cons 4 z) (2 + 2)).
Example deadbeta_accepted : run q_deadbeta = Accept.
Proof. vm_compute. reflexivity. Qed.

(** A discarded part with a guarded call: the β step drops [(fun k => g) 0]
    under the constructor, where a call is guarded. *)
MetaRocq Quote Recursively Definition q_b2 :=
  (cofix g : Stream :=
     (fun h : nat -> Stream => Cons 0 ((fun _ : Stream => zeros) (h 0))) (fun k : nat => g)).
Example b2_accepted : run q_b2 = Accept.
Proof. vm_compute. reflexivity. Qed.

(** A call to the outer block in the main function of a nested block. *)
MetaRocq Quote Recursively Definition q_nested_ok :=
  (cofix g : Stream :=
     Cons 0 (cofix f : Stream := Cons 1 g with f' : Stream := Cons 2 f' for f)).
Example nested_ok_accepted : run q_nested_ok = Accept.
Proof. vm_compute. reflexivity. Qed.

(** ** Refused: a call in a discarded part

    Each body below reduces to a guarded constructor application, and each
    reduction drops a part that holds an unguarded call. *)

(** β: the unread argument of an abstraction. *)
MetaRocq Quote Recursively Definition q_dead_beta :=
  (fun g : Stream => (fun _ : Stream => Cons 0 g) (tlS g)).
Example dead_beta_refused : run q_dead_beta = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** ζ: the value of an unread [let]. *)
MetaRocq Quote Recursively Definition q_dead_let :=
  (fun g : Stream => let dead := tlS g in Cons 0 g).
Example dead_let_refused : run q_dead_let = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** ι: a branch that the match on a known constructor does not select. *)
MetaRocq Quote Recursively Definition q_dead_match :=
  (fun g : Stream => match O with O => Cons 0 g | S _ => tlS g end).
Example dead_match_refused : run q_dead_match = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** fix: the unread argument of a fixpoint applied to a constructor. *)
MetaRocq Quote Recursively Definition q_fix :=
  (fun g : Stream =>
     (fix h (k s : nat) {struct k} : Stream := Cons 0 zeros) O (match g with Cons a _ => a end)).
Example fix_refused : run q_fix = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** ι: the unread argument of the selected constructor. *)
Inductive box := Box : nat -> box.
MetaRocq Quote Recursively Definition q_iota :=
  (fun g : Stream => match Box (match g with Cons a _ => a end) with Box _ => Cons 0 zeros end).
Example iota_refused : run q_iota = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** π: a field that the projection drops. *)
Set Primitive Projections.
Record pr := mk { fst' : nat; snd' : Stream }.
Unset Primitive Projections.
MetaRocq Quote Recursively Definition q_proj :=
  (fun g : Stream => (mk (match g with Cons a _ => a end) (Cons 0 zeros)).(snd')).
Example proj_refused : run q_proj = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** The reduct of [q_b2]: the dropped abstraction holds an unguarded call. *)
MetaRocq Quote Recursively Definition q_b2_reduct :=
  (fun g : Stream => (fun h : nat -> Stream => Cons 0 zeros) (fun k : nat => g)).
Example b2_reduct_refused : run q_b2_reduct = Reject err_unguarded.
Proof. vm_compute. reflexivity. Qed.

(** β drops [D 0 g], a value of another type [D2].  Read in [Stream]'s tree,
    [D]'s second argument would be [Cons]'s recursive position and [g] would
    pass; in [D2]'s own tree that position is not recursive.  A constructor
    of another type than the position's is refused. *)
Inductive D2 := D : nat -> Stream -> D2.
MetaRocq Quote Recursively Definition q_other_ctor :=
  (fun g : Stream => (fun _ : D2 => Cons 0 g) (D 0 g)).
Example other_ctor_refused : run q_other_ctor = Reject err_ctor_type.
Proof. vm_compute. reflexivity. Qed.

(** ** Refused: the kernel's other rules *)

(** A call that the reduction keeps, in a scrutinee. *)
MetaRocq Quote Recursively Definition q_live :=
  (fun g : Stream => (fun x : Stream => x) (tlS g)).
Example live_refused : run q_live = Reject err_casearg.
Proof. vm_compute. reflexivity. Qed.

(** A call that is not under a constructor. *)
MetaRocq Quote Recursively Definition q_unguarded := (fun g : Stream => g).
Example unguarded_refused : run q_unguarded = Reject err_unguarded.
Proof. vm_compute. reflexivity. Qed.

(** A call in a non-recursive argument of a constructor:
    [cofix f : StreamA (StreamA nat) := ConsA _ g f with g : StreamA nat := ConsA _ 0 g]. *)
CoInductive StreamA (A : Type) : Type := ConsA : A -> StreamA A -> StreamA A.
MetaRocq Quote Recursively Definition q_nonrec :=
  (fun (f : StreamA (StreamA nat)) (g : StreamA nat) => (ConsA _ g f, ConsA _ 0 g)).
Example nonrec_refused : run q_nonrec = Reject err_nonrec.
Proof. vm_compute. reflexivity. Qed.
(** A mutual twin: every call in a recursive argument. *)
MetaRocq Quote Recursively Definition q_rec :=
  (cofix f : StreamA nat := ConsA _ 0 g with g : StreamA nat := ConsA _ 1 f for f).
Example rec_accepted : run q_rec = Accept.
Proof. vm_compute. reflexivity. Qed.
(** A nested position: [TreeA] is nested in [StreamA].  The tree of [NodeA]'s
    argument is [StreamA]'s, and so is the constructor [ConsA] found there. *)
CoInductive TreeA : Type := NodeA : StreamA TreeA -> TreeA.
MetaRocq Quote Recursively Definition q_nested_pos :=
  (cofix t : TreeA := NodeA (cofix s : StreamA TreeA := ConsA _ t s)).
Example nested_pos_accepted : run q_nested_pos = Accept.
Proof. vm_compute. reflexivity. Qed.

(** A call to the outer block in the non-main function of a nested block. *)
CoInductive DRC (X Y : Type) := dcRC : X -> Y -> DRC X Y.
CoInductive CRC (A : Type) := ccRC : CRC A -> DRC (CRC A) A -> CRC A.
(* [IRC] needs no induction principle for its nesting in [CRC]. *)
Set Warnings "-register-all".
Inductive IRC : Type := icRC : CRC IRC -> IRC.
Set Warnings "register-all".
MetaRocq Quote Recursively Definition q_nonmain :=
  (fun cyc : CRC IRC =>
     (cofix f : CRC IRC := ccRC IRC f g
      with g : DRC (CRC IRC) IRC := dcRC (CRC IRC) IRC cyc (icRC cyc)
      for f)).
Example nonmain_refused : run q_nonmain = Reject err_nonmain.
Proof. vm_compute. reflexivity. Qed.

(** ** Refused: the codomain *)

CoInductive SR : Type := nextR : SR -> SR.
Inductive ER : Type := wrapR : ER -> ER.

(** rocq-prover/rocq#22386: the codomain is the outer [let] [actual], an
    inductive type.  The outer context's variables are opaque, so the codomain
    is not a coinductive type. *)
MetaRocq Quote Recursively Definition q_22386 :=
  (let actual := ER in let decoy := SR in fun recur : actual => wrapR recur).
Example cs_22386_refused : run q_22386 = Reject err_codomain.
Proof. vm_compute. reflexivity. Qed.

(** A codomain that reduces to an inductive type. *)
MetaRocq Quote Recursively Definition q_red_codomain :=
  (fun recur : (fun _ : nat => ER) O => wrapR recur).
Example red_codomain_refused : run q_red_codomain = Reject err_codomain.
Proof. vm_compute. reflexivity. Qed.

(** An outer [let] whose value is a coinductive type is opaque too: this
    productive cofixpoint is refused on purpose. *)
MetaRocq Quote Recursively Definition q_outer_let :=
  (let T := Stream in fun f : T => Cons 1 f).
Example outer_let_refused : run q_outer_let = Reject err_codomain.
Proof. vm_compute. reflexivity. Qed.
