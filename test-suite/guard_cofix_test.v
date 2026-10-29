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
    refusal.  A few shapes that Gallina cannot write (a match parameter that
    is not the scrutinee's, an index of no variable, a constant whose body has
    a free index) are made by editing a quoted block or its environment
    ([run_gen]).  The check runs directly, without the case well-formedness
    test of [check_guard_impl]: some shapes below match on a coinductive
    type with a return type that mentions the scrutinee, and the guard check
    must give its own answer on them whatever the case information says.
    Every assertion is an [Example] proved by [vm_compute; reflexivity]. *)
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Template Require Ast.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICProgram
     PCUICRecArgs PCUICGuardCoFix PCUICGuardChecker.
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

(** The check on the block of a quoted program, in its local context, with
    the declarations [extra] in front of the environment and [h] applied to
    the body of each function: [run_gen] builds the shapes that Gallina
    cannot write. *)
Definition run_gen (extra : global_declarations) (h : term -> term) (p : Ast.Env.program)
  : guard_result :=
  let Σ0 := trans_global_env p.1 in
  let Σ1 := trans_env_env Σ0 in
  let Σ := {| universes := Σ1.(universes); declarations := List.app extra Σ1.(declarations);
              retroknowledge := Σ1.(retroknowledge) |} in
  let '(n, m) := block_of 0 (trans Σ0 p.2) in
  match m with
  | [] => Reject err_no_block
  | _ => check_guard_gen (lookup_env Σ) Σ.(retroknowledge) guard_fuel CoFix n
           (strip_mfix (map (map_def (fun t => t) h) m))
  end.

Definition run (p : Ast.Env.program) : guard_result := run_gen [] (fun t => t) p.

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

(** ** Refused: the other rules of the analysis *)

Definition hdS (s : Stream) : nat := match s with Cons n _ => n end.

(** A corecursive call with a corecursive call in its arguments. *)
MetaRocq Quote Recursively Definition q_nested :=
  (fun g : nat -> Stream => Cons 0 (g (hdS (g 0)))).
Example nested_refused : run q_nested = Reject err_nested.
Proof. vm_compute. reflexivity. Qed.

(** A corecursive call in the type of an abstraction.  The type
    [(fun _ => nat) g] is convertible to [nat]. *)
MetaRocq Quote Recursively Definition q_typeabs :=
  (fun g : nat -> Stream => fun n : (fun _ : nat -> Stream => nat) g => Cons n (g n)).
Example typeabs_refused : run q_typeabs = Reject err_typeabs.
Proof. vm_compute. reflexivity. Qed.

(** A corecursive call in the type of a nested cofixpoint. *)
MetaRocq Quote Recursively Definition q_typedef :=
  (fun g : Stream => Cons 0 (cofix h : (fun _ : Stream => Stream) g := Cons 1 h)).
Example typedef_refused : run q_typedef = Reject err_typedef.
Proof. vm_compute. reflexivity. Qed.

(** A projection of a function of the block is stuck, so it is not in
    guarded form, even at a guarded position. *)
Set Primitive Projections.
CoInductive R : Type := mkR { hdR : nat; tlR : R }.
Unset Primitive Projections.
MetaRocq Quote Recursively Definition q_proj_self := (fun g : R => mkR 0 (tlR g)).
Example proj_self_refused : run q_proj_self = Reject err_notguarded.
Proof. vm_compute. reflexivity. Qed.

(** The tree-label check at a guarded position: under [Cons], β drops
    [D 0 g].  Read in [Stream]'s tree it would pass, as [g] is guarded there. *)
MetaRocq Quote Recursively Definition q_other_ctor_guarded :=
  (fun g : Stream => Cons 0 ((fun _ : D2 => g) (D 0 g))).
Example other_ctor_guarded_refused : run q_other_ctor_guarded = Reject err_ctor_type.
Proof. vm_compute. reflexivity. Qed.

(** ** The parameters of a constructor and of a match *)

(** A call in a parameter of a constructor, which the kernel does not look
    at.  [(fun _ => 0) g] is convertible to [0], so the term is typed. *)
CoInductive SN (n : nat) : Type := consN : SN n -> SN n.
MetaRocq Quote Recursively Definition q_ctor_param :=
  (fun g : SN 0 => consN ((fun _ : SN 0 => 0) g) g).
Example ctor_param_refused : run q_ctor_param = Reject err_nonrec.
Proof. vm_compute. reflexivity. Qed.
MetaRocq Quote Recursively Definition q_ctor_param_ok := (cofix g : SN 0 := consN 0 g).
Example ctor_param_ok_accepted : run q_ctor_param_ok = Accept.
Proof. vm_compute. reflexivity. Qed.

(** A match whose scrutinee is the outer, opaque [b].  As quoted it is
    accepted; with [g] put in place of its parameter, it is refused.  Gallina
    cannot write that match: its parameters are those of the scrutinee's
    type. *)
Inductive Bn (n : nat) : Type := bTn : Bn n | bFn : Bn n.
MetaRocq Quote Recursively Definition q_case_param :=
  (let b := bTn 0 in
   fun g : Stream => match b with bTn => Cons 0 g | bFn => Cons 1 g end).
Example case_param_ok_accepted : run q_case_param = Accept.
Proof. vm_compute. reflexivity. Qed.
Definition params_to_g (t : term) : term :=
  match t with
  | tCase ci p c brs =>
    tCase ci {| pparams := [tRel 0]; puinst := p.(puinst); pcontext := p.(pcontext);
                preturn := p.(preturn) |} c brs
  | _ => t
  end.
Example case_param_refused : run_gen [] params_to_g q_case_param = Reject err_casepred.
Proof. vm_compute. reflexivity. Qed.

(** A call in the return clause of a match: the return clause [Stream] of
    [q_case_param] made [(fun _ : Stream => Stream) g] (elaboration would
    reduce that redex away).  Under the return clause's binder, [g] is
    [tRel 1]. *)
Definition return_to_g (t : term) : term :=
  match t with
  | tCase ci p c brs =>
    tCase ci {| pparams := p.(pparams); puinst := p.(puinst); pcontext := p.(pcontext);
                preturn := tApp (tLambda {| binder_name := nAnon; binder_relevance := Relevant |}
                                   p.(preturn) p.(preturn)) (tRel 1) |} c brs
  | _ => t
  end.
Example case_ret_refused : run_gen [] return_to_g q_case_param = Reject err_casepred.
Proof. vm_compute. reflexivity. Qed.

(** A call in an argument of a match that returns a function. *)
MetaRocq Quote Recursively Definition q_casefun :=
  (let b := bTn 0 in
   fun g : Stream =>
     Cons 0 ((match b return Stream -> Stream with bTn => fun s => s | bFn => fun s => s end) g)).
Example casefun_refused : run q_casefun = Reject err_casefun.
Proof. vm_compute. reflexivity. Qed.

(** A return clause that depends on the scrutinee and whose codomain is not
    an inductive type. *)
MetaRocq Quote Recursively Definition q_retpred :=
  (let b := bTn 0 in
   fun g : Stream =>
     match b as x return match x with bTn => Stream | bFn => Stream end with
     | bTn => Cons 0 g
     | bFn => Cons 1 g
     end).
Example retpred_refused : run q_retpred = Reject err_retpred.
Proof. vm_compute. reflexivity. Qed.

(** A return clause that depends on the scrutinee through a parameter of the
    coinductive: the tree of the branches is the kernel's approximation
    ([has_constant_parameters] fails, so [get_recargs_approx] and
    [inter_wf_paths] run). *)
CoInductive SPm (A : Type) : Type := consPm : A -> SPm A -> SPm A.
MetaRocq Quote Recursively Definition q_dep_ret :=
  (let b := true in
   cofix g : SPm nat :=
     match b as x return SPm (if x then nat else nat) with
     | true => consPm _ 0 g
     | false => consPm _ 1 g
     end).
Example dep_ret_accepted : run q_dep_ret = Accept.
Proof. vm_compute. reflexivity. Qed.
(** That match does take the approximation: in its return clause, the
    parameter of [SPm] mentions the scrutinee, so [has_constant_parameters]
    answers [false]. *)
Definition dep_ret_params_constant : option bool :=
  let Σ0 := trans_global_env q_dep_ret.1 in
  let Σ := trans_env_env Σ0 in
  let lk := lookup_env Σ in
  let rk := Σ.(retroknowledge) in
  match block_of 0 (trans Σ0 q_dep_ret.2) with
  | (_, [d]) =>
    match strip d.(dbody) with
    | tCase _ p _ _ =>
      let pexp := it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn) in
      match whd_decompose_lambda lk rk guard_fuel pexp with
      | RtOk (nabs, ar) =>
        match whd_decompose_prod lk rk guard_fuel ar with
        | RtOk (nprods, s) =>
          match decompose_app s with
          | (tInd ind _, args) =>
            match has_constant_parameters (whd_red lk rk guard_fuel) lk rk guard_fuel []
                    nabs nprods ind args with
            | RtOk (c, _) => Some c
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end.
Example dep_ret_takes_approximation : dep_ret_params_constant = Some false.
Proof. vm_compute. reflexivity. Qed.

(** ** An index outside the block's context *)

(** In the body: [g] replaced by an index of no variable. *)
MetaRocq Quote Recursively Definition q_scope := (fun g : Stream => Cons 0 g).
Example scope_ok_accepted : run q_scope = Accept.
Proof. vm_compute. reflexivity. Qed.
Definition last_arg_free (t : term) : term :=
  match t with tApp f _ => tApp f (tRel 3) | _ => t end.
Example scope_refused : run_gen [] last_arg_free q_scope = Reject PCUICGuardCoFix.err_scope.
Proof. vm_compute. reflexivity. Qed.

(** In a reduct: the environment gives [c_bad] a body with a free index, so
    unfolding it at a guarded position gives an index of no variable.  With
    its real body, the block is accepted. *)
Definition c_bad (s : Stream) : Stream := s.
MetaRocq Quote Definition q_c_bad := c_bad.
Definition kn_c_bad : kername :=
  match q_c_bad with Ast.tConst kn _ => kn | _ => (MPfile [], "") end.
Definition c_bad_free : global_decl :=
  ConstantDecl
    {| cst_type := tSort Sort.type0;
       cst_body := Some (tLambda {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tSort Sort.type0) (tRel 5));
       cst_universes := Monomorphic_ctx;
       cst_relevance := Relevant |}.
MetaRocq Quote Recursively Definition q_scope_env := (fun g : Stream => Cons 0 (c_bad g)).
Example scope_env_ok_accepted : run q_scope_env = Accept.
Proof. vm_compute. reflexivity. Qed.
Example scope_env_refused :
  run_gen [(kn_c_bad, c_bad_free)] (fun t => t) q_scope_env = Reject PCUICGuardCoFix.err_scope.
Proof. vm_compute. reflexivity. Qed.

(** ** The discarded functions of an unfolded block

    When an unfolded body names no function of its block, the other
    functions are discarded and analysed as if kept. *)

(** A cofixpoint in a projection, then in a scrutinee: the block has one
    function, only its type is discarded, and the call [g] is guarded. *)
MetaRocq Quote Recursively Definition q_cofix_proj_ok :=
  (cofix g : R := mkR 0 (tlR (cofix h : R := mkR 1 g))).
Example cofix_proj_ok_accepted : run q_cofix_proj_ok = Accept.
Proof. vm_compute. reflexivity. Qed.
MetaRocq Quote Recursively Definition q_cofix_case_ok :=
  (cofix g : Stream := Cons 0 (match (cofix h : Stream := Cons 1 g) with Cons _ t => t end)).
Example cofix_case_ok_accepted : run q_cofix_case_ok = Accept.
Proof. vm_compute. reflexivity. Qed.

(** Unfolding [h] discards [tCoFix mfix 1], a nested cofixpoint whose main
    function is [h'] and whose non-main function [h] names [g].  The kernel
    accepts this productive body; the port refuses it. *)
MetaRocq Quote Recursively Definition q_cofix_drop :=
  (fun g : R => mkR 0 (tlR (cofix h : R := mkR 1 g with h' : R := mkR 2 h' for h))).
Example cofix_drop_refused : run q_cofix_drop = Reject err_nonmain.
Proof. vm_compute. reflexivity. Qed.

(** Unfolding [a] discards [tFix mfix 1], a stuck fixpoint that names [g].
    The kernel accepts this productive body; the port refuses it. *)
MetaRocq Quote Recursively Definition q_fix_drop :=
  (fun g : R =>
     mkR 0 ((fix a (n : nat) : R := g
             with b (n : nat) : R := match n with O => g | S m => mkR n (a m) end
             for a) 0)).
Example fix_drop_refused : run q_fix_drop = Reject err_notguarded.
Proof. vm_compute. reflexivity. Qed.

(** ** Mutual blocks *)

(** Functions with codomains of different inductives, each checked in its own
    tree.  In [StreamA]'s own tree the first argument of [ConsA] is not
    recursive, so [h] there is refused. *)
MetaRocq Quote Recursively Definition q_mixed :=
  (cofix f : Stream := Cons 0 f with h : StreamA nat := ConsA _ 0 h for f).
Example mixed_accepted : run q_mixed = Accept.
Proof. vm_compute. reflexivity. Qed.
MetaRocq Quote Recursively Definition q_mixed_nonrec :=
  (fun (f : StreamA Stream) (h : Stream) => (ConsA _ h f, Cons 0 h)).
Example mixed_nonrec_refused : run q_mixed_nonrec = Reject err_nonrec.
Proof. vm_compute. reflexivity. Qed.

(** A mutual coinductive: the functions call each other through the second
    inductive of the block.  With a constructor of [EvS] as the body of the
    function of type [OdS], the tree label differs. *)
CoInductive EvS : Type := consE : nat -> OdS -> EvS
with OdS : Type := consO : nat -> EvS -> OdS.
MetaRocq Quote Recursively Definition q_evod :=
  (cofix e : EvS := consE 0 o with o : OdS := consO 1 e for e).
Example evod_accepted : run q_evod = Accept.
Proof. vm_compute. reflexivity. Qed.
MetaRocq Quote Recursively Definition q_evod_label :=
  (fun (e : EvS) (o : OdS) => (consE 0 o, consE 1 o)).
Example evod_label_refused : run q_evod_label = Reject err_ctor_type.
Proof. vm_compute. reflexivity. Qed.

(** ** Accepted where the kernel refuses: opaque constants unfold

    PCUIC has no opacity, so [idS], closed by [Qed], unfolds; the kernel
    keeps it opaque and refuses [cofix f : Stream := Cons 0 (idS f)]. *)
Lemma idS : Stream -> Stream.
Proof. exact (fun s => s). Qed.
MetaRocq Quote Recursively Definition q_qed := (fun f : Stream => Cons 0 (idS f)).
Example qed_accepted : run q_qed = Accept.
Proof. vm_compute. reflexivity. Qed.
