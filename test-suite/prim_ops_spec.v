(* Distributed under the terms of the MIT license. *)
(** Negative controls for the reduction of primitive operations.

    [prim_ops.v] runs the verified checker on definitions Rocq's kernel accepts.
    This file runs it on environments Rocq's kernel cannot build: an operation
    registered twice on one constant, an operation registered on a constant that
    has a body, an operation whose declared type is not the type the operation
    has, a [retro_bool] that is not packet 0 of a two-constructor block named
    [true] then [false], a [retro_bool] that is declared nowhere or not
    registered at all, two primitive type constants that are the same kername,
    and an operation table whose entries are swapped.  Each must be refused.

    The environments are built by patching a quoted program, as [arity_delta.v]'s
    Part B does, and the checker runs inside Rocq by [vm_compute].  Each control
    names the declaration the refusal came from, not merely that there was one.
    That matters: an environment the checker does not yet inspect is refused
    anyway as soon as the program contains a statement that needs an operation
    to reduce, so a control that only asked for a refusal would hold for the
    wrong reason.  Each subject therefore has a program of its own, in which it
    is the only statement that can fail, and the environment controls run on
    [po_env_prog], which computes nothing at all.

    The operation table is a table: which operation a constant denotes is read
    from it, not from the constant's name.  The two swap controls check exactly
    that, by moving one entry and requiring the statement that was accepted to
    be refused.  Each is read together with its unswapped twin.

    [po_rev.b] is a two-constructor block whose constructors are named [false]
    and [true] in that order.  It is the separator for the orientation of the
    boolean readback, which is positional: constructor 0 is [true].  The
    [comparison] readback of the second slice has the same risk at three
    constructors; the controls for it are not in this file, which is written
    against the first slice's operation set.

    The last part is about weak-head normal forms.  One constructor covers a
    saturated application whose argument is a weak-head normal form that is
    neither neutral nor a literal.  No Rocq definition produces such a term,
    because such an argument is ill-typed, so that constructor is exercised by a
    unit lemma over a hand-written environment. *)

From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import config Kernames Primitive PrimitiveOps.
From MetaRocq.Template Require Import All Loader.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICSN PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateChecker.
From Corelib Require Import PrimInt63 PrimString.

(** * The subjects

    Written in [uint63_scope], which is closed again before the harness, so that
    every later numeral is the natural number it looks like. *)

Local Open Scope uint63_scope.

(** The statement whose operation the first swap control moves: [ltb 2 2] is
    [false], and under [Int63le] it would be [true]. *)
Definition po_ltb_equal : PrimInt63.ltb 2 2 = false := eq_refl.

(** The same for the two shifts: [lsl 1 1] is [2], and [lsr 1 1] is [0]. *)
Definition po_lsl_shifts : PrimInt63.eqb (PrimInt63.lsl 1 1) 2 = true := eq_refl.

(** An unsaturated application, convertible to itself and to nothing else.
    Its statement is doctored into [eqb 1 = eqb 2] below. *)
Definition po_unsat : PrimInt63.eqb 1 = PrimInt63.eqb 1 := eq_refl.

(** A saturated application one of whose arguments is a beta redex: the argument
    is neither neutral nor a literal, so no weak-head normal form constructor
    may cover the application, and the machine must reduce the argument before
    the operation fires.  Its statement is doctored into [= true] below, which
    the operation refutes. *)
Definition po_beta_arg : PrimInt63.eqb ((fun x : PrimInt63.int => x) 1) 2 = false
  := eq_refl.

(** A constant with a body, of the type an operation would have.  It is
    registered as an operation by one control, and named as [retro_int63] by
    another, where it satisfies neither [cst_body = None] nor
    [primitive_invariants]. *)
Definition po_defined : PrimInt63.int -> PrimInt63.int -> bool := PrimInt63.eqb.

(** Terms put into a doctored declaration or into the main term. *)
Definition po_ltb_true_ty : Ast.term := <% PrimInt63.ltb 2 2 = true %>.
Definition po_unsat_bad_ty : Ast.term := <% PrimInt63.eqb 1 = PrimInt63.eqb 2 %>.
Definition po_beta_true_ty : Ast.term :=
  <% PrimInt63.eqb ((fun x : PrimInt63.int => x) 1) 2 = true %>.
Definition po_int_int_int : Ast.term :=
  <% PrimInt63.int -> PrimInt63.int -> PrimInt63.int %>.
(** The wrong-tag saturated application of the [retro_int63 = retro_string]
    control: well typed in that environment, and no operation can fire on it. *)
Definition po_wrong_tag : Ast.term :=
  Ast.tApp <% PrimInt63.eqb %> [Ast.tString "a"%pstring; Ast.tInt 1].

Local Close Scope uint63_scope.
Local Open Scope bs_scope.

(** * The inductives the [retro_bool] controls register *)

(** Packet 1 of a two-packet block, with two constructors, one of which takes an
    argument.  Registering it reaches the condition only through the index. *)
Inductive po_mutA : Prop := po_mkA : po_mutB -> po_mutA
with po_mutB : Prop := po_mkB0 : po_mutB | po_mkB1 : po_mutA -> po_mutB.

(** Two nullary constructors, named neither [true] nor [false]. *)
Inductive po_twob : Set := po_yes | po_no.

(** Two nullary constructors named [false] and [true] in that order: the
    readback is positional, so this block is the orientation separator. *)
Module po_rev.
  Inductive b : Set := false | true.
End po_rev.

(** * The quoted programs

    One per subject, so that in each program exactly one declaration can fail
    and the refusal's declaration identifies the branch that refused it. *)

(** Computes nothing, so it is accepted before and after the operations reduce.
    Every environment control patches this one, and so observes the environment
    condition alone.  Its binders bring in the four blocks and the string type
    the controls need. *)
Definition po_env_witness
    (a : po_mutA) (b : po_mutB) (c : po_twob) (d : po_rev.b) (e : comparison)
    (s : PrimString.string) (x : PrimInt63.int) : bool :=
  andb (PrimInt63.eqb x x) (po_defined x x).

MetaRocq Quote Recursively Definition po_env_prog := po_env_witness.
MetaRocq Quote Recursively Definition po_ltb_prog := po_ltb_equal.
MetaRocq Quote Recursively Definition po_lsl_prog := po_lsl_shifts.
MetaRocq Quote Recursively Definition po_unsat_prog := po_unsat.
MetaRocq Quote Recursively Definition po_beta_prog := po_beta_arg.

(** * Patching *)

Definition po_nokn : kername := (MPfile ["po_nothing"], "po_nothing").

Definition po_cst_kn (t : Ast.term) : kername :=
  match t with Ast.tConst kn _ => kn | _ => po_nokn end.

Definition po_ind_of (t : Ast.term) : inductive :=
  match t with
  | Ast.tInd ind _ => ind
  | _ => {| inductive_mind := po_nokn; inductive_ind := 0 |}
  end.

Definition po_eqb_kn : kername := Eval vm_compute in po_cst_kn <% PrimInt63.eqb %>.
Definition po_ltb_kn : kername := Eval vm_compute in po_cst_kn <% PrimInt63.ltb %>.
Definition po_lsl_kn : kername := Eval vm_compute in po_cst_kn <% PrimInt63.lsl %>.
Definition po_int_kn : kername := Eval vm_compute in po_cst_kn <% PrimInt63.int %>.
Definition po_defined_kn : kername := Eval vm_compute in po_cst_kn <% po_defined %>.
Definition po_ltb_equal_kn : kername := Eval vm_compute in po_cst_kn <% po_ltb_equal %>.
Definition po_lsl_shifts_kn : kername := Eval vm_compute in po_cst_kn <% po_lsl_shifts %>.
Definition po_unsat_kn : kername := Eval vm_compute in po_cst_kn <% po_unsat %>.
Definition po_beta_arg_kn : kername := Eval vm_compute in po_cst_kn <% po_beta_arg %>.

Definition po_cmp_ind : inductive := Eval vm_compute in po_ind_of <% comparison %>.
Definition po_mut_ind : inductive := Eval vm_compute in po_ind_of <% po_mutA %>.
(* [po_twobI], not [po_twob_ind]: the latter is po_twob's induction scheme. *)
Definition po_twobI : inductive := Eval vm_compute in po_ind_of <% po_twob %>.
Definition po_rev_ind : inductive := Eval vm_compute in po_ind_of <% po_rev.b %>.

(** Packet 1 of [po_mutA]'s block. *)
Definition po_mut1_ind : inductive :=
  {| inductive_mind := po_mut_ind.(inductive_mind); inductive_ind := 1 |}.

(** A kername that is declared nowhere. *)
Definition po_absent_ind : inductive :=
  {| inductive_mind := (MPfile ["po_absent"], "po_undeclared"); inductive_ind := 0 |}.

(** Every name above was found: a [po_nothing] here would make a control pass by
    patching nothing. *)
Definition po_names_found_ok : bool := Eval vm_compute in
  forallb (fun kn => negb (eqb kn po_nokn))
    [po_eqb_kn; po_ltb_kn; po_lsl_kn; po_int_kn; po_defined_kn;
     po_ltb_equal_kn; po_lsl_shifts_kn; po_unsat_kn; po_beta_arg_kn;
     po_cmp_ind.(inductive_mind); po_mut_ind.(inductive_mind);
     po_twobI.(inductive_mind); po_rev_ind.(inductive_mind)].
Print po_names_found_ok.
Definition po_names_found_holds : po_names_found_ok = true := eq_refl.

(** ** Retroknowledge *)

Definition po_set_int63 (k : option kername) (r : Retroknowledge.t) : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := k;
     Retroknowledge.retro_float64 := r.(Retroknowledge.retro_float64);
     Retroknowledge.retro_string := r.(Retroknowledge.retro_string);
     Retroknowledge.retro_array := r.(Retroknowledge.retro_array);
     Retroknowledge.retro_ops := r.(Retroknowledge.retro_ops);
     Retroknowledge.retro_bool := r.(Retroknowledge.retro_bool) |}.

Definition po_set_string (k : option kername) (r : Retroknowledge.t) : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := r.(Retroknowledge.retro_int63);
     Retroknowledge.retro_float64 := r.(Retroknowledge.retro_float64);
     Retroknowledge.retro_string := k;
     Retroknowledge.retro_array := r.(Retroknowledge.retro_array);
     Retroknowledge.retro_ops := r.(Retroknowledge.retro_ops);
     Retroknowledge.retro_bool := r.(Retroknowledge.retro_bool) |}.

Definition po_set_ops (ops : list (kername × prim_op)) (r : Retroknowledge.t)
    : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := r.(Retroknowledge.retro_int63);
     Retroknowledge.retro_float64 := r.(Retroknowledge.retro_float64);
     Retroknowledge.retro_string := r.(Retroknowledge.retro_string);
     Retroknowledge.retro_array := r.(Retroknowledge.retro_array);
     Retroknowledge.retro_ops := ops;
     Retroknowledge.retro_bool := r.(Retroknowledge.retro_bool) |}.

Definition po_set_bool (i : option inductive) (r : Retroknowledge.t) : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := r.(Retroknowledge.retro_int63);
     Retroknowledge.retro_float64 := r.(Retroknowledge.retro_float64);
     Retroknowledge.retro_string := r.(Retroknowledge.retro_string);
     Retroknowledge.retro_array := r.(Retroknowledge.retro_array);
     Retroknowledge.retro_ops := r.(Retroknowledge.retro_ops);
     Retroknowledge.retro_bool := i |}.

Definition po_add_op (c : kername) (op : prim_op) (r : Retroknowledge.t)
    : Retroknowledge.t :=
  po_set_ops ((c, op) :: r.(Retroknowledge.retro_ops)) r.

(** Move one entry of the table to another operation, keeping its kername. *)
Definition po_swap_op (c : kername) (op : prim_op) (r : Retroknowledge.t)
    : Retroknowledge.t :=
  po_set_ops (map (fun e => if eqb e.1 c then (e.1, op) else e)
                  r.(Retroknowledge.retro_ops)) r.

Definition po_retro (f : Retroknowledge.t -> Retroknowledge.t) (p : Ast.Env.program)
    : Ast.Env.program :=
  ({| Ast.Env.universes := p.1.(Ast.Env.universes);
      Ast.Env.declarations := p.1.(Ast.Env.declarations);
      Ast.Env.retroknowledge := f p.1.(Ast.Env.retroknowledge) |}, p.2).

(** ** Declarations and the main term *)

Definition po_with_type (ty : Ast.term) (cb : Ast.Env.constant_body)
    : Ast.Env.constant_body :=
  {| Ast.Env.cst_type := ty;
     Ast.Env.cst_body := cb.(Ast.Env.cst_body);
     Ast.Env.cst_universes := cb.(Ast.Env.cst_universes);
     Ast.Env.cst_relevance := cb.(Ast.Env.cst_relevance) |}.

Definition po_patch_cst (kn : kername) (f : Ast.Env.constant_body -> Ast.Env.constant_body)
    (d : kername × Ast.Env.global_decl) : kername × Ast.Env.global_decl :=
  match d.2 with
  | Ast.Env.ConstantDecl cb =>
      if eqb d.1 kn then (d.1, Ast.Env.ConstantDecl (f cb)) else d
  | _ => d
  end.

Definition po_decl (kn : kername) (f : Ast.Env.constant_body -> Ast.Env.constant_body)
    (p : Ast.Env.program) : Ast.Env.program :=
  ({| Ast.Env.universes := p.1.(Ast.Env.universes);
      Ast.Env.declarations := map (po_patch_cst kn f) p.1.(Ast.Env.declarations);
      Ast.Env.retroknowledge := p.1.(Ast.Env.retroknowledge) |}, p.2).

Definition po_main (t : Ast.term) (p : Ast.Env.program) : Ast.Env.program := (p.1, t).

(** * The driver

    [nor] is an explicit parameter so that instance resolution finds it, as in
    [test-suite/reduction_test.v] and [test-suite/arity_delta.v]. *)

#[local] Existing Instance real_guard_impl.
#[local,program] Instance po_assume_normalization {nor}
  : @PCUICSN.Normalization default_checker_flags nor.
Next Obligation. todo "the row-P controls run infer under this test-only assumption". Qed.
#[local] Existing Instance PCUICSN.normalization.

Definition po_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined.

Definition po_run (nor : normalizing_flags) (p : Ast.Env.program) : string + string :=
  infer_and_print_template_program (cf := default_checker_flags) p Monomorphic_ctx.

Definition po_rejected (r : string + string) : bool :=
  match r with inl _ => false | inr _ => true end.

Definition po_error_contains (needle : string) (r : string + string) : bool :=
  match r with
  | inl _ => false
  | inr msg => match String.index 0 needle msg with Some _ => true | None => false end
  end.

(** [infer_and_print_template_program] closes every refusal with
    ", while checking <id>", the last text in the message: [toplevel] for the
    conditions [check_univs] tests on the retroknowledge alone, "toplevel term"
    for the inference of the program's own term, and [string_of_kername kn] for
    a condition on the declaration [kn]. *)
Definition po_refused_at (id : string) (r : string + string) : bool :=
  po_error_contains (", while checking " ^ id) r.

(** "toplevel" is a prefix of "toplevel term", so the retroknowledge-only
    conditions need the longer id ruled out. *)
Definition po_refused_at_toplevel (r : string + string) : bool :=
  po_refused_at "toplevel" r && negb (po_refused_at "toplevel term" r).

Definition po_not_convertible := "Types are not convertible".

Definition po_id_eqb : string := Eval vm_compute in string_of_kername po_eqb_kn.
Definition po_id_defined : string := Eval vm_compute in string_of_kername po_defined_kn.
Definition po_id_ltb_equal : string := Eval vm_compute in string_of_kername po_ltb_equal_kn.
Definition po_id_lsl_shifts : string := Eval vm_compute in string_of_kername po_lsl_shifts_kn.
Definition po_id_unsat : string := Eval vm_compute in string_of_kername po_unsat_kn.
Definition po_id_beta_arg : string := Eval vm_compute in string_of_kername po_beta_arg_kn.
Definition po_id_cmp : string :=
  Eval vm_compute in string_of_kername po_cmp_ind.(inductive_mind).
Definition po_id_twob : string :=
  Eval vm_compute in string_of_kername po_twobI.(inductive_mind).
Definition po_id_rev : string :=
  Eval vm_compute in string_of_kername po_rev_ind.(inductive_mind).

(** * The controls

    Each control is three commands.  [po_X] is the checker's answer, printed so
    that the log carries the message the refusal gave.  [po_X_ok] is that answer
    compared with what the control asks for, printed so that a run reports one
    named verdict per case even where it is not the expected one.
    [po_X_holds] is the assertion: it is what makes the test suite fail. *)

(** ** Part A — the positives

    [po_A0] is accepted before and after the operations reduce: it is the
    control on the harness itself.  [po_A1] to [po_A4] are the positive twins of
    the controls that move a table entry or a statement: each must be accepted
    once its subject's operation reduces. *)

Definition po_A0 := Eval vm_compute in po_run po_normal po_env_prog.
Print po_A0.
Definition po_A0_ok : bool := Eval vm_compute in negb (po_rejected po_A0).
Print po_A0_ok.
Definition po_A0_holds : po_A0_ok = true := eq_refl.

Definition po_A1 := Eval vm_compute in po_run po_normal po_ltb_prog.
Print po_A1.
Definition po_A1_ok : bool := Eval vm_compute in negb (po_rejected po_A1).
Print po_A1_ok.
Definition po_A1_holds : po_A1_ok = true := eq_refl.

Definition po_A2 := Eval vm_compute in po_run po_normal po_lsl_prog.
Print po_A2.
Definition po_A2_ok : bool := Eval vm_compute in negb (po_rejected po_A2).
Print po_A2_ok.
Definition po_A2_holds : po_A2_ok = true := eq_refl.

Definition po_A3 := Eval vm_compute in po_run po_normal po_unsat_prog.
Print po_A3.
Definition po_A3_ok : bool := Eval vm_compute in negb (po_rejected po_A3).
Print po_A3_ok.
Definition po_A3_holds : po_A3_ok = true := eq_refl.

Definition po_A4 := Eval vm_compute in po_run po_normal po_beta_prog.
Print po_A4.
Definition po_A4_ok : bool := Eval vm_compute in negb (po_rejected po_A4).
Print po_A4_ok.
Definition po_A4_holds : po_A4_ok = true := eq_refl.

(** ** Part B — doctored statements

    [po_B1] replaces [ltb 2 2 = false] by [ltb 2 2 = true], which the operation
    refutes.  [po_B2] replaces [eqb 1 = eqb 1] by [eqb 1 = eqb 2]: two
    unsaturated applications that cannot take a step, so conversion must answer
    no and prove it.  [po_B3] is [po_B1] for the application whose argument is a
    beta redex, so it asks the machine to reduce the argument and then refute
    the statement.  All three must be refused before and after the rule exists;
    they are the controls that must never turn. *)

Definition po_B1 := Eval vm_compute in
  po_run po_normal (po_decl po_ltb_equal_kn (po_with_type po_ltb_true_ty) po_ltb_prog).
Print po_B1.
Definition po_B1_ok : bool := Eval vm_compute in
  po_refused_at po_id_ltb_equal po_B1 && po_error_contains po_not_convertible po_B1.
Print po_B1_ok.
Definition po_B1_holds : po_B1_ok = true := eq_refl.

Definition po_B2 := Eval vm_compute in
  po_run po_normal (po_decl po_unsat_kn (po_with_type po_unsat_bad_ty) po_unsat_prog).
Print po_B2.
Definition po_B2_ok : bool := Eval vm_compute in
  po_refused_at po_id_unsat po_B2 && po_error_contains po_not_convertible po_B2.
Print po_B2_ok.
Definition po_B2_holds : po_B2_ok = true := eq_refl.

Definition po_B3 := Eval vm_compute in
  po_run po_normal (po_decl po_beta_arg_kn (po_with_type po_beta_true_ty) po_beta_prog).
Print po_B3.
Definition po_B3_ok : bool := Eval vm_compute in
  po_refused_at po_id_beta_arg po_B3 && po_error_contains po_not_convertible po_B3.
Print po_B3_ok.
Definition po_B3_holds : po_B3_ok = true := eq_refl.

(** ** Part C — the table decides, not the name

    One entry is moved to another operation of the same argument tags, and the
    statement that the twin positive accepts must then be refused.  The
    assertion on the table itself keeps a control from passing because the entry
    was not there to be moved. *)

Definition po_C1_env := Eval vm_compute in
  po_retro (po_swap_op po_ltb_kn Int63le) po_ltb_prog.
Definition po_C1_moved_ok : bool := Eval vm_compute in
  eqb (Retroknowledge.prim_op_of po_C1_env.1.(Ast.Env.retroknowledge) po_ltb_kn)
      (Some Int63le).
Print po_C1_moved_ok.
Definition po_C1_moved_holds : po_C1_moved_ok = true := eq_refl.
Definition po_C1 := Eval vm_compute in po_run po_normal po_C1_env.
Print po_C1.
Definition po_C1_ok : bool := Eval vm_compute in po_refused_at po_id_ltb_equal po_C1.
Print po_C1_ok.
Definition po_C1_holds : po_C1_ok = true := eq_refl.

Definition po_C2_env := Eval vm_compute in
  po_retro (po_swap_op po_lsl_kn Int63lsr) po_lsl_prog.
Definition po_C2_moved_ok : bool := Eval vm_compute in
  eqb (Retroknowledge.prim_op_of po_C2_env.1.(Ast.Env.retroknowledge) po_lsl_kn)
      (Some Int63lsr).
Print po_C2_moved_ok.
Definition po_C2_moved_holds : po_C2_moved_ok = true := eq_refl.
Definition po_C2 := Eval vm_compute in po_run po_normal po_C2_env.
Print po_C2.
Definition po_C2_ok : bool := Eval vm_compute in po_refused_at po_id_lsl_shifts po_C2.
Print po_C2_ok.
Definition po_C2_holds : po_C2_ok = true := eq_refl.

(** ** Part D — doctored environments

    Each of these is an environment Rocq's kernel never builds.  They run on
    [po_env_prog], which [po_A0] shows is accepted unpatched, so the refusal is
    the environment condition and nothing else. *)

(** D1: one constant carries two operations.  The table's kernames must be
    distinct, which is what makes [prim_op_of] a function. *)
Definition po_D1 := Eval vm_compute in
  po_run po_normal (po_retro (po_add_op po_eqb_kn Int63lt) po_env_prog).
Print po_D1.
Definition po_D1_ok : bool := Eval vm_compute in po_refused_at_toplevel po_D1.
Print po_D1_ok.
Definition po_D1_holds : po_D1_ok = true := eq_refl.

(** D2: an operation registered on a constant that has a body.  The rule and
    delta reduction would both apply to it. *)
Definition po_D2 := Eval vm_compute in
  po_run po_normal (po_retro (po_add_op po_defined_kn Int63eq) po_env_prog).
Print po_D2.
Definition po_D2_ok : bool := Eval vm_compute in po_refused_at po_id_defined po_D2.
Print po_D2_ok.
Definition po_D2_holds : po_D2_ok = true := eq_refl.

(** D3: the declared type of a registered operation is not the type the
    operation has. *)
Definition po_D3 := Eval vm_compute in
  po_run po_normal (po_decl po_eqb_kn (po_with_type po_int_int_int) po_env_prog).
Print po_D3.
Definition po_D3_ok : bool := Eval vm_compute in po_refused_at po_id_eqb po_D3.
Print po_D3_ok.
Definition po_D3_holds : po_D3_ok = true := eq_refl.

(** D4: [retro_bool] at packet 1 of a mutual block, whose constructors are not
    the two nullary ones the readback needs. *)
Definition po_D4 := Eval vm_compute in
  po_run po_normal (po_retro (po_set_bool (Some po_mut1_ind)) po_env_prog).
Print po_D4.
Definition po_D4_ok : bool := Eval vm_compute in po_refused_at_toplevel po_D4.
Print po_D4_ok.
Definition po_D4_holds : po_D4_ok = true := eq_refl.

(** D5: no [retro_bool] at all, while [eqb] is registered: the result of [eqb]
    has nothing to be read back to. *)
Definition po_D5 := Eval vm_compute in
  po_run po_normal (po_retro (po_set_bool None) po_env_prog).
Print po_D5.
Definition po_D5_ok : bool := Eval vm_compute in po_refused_at po_id_eqb po_D5.
Print po_D5_ok.
Definition po_D5_holds : po_D5_ok = true := eq_refl.

(** D6: [retro_int63] and [retro_string] are one kername, so one bodiless
    constant of type [Set] types both an integer and a string literal, and [eqb]
    applied to one of each is well typed and saturated while no operation can
    fire on it.  The main term is that application. *)
Definition po_D6 := Eval vm_compute in
  po_run po_normal
    (po_main po_wrong_tag (po_retro (po_set_string (Some po_int_kn)) po_env_prog)).
Print po_D6.
Definition po_D6_ok : bool := Eval vm_compute in po_refused_at_toplevel po_D6.
Print po_D6_ok.
Definition po_D6_holds : po_D6_ok = true := eq_refl.

(** D7: [retro_bool] names a kername that is declared nowhere, while
    [prim_op_type] is still a type. *)
Definition po_D7 := Eval vm_compute in
  po_run po_normal (po_retro (po_set_bool (Some po_absent_ind)) po_env_prog).
Print po_D7.
Definition po_D7_ok : bool := Eval vm_compute in po_refused_at po_id_eqb po_D7.
Print po_D7_ok.
Definition po_D7_holds : po_D7_ok = true := eq_refl.

(** D8, D9 and D10 doctor the registered block and leave the table empty, so
    that the only clause they can violate is the one on that block.  With the
    table in place, the operations' own declarations would fail first, because
    their result type would no longer be the registered inductive, and the
    refusal would name a constant rather than the block.

    D8: [retro_bool] with three constructors. *)
Definition po_D8 := Eval vm_compute in
  po_run po_normal
    (po_retro (fun r => po_set_ops [] (po_set_bool (Some po_cmp_ind) r)) po_env_prog).
Print po_D8.
Definition po_D8_ok : bool := Eval vm_compute in po_refused_at po_id_cmp po_D8.
Print po_D8_ok.
Definition po_D8_holds : po_D8_ok = true := eq_refl.

(** D9: [retro_bool] with two nullary constructors named neither [true] nor
    [false]. *)
Definition po_D9 := Eval vm_compute in
  po_run po_normal
    (po_retro (fun r => po_set_ops [] (po_set_bool (Some po_twobI) r)) po_env_prog).
Print po_D9.
Definition po_D9_ok : bool := Eval vm_compute in po_refused_at po_id_twob po_D9.
Print po_D9_ok.
Definition po_D9_holds : po_D9_ok = true := eq_refl.

(** D10: the orientation separator.  Two nullary constructors named [false] and
    [true], in that order.  The readback is positional, so an environment that
    passed here would read [eqb 7 7] back as [false]. *)
Definition po_D10 := Eval vm_compute in
  po_run po_normal
    (po_retro (fun r => po_set_ops [] (po_set_bool (Some po_rev_ind) r)) po_env_prog).
Print po_D10.
Definition po_D10_ok : bool := Eval vm_compute in po_refused_at po_id_rev po_D10.
Print po_D10_ok.
Definition po_D10_holds : po_D10_ok = true := eq_refl.

(** D11: [retro_int63] names a constant that has a body and is not of type
    [Set], so the integer tag has no declaration satisfying
    [primitive_invariants] and the reduct of an integer operation could not be
    typed. *)
Definition po_D11 := Eval vm_compute in
  po_run po_normal (po_retro (po_set_int63 (Some po_defined_kn)) po_env_prog).
Print po_D11.
Definition po_D11_ok : bool := Eval vm_compute in po_refused_at po_id_eqb po_D11.
Print po_D11_ok.
Definition po_D11_holds : po_D11_ok = true := eq_refl.

(** * Part E — weak-head normal forms

    The constructor for a saturated application whose argument is a weak-head
    normal form that is neither neutral nor a literal of the expected tag.  No
    Rocq definition produces such a term: the argument's declared type is the
    registered integer constant, which is neither a sort nor an inductive nor a
    product, so the application is ill-typed and the kernel never builds it.
    The environment is written by hand, as [arity_delta_spec.v] does, and the
    statement is a unit lemma, not a run of the checker. *)

From MetaRocq.PCUIC Require Import PCUICNormal.

Definition po_mp : modpath := MPfile ["prim_ops_spec"; "TestSuite"; "MetaRocq"].
Definition po_kn (s : ident) : kername := (po_mp, s).

(** A bodiless monomorphic constant for the integer tag, and one for the
    operation.  Neither type matters here: the weak-head constructors read the
    table and the body, never a type. *)
Definition po_bodiless : constant_body :=
  {| cst_type := tSort Sort.type0; cst_body := None;
     cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Definition po_retro_e : Retroknowledge.t :=
  {| Retroknowledge.retro_int63 := Some (po_kn "int");
     Retroknowledge.retro_float64 := None;
     Retroknowledge.retro_string := None;
     Retroknowledge.retro_array := None;
     Retroknowledge.retro_ops := [(po_kn "eq", Int63eq)];
     Retroknowledge.retro_bool := None |}.

Definition po_Sigma : global_env :=
  {| universes := ContextSet.empty;
     declarations := [(po_kn "eq", ConstantDecl po_bodiless);
                      (po_kn "int", ConstantDecl po_bodiless)];
     retroknowledge := po_retro_e |}.

(** [eq] applied to a sort and to an integer literal: saturated, the first
    argument a weak-head normal form that is not a literal, the second a
    literal.  The application is a weak-head normal form. *)
Definition po_rigid_term (u : Instance.t) (s : Sort.t) : term :=
  mkApps (tConst (po_kn "eq") u) [tSort s; tPrim (prim_int 2%uint63)].

Example po_E1_whnf u s Γ : whnf RedFlags.default po_Sigma Γ (po_rigid_term u s).
Proof.
  eapply whnf_primapp_rigid with (decl := po_bodiless) (op := Int63eq) (n := 0)
    (a := tSort s); cbn; try reflexivity.
  apply whnf_sort.
Qed.

Print Assumptions po_E1_whnf.

(** The verdict line for the run: it exists only if the lemma above closed. *)
Definition po_E1_ok : bool :=
  (fun _ : whnf RedFlags.default po_Sigma [] (po_rigid_term [] Sort.type0) => true)
    (po_E1_whnf [] Sort.type0 []).
Print po_E1_ok.
Definition po_E1_holds : po_E1_ok = true := eq_refl.
