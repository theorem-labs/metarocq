(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICCases
     PCUICClosed PCUICRecArgs PCUICGuardReduce.
From MetaRocq.PCUIC Require Export PCUICGuardResult.
From MetaRocq.PCUIC Require Import PCUICGuardCoFix.

From Stdlib Require Import ssreflect ssrbool.

Local Open Scope bs_scope.
Local Open Scope list_scope.
Set Default Goal Selector "!".

(** * The executable guard checker for PCUIC

  [check_guard_gen lookup retro fuel b n mfix] decides whether the block
  [mfix], checked in a local context of length [n], is guarded.  The context
  itself is never read: each of its variables is an opaque assumption.

  The fixpoint case is a port of the fixpoint guard checker of the Rocq
  kernel (kernel/inductive.ml: [subterm_specif], [branches_specif],
  [restrict_spec], [filter_stack_domain], [find_uniform_parameters],
  [drop_uniform_parameters], [filter_fix_stack_domain], [check_one_fix],
  [raw_prefix_escapes], [inductive_of_mutfix], [check_fix]); the recursive
  argument trees come from [PCUICRecArgs] and every reduction step from
  [head_step] in [PCUICGuardReduce].  The cofixpoint case is
  [check_cofix_block] ([PCUICGuardCoFix]).

  The port differs from the kernel's fixpoint checker in these ways.  All
  but one refuse more than the kernel, or follow PCUIC's reduction; the
  exception is the unfolding of constants (below), which can accept a block
  that the kernel refuses:

  - Every reduction the check performs is a sequence of single [head_step]
    steps: the reductions of [subterm_specif], [restrict_spec],
    [filter_stack_domain], [check_inductive_codomain], [find_inductive],
    [split_struct_arg], [check_nested_fix_body], the binder prefix of the
    block ([check_occur]) and the expansions of [check_rec_call_state].  A
    part that a step discards must carry no pending recursive call: it is
    walked at its own redex level and the block is refused if the walk
    returns a pending status, or sets one at a level where there was none.
    The match, projection and fixpoint expansions check the parts they
    discard in the same way: the return clause, the parameters, the other
    fields, and (for a fixpoint whose body names none of its functions) the
    types, binder prefixes and other bodies.  For that, each branch of a
    match, each body of a nested fixpoint, the nested fixpoint's types and
    its binder prefixes have their own redex level.  An argument of a
    β-redex that goes into an unused binder, a dropped [let] value, a
    λ-domain, a [let] type and the stack of a product, sort or primitive
    must carry no pending status either.  The selected branch of a match
    stays a β-redex applied to the constructor arguments, so an argument
    that the branch does not use is a dropped β-argument.
    Inside a specification computation ([subterm_specif] and the functions
    it calls) there is no redex stack, so a discarded part there must carry
    no pending status at any level.  A discarded part in which no function
    of the block occurs carries no status and is not walked.
  - Every occurrence of a function of the block in the block's own binder
    prefix, before the recursive argument, is refused, the type of a [let]
    included; the prefix is reduced one step at a time and a step that
    discards a part mentioning the block is refused.
  - A variable of the outer context is an opaque assumption with no
    subterm information; an index beyond the outer context is refused.
  - Each kernel anomaly or assertion, and each name [lookup] does not know,
    is a refusal.  Existential and named variables are refused.
  - **Accepts more:** constants with a body unfold, including proofs closed
    by [Qed], which the quoting keeps as bodies (PCUIC has no opacity).
    The kernel never unfolds an opaque constant, so a fixpoint whose call
    is guarded only through such a body, for example
    [fix f n := c (fun z => f z) n] with [c] a [Qed] constant that applies
    its function argument to a subterm, is accepted here and refused by
    the kernel.
  - A match on a coinductive ([CoFinite]) type gives no subterm in its
    branches, and a projection out of a coinductive ([CoFinite]) record
    gives no subterm, whatever the scrutinee or the projected term is.
  - A relevant fixpoint is refused on an inductive whose sort is [SProp]
    ([is_allowed_fixpoint]); PCUIC always checks eliminations, so the
    kernel's [ind_ignores_elim_constraints] is false here.  It is also
    refused when the inductive's [ind_kelim] is [IntoSProp].
  - A match keeps its parameters only in the instantiated contexts of the
    return clause and branches, as the kernel's expanded match does; the
    contexts are those of the term ([inst_case_branch_context]), which is
    what ι-reduction reads.
  - The approximate recursive-argument trees ([get_recargs_approx],
    [has_constant_parameters]) reduce types with every variable opaque, and
    the parts those reductions discard are not walked: such a reduction only
    narrows a tree and never replaces a part of the term being checked.
  - PCUIC has no primitive operations, so [primitive_specif] gives no
    subterm.
  - Recursion is bounded by doubling fuel: a fuel of [k] allows [2 ^ k]
    nested steps.  Exhaustion is [OutOfFuel], which is never caught and
    never turned into [Reject]. *)

(** The fixpoint checker lives in its own module, so that its many short
    names do not reach the files that import this one. *)
Module FixGuard.

(** ** Data of the check *)

Inductive size := Large | Strict.

Definition size_glb (s1 s2 : size) : size :=
  match s1, s2 with Strict, Strict => Strict | _, _ => Large end.

(** Sets of redex levels, as sorted lists. *)
Fixpoint iset_add (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: l' => if Nat.ltb x y then x :: l else if Nat.eqb x y then l else y :: iset_add x l'
  end.

Definition iset_union (l1 l2 : list nat) : list nat :=
  fold_left (fun acc x => iset_add x acc) l1 l2.

Inductive subterm_spec :=
| Subterm (internal : list nat) (s : size) (t : wf_paths)
| Dead_code
| Not_subterm
| Internally_bound_subterm (l : list nat).

(** A deferred specification: a value, or a slot of the memo table. *)
Inductive lspec := LVal (s : subterm_spec) | LSlot (id : positive).

Inductive fix_check_result := NeedReduce (msg : string) | NoNeedReduce.

Definition orfcr (x y : fix_check_result) : fix_check_result :=
  match x with NeedReduce _ => x | NoNeedReduce => y end.

Definition is_need (x : fix_check_result) : bool :=
  match x with NeedReduce _ => true | NoNeedReduce => false end.

Definition or_list (l : list fix_check_result) : fix_check_result :=
  fold_right orfcr NoNeedReduce l.

(** The guard environment: the [let] bodies of the variables bound since the
    root of the check (innermost first), their number, the index of the last
    function of the block ([rel_min], from 0) and the specifications. *)
Record renv := mk_renv {
  r_lets : list (option term);
  r_depth : nat;
  r_min : nat;
  r_genv : list lspec }.

Inductive stack_element :=
| SClosure (st : fix_check_result) (r : renv) (k : nat) (c : term)
| SArg (s : lspec).

(** What a slot of the memo table computes. *)
Inductive thunk :=
| TSub (r : renv) (stack : list stack_element) (t : term)
  (** [lazy_subterm_specif] *)
| TIota (nr : nat) (s : lspec)
  (** [set_iota_specif] *)
| TBranch (cs : lspec) (ind : inductive) (i nca j : nat)
  (** argument [j] of constructor [i] in [branches_specif] *)
| TFilter (s : lspec) (ind : inductive) (args : list term)
  (** the restricted specification of [filter_stack_domain] *).

Inductive slot := SPending (th : thunk) | SForcing | SDone (s : subterm_spec).

(** A binary trie indexed by [positive]. *)
Inductive ptrie (A : Type) := PEmpty | PNode (l : ptrie A) (o : option A) (r : ptrie A).
Arguments PEmpty {A}.
Arguments PNode {A} l o r.

Fixpoint pget {A} (p : positive) (t : ptrie A) : option A :=
  match t with
  | PEmpty => None
  | PNode l o r => match p with xH => o | xO p => pget p l | xI p => pget p r end
  end.

Fixpoint pset {A} (p : positive) (x : A) (t : ptrie A) : ptrie A :=
  match t with
  | PEmpty =>
    match p with
    | xH => PNode PEmpty (Some x) PEmpty
    | xO p => PNode (pset p x PEmpty) None PEmpty
    | xI p => PNode PEmpty None (pset p x PEmpty)
    end
  | PNode l o r =>
    match p with
    | xH => PNode l (Some x) r
    | xO p => PNode (pset p x l) o r
    | xI p => PNode l o (pset p x r)
    end
  end.

(** ** The monad: the memo table of deferred specifications and the memo of
    recursive-argument trees; a refusal or an exhaustion ends the check. *)

Record gstate := mk_gstate {
  gs_slots : ptrie slot;
  gs_next : positive;
  gs_memo : recargs_memo }.

Inductive gres (X : Type) := GOk (x : X) (s : gstate) | GReject (msg : string) | GFuel.
Arguments GOk {X} x s.
Arguments GReject {X} msg.
Arguments GFuel {X}.

Definition M (X : Type) : Type := gstate -> gres X.

Definition ret {X} (x : X) : M X := fun s => GOk x s.
Definition gbind {X Y} (m : M X) (f : X -> M Y) : M Y :=
  fun s => match m s with GOk x s' => f x s' | GReject msg => GReject msg | GFuel => GFuel end.
Definition reject {X} (msg : string) : M X := fun _ => GReject msg.
Definition mfuel {X} : M X := fun _ => GFuel.

Local Notation "x <- m ;; f" := (gbind m (fun x => f))
  (at level 100, m at next level, right associativity).

Definition of_rt {X} (a : rt_answer X) : M X :=
  match a with RtOk x => ret x | RtBad msg => reject msg | RtFuel => mfuel end.

Definition of_option {X} (msg : string) (o : option X) : M X :=
  match o with Some x => ret x | None => reject msg end.

Definition with_memo {X} (f : recargs_memo -> rt_answer (X * recargs_memo)) : M X :=
  fun s =>
    match f s.(gs_memo) with
    | RtOk (x, m) => GOk x {| gs_slots := s.(gs_slots); gs_next := s.(gs_next); gs_memo := m |}
    | RtBad msg => GReject msg
    | RtFuel => GFuel
    end.

Definition alloc (th : thunk) : M lspec :=
  fun s => GOk (LSlot s.(gs_next))
    {| gs_slots := pset s.(gs_next) (SPending th) s.(gs_slots);
       gs_next := Pos.succ s.(gs_next); gs_memo := s.(gs_memo) |}.

Definition set_slot (id : positive) (x : slot) (s : gstate) : gstate :=
  {| gs_slots := pset id x s.(gs_slots); gs_next := s.(gs_next); gs_memo := s.(gs_memo) |}.

Fixpoint map_m {A B} (f : A -> M B) (l : list A) : M (list B) :=
  match l with
  | [] => ret []
  | x :: l => y <- f x ;; ys <- map_m f l ;; ret (y :: ys)
  end.

Fixpoint mapi_m_rec {A B} (f : nat -> A -> M B) (i : nat) (l : list A) : M (list B) :=
  match l with
  | [] => ret []
  | x :: l => y <- f i x ;; ys <- mapi_m_rec f (S i) l ;; ret (y :: ys)
  end.

Definition sep_first {A} (l : list A) : M (A * list A) :=
  match l with x :: l => ret (x, l) | [] => reject "guard check: empty redex stack" end.

(** ** Messages *)

Definition err_anomaly := "guard check: ill-formed term".
Definition err_scope := "a de Bruijn index escapes the block's context".
Definition err_evar := "the guard checker does not handle existential variables".
Definition err_var := "the guard checker does not handle section variables".
Definition err_ind_missing := "an inductive type is not declared in the environment".
Definition err_const_missing := "a constant is not declared in the environment".
Definition err_illegal := "a recursive call is not on a structural subterm".
Definition err_nargs := "a recursive call is not applied to its recursive argument".
Definition err_discard := "a reduction step discards a recursive call that is not yet guarded".
Definition err_prefix_occ := "a function of the block occurs in the binder prefix of a fixpoint".
Definition err_nabs := "the body of a fixpoint has too few abstractions".
Definition err_notind := "the recursive argument of a fixpoint is not of an inductive type".
Definition err_elim := "the recursive argument's inductive type cannot be eliminated into the fixpoint's sort".
Definition err_cycle := "a deferred subterm specification depends on itself".

(** ** Pure helpers *)

Fixpoint set_nth {A} (i : nat) (x : A) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l, 0 => x :: l
  | y :: l, S i => y :: set_nth i x l
  end.

Definition push_var (r : renv) (s : lspec) : renv :=
  {| r_lets := None :: r.(r_lets); r_depth := S r.(r_depth); r_min := S r.(r_min);
     r_genv := s :: r.(r_genv) |}.

Definition push_let (r : renv) (c : term) (s : lspec) : renv :=
  {| r_lets := Some c :: r.(r_lets); r_depth := S r.(r_depth); r_min := S r.(r_min);
     r_genv := s :: r.(r_genv) |}.

(** [push_var_renv] *)
Definition push_var_renv (r : renv) (lvl : nat) : renv :=
  push_var r (LVal (if Nat.leb 1 lvl then Internally_bound_subterm [lvl] else Not_subterm)).

(** [push_ctxt_renv]: [l] gives the [let] bodies, innermost first. *)
Definition push_decls (r : renv) (l : list (option term)) : renv :=
  {| r_lets := l ++ r.(r_lets); r_depth := #|l| + r.(r_depth); r_min := #|l| + r.(r_min);
     r_genv := repeat (LVal Not_subterm) #|l| ++ r.(r_genv) |}.

(** [push_fix_renv] *)
Definition push_fix_renv (r : renv) (nb : nat) : renv := push_decls r (repeat None nb).

(** [assign_var_spec], with an index from 0. *)
Definition assign_var_spec (r : renv) (i : nat) (s : lspec) : M renv :=
  if Nat.ltb i #|r.(r_genv)| then
    ret {| r_lets := r.(r_lets); r_depth := r.(r_depth); r_min := r.(r_min);
           r_genv := set_nth i s r.(r_genv) |}
  else reject err_anomaly.

Fixpoint needreduce_of_stack (s : list stack_element) : fix_check_result :=
  match s with
  | [] => NoNeedReduce
  | SArg _ :: l => needreduce_of_stack l
  | SClosure st _ _ _ :: l => orfcr st (needreduce_of_stack l)
  end.

Definition lift_stack (k : nat) (s : list stack_element) : list stack_element :=
  map (fun e => match e with SClosure st r n c => SClosure st r (n + k) c | x => x end) s.

Definition push_stack_closures (r : renv) (l : list term) (stack : list stack_element) :=
  map (fun a => SClosure NoNeedReduce r 0 a) l ++ stack.

Definition push_stack_args (l : list lspec) (stack : list stack_element) :=
  map SArg l ++ stack.

Definition illegal_msg (z : stack_element) : string :=
  match z with SArg _ => err_nargs | SClosure _ _ _ _ => err_illegal end.

(** [true] if a status other than the [k]-th is pending. *)
Fixpoint pending_except (k j : nat) (l : list fix_check_result) : bool :=
  match l with
  | [] => false
  | x :: l => (negb (Nat.eqb j k) && is_need x) || pending_except k (S j) l
  end.

(** [Term.decompose_lambda_decls]: syntactic λs and [let]s. *)
Fixpoint decompose_lam_decls (acc : list (option term)) (t : term) : list (option term) * term :=
  match t with
  | tLambda _ _ b => decompose_lam_decls (None :: acc) b
  | tLetIn _ v _ b => decompose_lam_decls (Some v :: acc) b
  | _ => (acc, t)
  end.

(** [ctx] innermost first. *)
Definition lambdas (ctx : list (aname * term)) (b : term) : term :=
  fold_left (fun b '(na, ty) => tLambda na ty b) ctx b.

Definition lam_form (p : predicate term) : term :=
  it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn).

Definition branch_forms (p : predicate term) (brs : list (branch term)) : list term :=
  map (fun br => it_mkLambda_or_LetIn (inst_case_branch_context p br) br.(bbody)) brs.

(** The heads that [check_rec_call_state]'s expansions treat as anomalies. *)
Definition is_anomaly_head (h : term) : bool :=
  match h with
  | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _ | tSort _ | tPrim _ => true
  | _ => false
  end.

Definition is_block_rel (k nb i : nat) : bool := Nat.leb k i && Nat.ltb i (k + nb).

(** ** Uniform parameters of a nested fixpoint

  [find_uniform_parameters] and [drop_uniform_parameters], with de Bruijn
  indices from 0: in a stripped body under [k] binders, the functions of
  the nested block are [k .. k + nb - 1] and its [j]-th parameter is
  [k - 1 - j].  The kernel's count is a minimum over all occurrences, so
  the order of the traversal does not matter.  [fup] follows the kernel's
  traversal node by node.  At an application headed by a variable, each
  argument that is a bare function of the nested block gives [0]; every
  other argument is visited as the kernel's [fold_constr_with_binders]
  visits it: its immediate subterms (for an application: its head and its
  arguments) are counted by [fup].  So an argument [g u m'], with [g] in the
  nested block, gives [0] through its bare head [g], while [h' (g u m')]
  counts the uniform prefix of [g u m']. *)

Fixpoint uniform_prefix (k nunif j : nat) (l : list term) : nat :=
  match l with
  | [] => j
  | a :: l =>
    if Nat.leb nunif j then nunif else
    match a with
    | tRel m => if Nat.eqb (S (m + j)) k then uniform_prefix k nunif (S j) l else j
    | _ => j
    end
  end.

Fixpoint fup (nb k acc : nat) (c : term) {struct c} : nat :=
  match c with
  | tRel i => if is_block_rel k nb i then 0 else acc
  | tApp u v =>
    match fst (decompose_app c) with
    | tRel i =>
      (* The kernel's [fold_constr_with_binders] on one argument. *)
      let arg (acc : nat) (a : term) : nat :=
        match a with
        | tRel m => if is_block_rel k nb m then 0 else acc
        | tApp _ _ =>
          (fix app (t : term) (acc : nat) {struct t} : nat :=
             match t with
             | tApp t' b => fup nb k (app t' acc) b
             | _ => fup nb k acc t
             end) a acc
        | _ => fup nb k acc a
        end in
      let fix spine (u : term) (acc : nat) {struct u} : nat :=
        match u with
        | tApp u' a => spine u' (arg acc a)
        | _ => acc
        end in
      let acc' := spine u (arg acc v) in
      if is_block_rel k nb i then uniform_prefix k acc' 0 (snd (decompose_app c)) else acc'
    | _ => fup nb k (fup nb k acc u) v
    end
  | tLambda _ A b | tProd _ A b => fup nb (S k) (fup nb k acc A) b
  | tLetIn _ v t b => fup nb (S k) (fup nb k (fup nb k acc v) t) b
  | tCase _ p c brs =>
    let acc := fold_left (fun acc a => fup nb k acc a) p.(pparams) acc in
    let acc := fup nb (k + #|p.(pcontext)|) acc p.(preturn) in
    let acc := fup nb k acc c in
    fold_left (fun acc br => fup nb (k + #|br.(bcontext)|) acc br.(bbody)) brs acc
  | tProj _ c => fup nb k acc c
  | tFix mfix _ | tCoFix mfix _ =>
    let acc := fold_left (fun acc d => fup nb k acc d.(dtype)) mfix acc in
    fold_left (fun acc d => fup nb (k + #|mfix|) acc d.(dbody)) mfix acc
  | tEvar _ l => fold_left (fun acc a => fup nb k acc a) l acc
  | tPrim p =>
    match p with
    | (primArray; primArrayModel ar) =>
      fold_left (fun acc a => fup nb k acc a) ar.(array_value)
        (fup nb k (fup nb k acc ar.(array_default)) ar.(array_type))
    | _ => acc
    end
  | _ => acc
  end.

Fixpoint dup (nunif nb k : nat) (c : term) {struct c} : term :=
  match c with
  | tApp u v =>
    match fst (decompose_app c) with
    | tRel i =>
      let fix spine (u : term) {struct u} : list term :=
        match u with
        | tApp u' a => spine u' ++ [dup nunif nb k a]
        | _ => []
        end in
      let args := spine u ++ [dup nunif nb k v] in
      mkApps (tRel i) (if is_block_rel k nb i then skipn nunif args else args)
    | _ => tApp (dup nunif nb k u) (dup nunif nb k v)
    end
  | tLambda na A b => tLambda na (dup nunif nb k A) (dup nunif nb (S k) b)
  | tProd na A b => tProd na (dup nunif nb k A) (dup nunif nb (S k) b)
  | tLetIn na v t b => tLetIn na (dup nunif nb k v) (dup nunif nb k t) (dup nunif nb (S k) b)
  | tCase ci p c brs =>
    tCase ci
      {| pparams := map (dup nunif nb k) p.(pparams); puinst := p.(puinst);
         pcontext := p.(pcontext); preturn := dup nunif nb (k + #|p.(pcontext)|) p.(preturn) |}
      (dup nunif nb k c)
      (map (fun br => {| bcontext := br.(bcontext);
                         bbody := dup nunif nb (k + #|br.(bcontext)|) br.(bbody) |}) brs)
  | tProj pr c => tProj pr (dup nunif nb k c)
  | tFix mfix idx =>
    tFix (map (fun d => {| dname := d.(dname); dtype := dup nunif nb k d.(dtype);
                           dbody := dup nunif nb (k + #|mfix|) d.(dbody); rarg := d.(rarg) |}) mfix) idx
  | tCoFix mfix idx =>
    tCoFix (map (fun d => {| dname := d.(dname); dtype := dup nunif nb k d.(dtype);
                             dbody := dup nunif nb (k + #|mfix|) d.(dbody); rarg := d.(rarg) |}) mfix) idx
  | tEvar ev l => tEvar ev (map (dup nunif nb k) l)
  | tPrim p => tPrim (mapu_prim (fun l => l) (dup nunif nb k) p)
  | _ => c
  end.

Definition find_uniform_parameters (nb : nat) (recindx : list nat) (nargs : nat)
  (stripped : list term) : nat :=
  fold_left (fun acc '(ri, c) => fup nb (S ri) acc c) (combine recindx stripped)
    (fold_left Nat.min recindx nargs).

Definition drop_uniform_parameters (nunif nb : nat) (recindx : list nat) (stripped : list term)
  : list term :=
  map (fun '(ri, c) => dup nunif nb (S ri) c) (combine recindx stripped).

(** ** Sorts: [is_allowed_fixpoint] compares qualities only. *)

Inductive quality := QSProp | QProp | QType.

Definition quality_of (s : sort) : quality :=
  match s with sSProp => QSProp | sProp => QProp | sType _ => QType end.

Definition elim_to (q1 q2 : quality) : bool :=
  match q1, q2 with
  | QType, _ => true
  | QProp, (QProp | QSProp) => true
  | QSProp, QSProp => true
  | _, _ => false
  end.

(** ** The recursive calls of the check, as one sum type

  Each constructor is one of the kernel's mutually recursive functions, or
  a loop of the port (a checked weak-head reduction, a decomposition). *)

(** How the parts a reduction step discards are checked: against a redex
    stack, with no redex stack (no pending status at all), or (in the
    block's own prefix) for any mention of the block [k .. k + nb - 1]. *)
Inductive cmode := CMRs (rs : list fix_check_result) | CMStrict | CMNoOcc (k nb : nat).

(** The [expand_head] closures of [check_rec_call_state]. *)
Inductive expander :=
| ENone
| ERel (i : nat)
| EConst (c : kername) (u : Instance.t)
| ECase (ci : case_info) (p : predicate term) (brs : list (branch term)) (brs' : list term)
    (c0 : term) (sts : list fix_check_result)
| EFix (mfix : mfixpoint term) (i : nat) (stack : list stack_element) (nunif : nat)
    (st_types st_prefix : fix_check_result) (st_bodies : list fix_check_result)
| EProj (p : projection) (c : term).

Inductive call :=
| CStack (r : renv) (stack : list stack_element) (rs : list fix_check_result) (t : term)
  (** [check_rec_call_stack] *)
| CNested (nrb : nat) (r : renv) (decr : nat) (stack : list stack_element)
    (rs : list fix_check_result) (body : term)
  (** [check_nested_fix_body] *)
| CPrefix (r : renv) (needed : nat) (c : term) (rs : list fix_check_result)
  (** [check_erased_prefix] *)
| CBeta (r : renv) (needed : nat) (f : term) (args : list term) (rs : list fix_check_result)
  (** [check_erased_beta] *)
| CSpec (r : renv) (stack : list stack_element) (t : term)
  (** [subterm_specif] *)
| CForce (id : positive)
  (** forcing a deferred specification *)
| CWhd (r : renv) (m : cmode) (t : term)
  (** weak-head normal form by checked steps *)
| CClean (r : renv) (m : cmode) (part : term)
  (** a discarded part carries no pending status *)
| CLams (r : renv) (m : cmode) (acc : list (option term)) (t : term)
  (** [whd_decompose_lambda_decls] *)
| CProds (r : renv) (m : cmode) (acc : list (aname * term)) (t : term)
  (** [whd_decompose_prod] *)
| CRaw (nb k needed : nat) (c : term)
  (** [raw_prefix_escapes] *)
| CRawBeta (nb k needed : nat) (f : term) (args : list term).

Definition cres (c : call) : Type :=
  match c with
  | CStack _ _ _ _ | CNested _ _ _ _ _ _ | CPrefix _ _ _ _ | CBeta _ _ _ _ _ => list fix_check_result
  | CSpec _ _ _ | CForce _ => subterm_spec
  | CWhd _ _ _ => term
  | CClean _ _ _ => unit
  | CLams _ _ _ _ => list (option term) * term
  | CProds _ _ _ _ => list (aname * term) * term
  | CRaw _ _ _ _ | CRawBeta _ _ _ _ _ => bool
  end.

Inductive check_subterm_result := InvalidSubterm | NeedReduceSubterm (l : list nat).

Definition inter_recarg (r1 r2 : recarg) : option recarg :=
  if recarg_eqb r1 r2 then Some r1 else None.

Definition match_inductive (ind : inductive) (ra : recarg) : bool :=
  match ra with Mrec (RecArgInd i) => eqb ind i | _ => false end.

Section Checker.
  Context (lookup : kername -> option global_decl) (retro : Retroknowledge.t)
    (fuel : nat) (n_ctx : nat).

  (** The reducer of the recursive-argument trees: every variable opaque. *)
  Definition plain_whd (t : term) : red_answer :=
    match whd_plain lookup retro fuel t with
    | WhdOk t' _ => RdWhnf t'
    | WhdBad msg => RdBad msg
    | WhdFuel => RdFuel
    end.

  Definition lookup_mib (kn : kername) : M mutual_inductive_body :=
    match lookup kn with
    | Some (InductiveDecl mib) => ret mib
    | _ => reject err_ind_missing
    end.

  (** [mind_recargs] of [ind], memoised by block. *)
  Definition tree_of (ind : inductive) : M wf_paths :=
    p <- with_memo (fun m => ind_block_recargs_memo plain_whd lookup retro fuel m ind.(inductive_mind)) ;;
    of_option err_ind_missing (nth_error p.2 ind.(inductive_ind)).

  Definition inter_paths (t1 t2 : wf_paths) : M wf_paths :=
    of_rt (rt_inter recarg_eqb inter_recarg Norec fuel t1 t2).

  Definition incl_paths (t1 t2 : wf_paths) : M bool :=
    of_rt (rt_incl recarg_eqb inter_recarg Norec fuel t1 t2).

  Definition spec_of_tree (internal : list nat) (t : wf_paths) : M subterm_spec :=
    b <- of_rt (is_norec_path fuel t) ;;
    ret (if b then Not_subterm else Subterm internal Strict t).

  Definition inter_spec (s1 s2 : subterm_spec) : M subterm_spec :=
    match s1, s2 with
    | _, Dead_code => ret s1
    | Dead_code, _ => ret s2
    | Not_subterm, _ => ret s1
    | _, Not_subterm => ret s2
    | Internally_bound_subterm l1, Internally_bound_subterm l2 =>
      ret (Internally_bound_subterm (iset_union l1 l2))
    | Subterm l1 a1 t1, Internally_bound_subterm l2 => ret (Subterm (iset_union l1 l2) a1 t1)
    | Internally_bound_subterm l1, Subterm l2 a2 t2 => ret (Subterm (iset_union l1 l2) a2 t2)
    | Subterm l1 a1 t1, Subterm l2 a2 t2 =>
      t <- inter_paths t1 t2 ;; ret (Subterm (iset_union l1 l2) (size_glb a1 a2) t)
    end.

  Fixpoint fold_inter (acc : subterm_spec) (l : list subterm_spec) : M subterm_spec :=
    match l with
    | [] => ret acc
    | s :: l => acc <- inter_spec acc s ;; fold_inter acc l
    end.

  Definition check_is_subterm (s : subterm_spec) (tree : wf_paths) : M check_subterm_result :=
    match s with
    | Subterm need Strict tree' =>
      b <- incl_paths tree tree' ;; ret (if b then NeedReduceSubterm need else InvalidSubterm)
    | Dead_code => ret (NeedReduceSubterm [])
    | Not_subterm | Subterm _ Large _ => ret InvalidSubterm
    | Internally_bound_subterm l => ret (NeedReduceSubterm l)
    end.

  Definition set_need_reduce_one (nr : nat) (msg : string) (rs : list fix_check_result)
    : M (list fix_check_result) :=
    let mr := #|rs| in
    if Nat.eqb nr 0 || Nat.ltb mr nr then reject err_anomaly else
    match skipn (mr - nr) rs with
    | _ :: rs2 => ret (firstn (mr - nr) rs ++ NeedReduce msg :: rs2)
    | [] => reject err_anomaly
    end.

  Fixpoint set_need_reduce (l : list nat) (msg : string) (rs : list fix_check_result)
    : M (list fix_check_result) :=
    match l with
    | [] => ret rs
    | x :: l => rs <- set_need_reduce_one x msg rs ;; set_need_reduce l msg rs
    end.

  (** [stack_element_specif]: a fresh deferred specification, as the kernel
      builds a fresh [Lazy.t] at each call. *)
  Definition element_spec (z : stack_element) : M lspec :=
    match z with
    | SClosure _ r _ h => alloc (TSub r [] h)
    | SArg x => ret x
    end.

  Definition extract_stack (stack : list stack_element) : M (lspec * list stack_element) :=
    match stack with
    | [] => ret (LVal Not_subterm, [])
    | e :: l => s <- element_spec e ;; ret (s, l)
    end.

  (** [set_iota_specif nr] when [io = Some nr]; the identity otherwise. *)
  Definition iota_spec (io : option nat) (s : lspec) : M lspec :=
    match io with None => ret s | Some nr => alloc (TIota nr s) end.

  Fixpoint all_not (io : option nat) (stack : list stack_element) : M (list stack_element) :=
    match stack with
    | [] => ret []
    | _ :: s => x <- iota_spec io (LVal Not_subterm) ;; rest <- all_not io s ;; ret (SArg x :: rest)
    end.

  (** [filter_fix_stack_domain] *)
  Fixpoint filter_fix_stack (nr decrarg i nunif : nat) (stack : list stack_element)
    : M (list stack_element) :=
    match stack with
    | [] => ret []
    | a :: stack =>
      let '(uniform, nunif') := match nunif with 0 => (false, 0) | S k => (true, k) end in
      a' <- (if uniform then ret a
             else if Nat.eqb i decrarg then (s <- element_spec a ;; ret (SArg s))
             else (s <- alloc (TIota nr (LVal Not_subterm)) ;; ret (SArg s))) ;;
      rest <- filter_fix_stack nr decrarg (S i) nunif' stack ;;
      ret (a' :: rest)
    end.

  (** [branches_specif]: the deferred specifications of the arguments of
      each constructor.  A match on a coinductive ([CoFinite]) type gives
      [Not_subterm] everywhere. *)
  Definition branches_specif (ind : inductive) (cs : lspec) : M (list (list lspec)) :=
    tree <- tree_of ind ;;
    x <- of_rt (rt_dest_node fuel tree) ;;
    let car := map (fun l => #|l|) x.2 in
    mib <- lookup_mib ind.(inductive_mind) ;;
    match mib.(ind_finite) with
    | CoFinite => ret (map (fun nca => repeat (LVal Not_subterm) nca) car)
    | _ =>
      mapi_m_rec (fun i nca => map_m (fun j => alloc (TBranch cs ind i nca j)) (seq 0 nca)) 0 car
    end.

  Definition has_constant_params (nvars k : nat) (ind : inductive) (args : list term) : M bool :=
    with_memo (fun m => has_constant_parameters plain_whd lookup retro fuel m nvars k ind args).

  Definition recargs_approx (tree : wf_paths) (ind : inductive) (args : list term) : M wf_paths :=
    with_memo (fun m => get_recargs_approx plain_whd lookup retro fuel m tree ind args).

  Section Block.
    (** The number of functions of the block, their recursive argument
        positions and the trees of their recursive arguments. *)
    Context (nfi : nat) (recpos : list nat) (trees : list wf_paths).

    Section Steps.
      Context (rec : forall c, M (cres c)).

      Definition c_stack r stack rs t : M (list fix_check_result) := rec (CStack r stack rs t).
      Definition c_whd r m t : M term := rec (CWhd r m t).
      Definition c_lams r m t : M (list (option term) * term) := rec (CLams r m [] t).
      Definition c_prods r m t : M (list (aname * term) * term) := rec (CProds r m [] t).
      Definition c_spec r stack t : M subterm_spec := rec (CSpec r stack t).

      Definition force (s : lspec) : M subterm_spec :=
        match s with LVal x => ret x | LSlot id => rec (CForce id) end.

      (** [check_rec_call] *)
      Definition rec_call r rs c : M (fix_check_result * list fix_check_result) :=
        rs' <- c_stack r [] (NoNeedReduce :: rs) c ;; sep_first rs'.

      Fixpoint clean_all (r : renv) (m : cmode) (l : list term) : M unit :=
        match l with
        | [] => ret tt
        | a :: l => _ <- rec (CClean r m a) ;; clean_all r m l
        end.

      (** A checked weak head, with a cofixpoint at the head contracted as
          the kernel does in a match or a projection. *)
      Definition whd_ctor r rs c : M (term * list term) :=
        c' <- c_whd r (CMRs rs) c ;;
        match head_cofix c' with
        | Some (mfix, idx, args) =>
          match contract_cofix mfix idx with
          | None => reject err_anomaly
          | Some (fn, d) =>
            _ <- clean_all r (CMRs rs) d ;;
            c'' <- c_whd r (CMRs rs) (mkApps fn args) ;;
            ret (decompose_app c'')
          end
        | None => ret (decompose_app c')
        end.

      (** The [expand_head] closures of [check_rec_call_state]. *)
      Definition expand r rs (e : expander) : M (option (term * list stack_element)) :=
        match e with
        | ENone => ret None
        | ERel i =>
          ret (match nth_error r.(r_lets) i with Some (Some b) => Some (lift0 (S i) b, []) | _ => None end)
        | EConst c u =>
          match lookup c with
          | Some (ConstantDecl cb) => ret (option_map (fun b => (subst_instance u b, [])) cb.(cst_body))
          | _ => reject err_const_missing
          end
        | ECase ci p brs brs' c0 sts =>
          x <- whd_ctor r rs c0 ;;
          let (hd, args) := x in
          match hd with
          | tConstruct ind k _ =>
            if negb (eq_inductive ind ci.(ci_ind)) then reject err_anomaly else
            br <- of_option err_anomaly (nth_error brs k) ;;
            br' <- of_option err_anomaly (nth_error brs' k) ;;
            if negb (Nat.eqb #|args| (ci.(ci_npar) + context_assumptions br.(bcontext)))
            then reject err_anomaly else
            if pending_except k 0 sts then reject err_discard else
            _ <- clean_all r (CMRs rs) (p.(pparams) ++ lam_form p :: firstn ci.(ci_npar) args) ;;
            ret (Some (mkApps br' (skipn ci.(ci_npar) args), []))
          | h => if is_anomaly_head h then reject err_anomaly else ret None
          end
        | EFix mfix i stack nunif st_t st_p st_b =>
          d <- of_option err_anomaly (nth_error mfix i) ;;
          match nth_error stack d.(rarg) with
          | None | Some (SArg _) => ret None
          | Some (SClosure _ _ k recArg) =>
            c <- c_whd r (CMRs rs) (lift0 k recArg) ;;
            let hd := fst (decompose_app c) in
            match hd with
            | tConstruct _ _ _ =>
              if noccur_between 0 #|mfix| d.(dbody)
                 && (is_need st_t || is_need st_p || pending_except i 0 st_b)
              then reject err_discard
              else ret (Some (subst0 (fix_subst mfix) d.(dbody), firstn nunif stack))
            | h => if is_anomaly_head h then reject err_anomaly else ret None
            end
          end
        | EProj pr c =>
          x <- whd_ctor r rs c ;;
          let (hd, args) := x in
          match hd with
          | tConstruct ind k _ =>
            if negb (eq_inductive ind pr.(proj_ind)) || negb (Nat.eqb k 0) then reject err_anomaly else
            let kk := pr.(proj_npars) + pr.(proj_arg) in
            a <- of_option err_anomaly (nth_error args kk) ;;
            _ <- clean_all r (CMRs rs) (except_nth kk args) ;;
            ret (Some (a, []))
          | h => if is_anomaly_head h then reject err_anomaly else ret None
          end
        end.

      (** [check_rec_call_state] *)
      Definition state r nrh stack rs e : M (list fix_check_result) :=
        match orfcr nrh (needreduce_of_stack stack) with
        | NoNeedReduce => ret rs
        | NeedReduce msg =>
          o <- expand r rs e ;;
          match o with
          | None => match rs with [] => reject err_anomaly | _ :: rs' => ret (NeedReduce msg :: rs') end
          | Some (c, stack') => c_stack r (stack' ++ stack) rs c
          end
        end.

      (** [check_inert_subterm_rec_call] *)
      Definition inert r rs c : M (list fix_check_result) :=
        x <- rec_call r rs c ;; state r x.1 [] x.2 ENone.

      Fixpoint fold_inert r rs (l : list term) : M (list fix_check_result) :=
        match l with
        | [] => ret rs
        | a :: l => rs <- inert r rs a ;; fold_inert r rs l
        end.

      (** [pop_argument] *)
      Definition pop_argument (nr : fix_check_result) r elt stack (b : term)
        : M (renv * (list stack_element * term)) :=
        match nr, elt with
        | NoNeedReduce, SClosure NoNeedReduce _ k c =>
          s <- element_spec elt ;; ret (push_let r (lift0 k c) s, (lift_stack 1 stack, b))
        | _, SClosure st _ k c =>
          if is_need nr || (noccur_between 0 1 b && is_need st) then reject err_discard
          else ret (r, (stack, subst10 (lift0 k c) b))
        | _, SArg s =>
          if is_need nr then reject err_discard else ret (push_var r s, (lift_stack 1 stack, b))
        end.

      Fixpoint push_args r (l : list term) rs stack
        : M (list fix_check_result * list stack_element) :=
        match l with
        | [] => ret (rs, stack)
        | a :: l => x <- rec_call r rs a ;; push_args r l x.2 (SClosure x.1 r 0 a :: stack)
        end.

      (** [split_struct_arg]: [None] for too few abstractions. *)
      Fixpoint split_loop (m : cmode) (lvl : nat) (r : renv) (k : nat) (ctx : list (aname * term))
        (c : term) : M (option (list (aname * term) * term)) :=
        match k with
        | 0 => ret (Some (ctx, c))
        | S k =>
          c' <- c_whd r m c ;;
          match c' with
          | tLambda na ty bd => split_loop m lvl (push_var_renv r lvl) k ((na, ty) :: ctx) bd
          | _ => ret None
          end
        end.

      (** [filter_stack_domain]: [p'] is the return clause as an abstraction. *)
      Fixpoint filter_loop (io : option nat) (len : nat) (r : renv) (k : nat) (ar : term)
        (stack : list stack_element) : M (list stack_element) :=
        match stack with
        | [] => ret []
        | elt :: stack' =>
          t <- c_whd r CMStrict ar ;;
          match t with
          | tProd _ a c0 =>
            x <- c_prods r CMStrict a ;;
            let r2 := push_decls r (map (fun _ => None) x.1) in
            a' <- c_whd r2 CMStrict x.2 ;;
            let (ty, args) := decompose_app a' in
            elt' <- (match ty with
                     | tInd ind _ =>
                       s <- element_spec elt ;;
                       b <- has_constant_params len (k + #|x.1|) ind args ;;
                       if b then ret (SArg s) else (s' <- alloc (TFilter s ind args) ;; ret (SArg s'))
                     | _ => s <- iota_spec io (LVal Not_subterm) ;; ret (SArg s)
                     end) ;;
            rest <- filter_loop io len (push_var r (LVal Not_subterm)) (S k) c0 stack' ;;
            ret (elt' :: rest)
          | _ => all_not io stack
          end
        end.

      Definition filter_stack_domain r (p' : term) (io : option nat) stack : M (list stack_element) :=
        let (absctx, ar) := decompose_lam_decls [] p' in
        let len := #|absctx| in
        if noccur_between 0 len ar then ret stack
        else filter_loop io len (push_decls r absctx) 0 ar stack.

      (** [restrict_spec] *)
      Definition restrict_spec r (sp : subterm_spec) (p' : term) : M subterm_spec :=
        match sp with
        | Not_subterm | Internally_bound_subterm _ => ret sp
        | _ =>
          x <- c_lams r CMStrict p' ;;
          let len := #|x.1| in
          if noccur_between 0 len x.2 then ret sp else
          let r1 := push_decls r x.1 in
          y <- c_prods r1 CMStrict x.2 ;;
          let r2 := push_decls r1 (map (fun _ => None) y.1) in
          s <- c_whd r2 CMStrict y.2 ;;
          let (hd, args) := decompose_app s in
          match hd with
          | tInd ind _ =>
            b <- has_constant_params len #|y.1| ind args ;;
            if b then ret sp else
            match sp with
            | Dead_code => ret sp
            | Subterm l st tree =>
              ra <- recargs_approx tree ind args ;; t' <- inter_paths tree ra ;; ret (Subterm l st t')
            | _ => reject err_anomaly
            end
          | _ => ret Not_subterm
          end
        end.

      (** [check_inductive_codomain] *)
      Definition inductive_codomain r (p : term) : M bool :=
        x <- c_lams r CMStrict p ;;
        let r1 := push_decls r x.1 in
        y <- c_prods r1 CMStrict x.2 ;;
        let r2 := push_decls r1 (map (fun _ => None) y.1) in
        s <- c_whd r2 CMStrict y.2 ;;
        ret (match fst (decompose_app s) with tInd _ _ => true | _ => false end).

      (** [find_inductive]; [None] is the kernel's [Not_found]. *)
      Definition find_inductive r (c : term) : M (option inductive) :=
        c' <- c_whd r CMStrict c ;;
        match fst (decompose_app c') with
        | tInd ind _ =>
          mib <- lookup_mib ind.(inductive_mind) ;;
          match mib.(ind_finite) with CoFinite => ret None | _ => ret (Some ind) end
        | _ => ret None
        end.

      Fixpoint spec_branches r (cs : list (list lspec)) stack' (l : list term) (k : nat)
        : M (list subterm_spec) :=
        match l with
        | [] => ret []
        | b :: l =>
          a <- of_option err_anomaly (nth_error cs k) ;;
          s <- c_spec r (push_stack_args a stack') b ;;
          rest <- spec_branches r cs stack' l (S k) ;;
          ret (s :: rest)
        end.

      (** The [Fix] case of [subterm_specif]. *)
      Definition fix_spec r stack (l : list term) (mfix : mfixpoint term) (i : nat) : M subterm_spec :=
        d <- of_option err_anomaly (nth_error mfix i) ;;
        ok <- inductive_codomain r d.(dtype) ;;
        if negb ok then ret Not_subterm else
        x <- c_prods r CMStrict d.(dtype) ;;
        oind <- find_inductive (push_decls r (map (fun _ => None) x.1)) x.2 ;;
        match oind with
        | None => ret Not_subterm
        | Some ind =>
          recargs <- tree_of ind ;;
          let nb := #|mfix| in
          r' <- assign_var_spec (push_fix_renv r nb) (nb - S i) (LVal (Subterm [] Strict recargs)) ;;
          sp <- split_loop CMStrict 0 r' (S d.(rarg)) [] d.(dbody) ;;
          match sp with
          | None => ret Not_subterm
          | Some (sign, stripped) =>
            let stack' := push_stack_closures r l stack in
            let r'' := push_decls r' (map (fun _ => None) sign) in
            r'' <- (if Nat.ltb #|stack'| (S d.(rarg)) then ret r'' else
                     match nth_error stack' d.(rarg) with
                     | Some e => s <- element_spec e ;; assign_var_spec r'' 0 s
                     | None => reject err_anomaly
                     end) ;;
            c_spec r'' [] stripped
          end
        end.

      (** [subterm_specif] *)
      Definition spec_step r stack (t : term) : M subterm_spec :=
        t' <- c_whd r CMStrict t ;;
        let (f, l) := decompose_app t' in
        match f with
        | tRel i =>
          if Nat.leb (r.(r_depth) + n_ctx) i then reject err_scope else
          match nth_error r.(r_genv) i with Some s => force s | None => ret Not_subterm end
        | tCase ci p c brs =>
          let p' := lam_form p in
          stack' <- filter_stack_domain r p' None (push_stack_closures r l stack) ;;
          cs <- alloc (TSub r [] c) ;;
          case_spec <- branches_specif ci.(ci_ind) cs ;;
          stl <- spec_branches r case_spec stack' (branch_forms p brs) 0 ;;
          sp <- fold_inter Dead_code stl ;;
          restrict_spec r sp p'
        | tFix mfix i => fix_spec r stack l mfix i
        | tLambda _ _ b =>
          match l with
          | [] => x <- extract_stack stack ;; c_spec (push_var r x.1) x.2 b
          | _ => reject err_anomaly
          end
        | tEvar _ _ => reject err_evar
        | tVar _ => reject err_var
        | tProj pr c =>
          subt <- c_spec r stack c ;;
          mib <- lookup_mib pr.(proj_ind).(inductive_mind) ;;
          match mib.(ind_finite) with
          | CoFinite => ret Not_subterm
          | _ =>
            match subt with
            | Subterm internal _ wf =>
              subs <- of_rt (dest_subterms fuel wf) ;;
              a0 <- of_option err_anomaly (nth_error subs 0) ;;
              a <- of_option err_anomaly (nth_error a0 pr.(proj_arg)) ;;
              spec_of_tree internal a
            | s => ret s
            end
          end
        | tConst c _ =>
          match lookup c with Some (ConstantDecl _) => ret Not_subterm | _ => reject err_const_missing end
        | _ => ret Not_subterm
        end.

      (** Forcing a slot computes it once, in the order the kernel forces
          its [Lazy.t]. *)
      Definition compute_thunk (th : thunk) : M subterm_spec :=
        match th with
        | TSub r stack t => c_spec r stack t
        | TIota nr s =>
          x <- force s ;;
          ret (match x with
               | Not_subterm => if Nat.leb 1 nr then Internally_bound_subterm [nr] else Not_subterm
               | x => x
               end)
        | TBranch cs ind i nca j =>
          x <- force cs ;;
          match x with
          | Subterm internal _ t =>
            ra <- of_rt (dest_recarg fuel t) ;;
            if match_inductive ind ra then
              subs <- of_rt (dest_subterms fuel t) ;;
              vra <- of_option err_anomaly (nth_error subs i) ;;
              if negb (Nat.eqb nca #|vra|) then reject err_anomaly else
              a <- of_option err_anomaly (nth_error vra j) ;;
              spec_of_tree internal a
            else ret Not_subterm
          | Dead_code => ret Dead_code
          | Internally_bound_subterm l => ret (Internally_bound_subterm l)
          | Not_subterm => ret Not_subterm
          end
        | TFilter s ind args =>
          x <- force s ;;
          match x with
          | Subterm l sz tree =>
            ra <- recargs_approx tree ind args ;; t' <- inter_paths tree ra ;; ret (Subterm l sz t')
          | x => ret x
          end
        end.

      Definition force_step (id : positive) : M subterm_spec :=
        fun st =>
          match pget id st.(gs_slots) with
          | Some (SDone x) => GOk x st
          | Some SForcing => GReject err_cycle
          | Some (SPending th) =>
            gbind (compute_thunk th) (fun x st' => GOk x (set_slot id (SDone x) st'))
              (set_slot id SForcing st)
          | None => GReject err_anomaly
          end.

      Definition whd_step r m (t : term) : M term :=
        match head_step lookup retro r.(r_lets) t with
        | Stuck => ret t
        | StepBad msg => reject msg
        | Stepped t' d => _ <- clean_all r m d ;; c_whd r m t'
        end.

      (** A discarded part: no pending status at its own level, and none set
          where there was none ([CMRs]); no pending status at all
          ([CMStrict]); no mention of the block ([CMNoOcc]). *)
      Definition clean_step r m (part : term) : M unit :=
        match m with
        | CMNoOcc k nb => if noccur_between k nb part then ret tt else reject err_prefix_occ
        | CMRs rs =>
          if noccur_between r.(r_min) nfi part then ret tt else
          x <- rec_call r rs part ;;
          if is_need x.1 then reject err_discard else
          if forallb2 (fun a b => negb (is_need b) || is_need a) rs x.2 then ret tt
          else reject err_discard
        | CMStrict =>
          if noccur_between r.(r_min) nfi part then ret tt else
          x <- rec_call r [] part ;;
          if is_need x.1 then reject err_discard else ret tt
        end.

      Definition lams_step r m acc (t : term) : M (list (option term) * term) :=
        match t with
        | tLambda _ _ b => rec (CLams (push_var r (LVal Not_subterm)) m (None :: acc) b)
        | tLetIn _ v _ b => rec (CLams (push_let r v (LVal Not_subterm)) m (Some v :: acc) b)
        | _ =>
          match head_step lookup retro r.(r_lets) t with
          | Stuck => ret (acc, t)
          | StepBad msg => reject msg
          | Stepped t' d => _ <- clean_all r m d ;; rec (CLams r m acc t')
          end
        end.

      Definition prods_step r m acc (t : term) : M (list (aname * term) * term) :=
        t' <- c_whd r m t ;;
        match t' with
        | tProd na a b => rec (CProds (push_var r (LVal Not_subterm)) m ((na, a) :: acc) b)
        | _ => ret (acc, t')
        end.

      (** [check_erased_prefix]; a [let]'s type is analysed too. *)
      Definition prefix_step r (needed : nat) (c : term) rs : M (list fix_check_result) :=
        match needed with
        | 0 => ret rs
        | S needed' =>
          match c with
          | tLambda _ ty bd => rs <- inert r rs ty ;; rec (CPrefix (push_var_renv r #|rs|) needed' bd rs)
          | tLetIn _ v ty bd =>
            rs <- (if noccur_between 0 1 bd then inert r rs v else ret rs) ;;
            rs <- inert r rs ty ;;
            s <- alloc (TSub r [] v) ;;
            rec (CPrefix (push_let r v s) needed bd rs)
          | _ =>
            match decompose_app c with
            | (tLambda _ _ _ as f, (_ :: _) as args) => rec (CBeta r needed f args rs)
            | _ => inert r rs c
            end
          end
        end.

      (** [check_erased_beta] *)
      Definition beta_step r needed (f : term) (args : list term) rs : M (list fix_check_result) :=
        match args with
        | [] => rec (CPrefix r needed f rs)
        | a :: rest =>
          match f with
          | tLambda _ ty bd =>
            rs <- inert r rs ty ;;
            rs <- (if noccur_between 0 1 bd then inert r rs a else ret rs) ;;
            rec (CBeta r needed (subst10 a bd) rest rs)
          | _ => inert r rs (mkApps f args)
          end
        end.

      (** [raw_prefix_escapes], with the block at [k .. k + nb - 1]; the type
          of a [let] is a position too. *)
      Definition raw_step (nb k needed : nat) (c : term) : M bool :=
        let mentions k c := negb (noccur_between k nb c) in
        match needed with
        | 0 => ret false
        | S needed' =>
          match c with
          | tLambda _ ty bd => if mentions k ty then ret true else rec (CRaw nb (S k) needed' bd)
          | tLetIn _ v ty bd =>
            if mentions k ty || (noccur_between 0 1 bd && mentions k v) then ret true
            else rec (CRaw nb (S k) needed bd)
          | _ =>
            match decompose_app c with
            | (tLambda _ _ _ as f, (_ :: _) as args) => rec (CRawBeta nb k needed f args)
            | _ => ret (mentions k c)
            end
          end
        end.

      Definition rawbeta_step (nb k needed : nat) (f : term) (args : list term) : M bool :=
        let mentions k c := negb (noccur_between k nb c) in
        match args with
        | [] => rec (CRaw nb k needed f)
        | a :: rest =>
          match f with
          | tLambda _ ty bd =>
            if mentions k ty || (noccur_between 0 1 bd && mentions k a) then ret true
            else rec (CRawBeta nb k needed (subst10 a bd) rest)
          | _ => ret (mentions k (mkApps f args))
          end
        end.

      (** [check_nested_fix_body] *)
      Definition nested_step (nrb : nat) r (decr : nat) stack rs (body : term)
        : M (list fix_check_result) :=
        match decr with
        | 0 => inert r rs body
        | S decr' =>
          b <- c_whd r (CMRs rs) body ;;
          match b with
          | tLambda _ a body =>
            rs <- inert r rs a ;;
            match stack with
            | elt :: stack =>
              y <- pop_argument NoNeedReduce r elt stack body ;;
              rec (CNested nrb y.1 decr' y.2.1 rs y.2.2)
            | [] => rec (CNested nrb (push_var_renv r nrb) decr' [] rs body)
            end
          | _ => reject err_anomaly
          end
        end.

      Fixpoint walk_branches r (cs : list (list lspec)) stack' rs (l : list term) (k : nat)
        : M (list fix_check_result * list fix_check_result) :=
        match l with
        | [] => ret ([], rs)
        | b :: l =>
          a <- of_option err_anomaly (nth_error cs k) ;;
          rs1 <- c_stack r (push_stack_args a stack') (NoNeedReduce :: rs) b ;;
          w <- sep_first rs1 ;;
          v <- walk_branches r cs stack' w.2 l (S k) ;;
          ret (w.1 :: v.1, v.2)
        end.

      Fixpoint fold_prefix r' rs (mfix : mfixpoint term) : M (list fix_check_result) :=
        match mfix with
        | [] => ret rs
        | d :: mfix => rs <- rec (CPrefix r' (S d.(rarg)) d.(dbody) rs) ;; fold_prefix r' rs mfix
        end.

      Fixpoint walk_bodies r' (nrb i : nat) sthis sothers rs (ris : list nat) (bodies : list term)
        (j : nat) : M (list fix_check_result * list fix_check_result) :=
        match ris, bodies with
        | ri :: ris, b :: bodies =>
          rs1 <- rec (CNested nrb r' (S ri) (if Nat.eqb i j then sthis else sothers)
                        (NoNeedReduce :: rs) b) ;;
          w <- sep_first rs1 ;;
          v <- walk_bodies r' nrb i sthis sothers w.2 ris bodies (S j) ;;
          ret (w.1 :: v.1, v.2)
        | _, _ => ret ([], rs)
        end.

      Fixpoint cofix_bodies r r' stack rs (l : list term) : M (list fix_check_result) :=
        match l with
        | [] => ret rs
        | b :: l => x <- rec_call r' rs b ;; rs <- state r x.1 stack x.2 ENone ;; cofix_bodies r r' stack rs l
        end.

      Definition stack_need_ok stack rs : M (list fix_check_result) :=
        if is_need (needreduce_of_stack stack) then reject err_discard else ret rs.

      (** The [Fix] case of [check_rec_call_stack]. *)
      Definition fix_case r stack rs (mfix : mfixpoint term) (i : nat) : M (list fix_check_result) :=
        d <- of_option err_anomaly (nth_error mfix i) ;;
        let decrArg := d.(rarg) in
        let nb := #|mfix| in
        let ris := map rarg mfix in
        rs1 <- fold_inert r (NoNeedReduce :: NoNeedReduce :: rs) (map dtype mfix) ;;
        t1 <- sep_first rs1 ;;
        let r' := push_fix_renv r nb in
        rs2 <- fold_prefix r' (NoNeedReduce :: t1.2) mfix ;;
        t2 <- sep_first rs2 ;;
        let rs' := t2.2 in
        split <- map_m (fun d =>
                   o <- split_loop (CMRs rs') #|rs'| r' (S d.(rarg)) [] d.(dbody) ;;
                   of_option err_nabs o) mfix ;;
        let stripped := map snd split in
        let nunif := find_uniform_parameters nb ris #|stack| stripped in
        let stripped := drop_uniform_parameters nunif nb ris stripped in
        let bodies := map (fun '(sp, b) => lambdas sp.1 b) (combine split stripped) in
        fix_stack <- filter_fix_stack #|rs| decrArg 0 nunif stack ;;
        let fix_stack := if Nat.ltb decrArg #|stack| then firstn (S decrArg) fix_stack else fix_stack in
        let sthis := lift_stack nb fix_stack in
        let sothers := lift_stack nb (firstn nunif fix_stack) in
        w <- walk_bodies r' #|rs'| i sthis sothers rs' ris bodies 0 ;;
        t3 <- sep_first w.2 ;;
        let parts := orfcr t1.1 (orfcr t2.1 (or_list w.1)) in
        state r (orfcr t3.1 parts) (skipn nunif stack) t3.2 (EFix mfix i stack nunif t1.1 t2.1 w.1).

      (** [check_rec_call_stack] *)
      Definition stack_step r stack rs (t : term) : M (list fix_check_result) :=
        match t with
        | tApp _ _ =>
          let (f, args) := decompose_app t in
          x <- push_args r (List.rev args) rs stack ;;
          c_stack r x.2 x.1 f
        | tRel i =>
          if Nat.leb (r.(r_depth) + n_ctx) i then reject err_scope else
          rs <- (if is_block_rel r.(r_min) nfi i then
                   let glob := r.(r_min) + nfi - S i in
                   let np := nth glob recpos 0 in
                   if Nat.leb #|stack| np then set_need_reduce_one #|rs| err_nargs rs
                   else
                     z <- of_option err_anomaly (nth_error stack np) ;;
                     s <- element_spec z ;;
                     sp <- force s ;;
                     tr <- of_option err_anomaly (nth_error trees glob) ;;
                     cr <- check_is_subterm sp tr ;;
                     match cr with
                     | NeedReduceSubterm l => set_need_reduce l (illegal_msg z) rs
                     | InvalidSubterm => reject (illegal_msg z)
                     end
                 else ret rs) ;;
          state r NoNeedReduce stack rs (ERel i)
        | tCase ci p c0 brs =>
          let p' := lam_form p in
          let brs' := branch_forms p brs in
          x <- rec_call r rs c0 ;;
          rs <- inert r x.2 p' ;;
          let rs' := NoNeedReduce :: rs in
          let nr := #|rs'| in
          s0 <- alloc (TSub r [] c0) ;;
          s1 <- alloc (TIota nr s0) ;;
          case_spec <- branches_specif ci.(ci_ind) s1 ;;
          stack' <- filter_stack_domain r p' (Some nr) stack ;;
          y <- walk_branches r case_spec stack' rs' brs' 0 ;;
          z <- sep_first y.2 ;;
          state r (orfcr z.1 (orfcr x.1 (or_list y.1))) stack z.2 (ECase ci p brs brs' c0 y.1)
        | tFix mfix i => fix_case r stack rs mfix i
        | tConst c u => state r NoNeedReduce stack rs (EConst c u)
        | tLambda _ a b =>
          x <- rec_call r rs a ;;
          match stack with
          | elt :: stack =>
            y <- pop_argument x.1 r elt stack b ;; c_stack y.1 y.2.1 x.2 y.2.2
          | [] =>
            if is_need x.1 then reject err_discard else c_stack (push_var_renv r #|x.2|) [] x.2 b
          end
        | tProd _ a u =>
          rs <- inert r rs a ;;
          rs <- stack_need_ok stack rs ;;
          c_stack (push_var_renv r #|rs|) [] rs u
        | tCoFix mfix _ =>
          rs <- fold_inert r rs (map dtype mfix) ;;
          cofix_bodies r (push_fix_renv r #|mfix|) stack rs (map dbody mfix)
        | tInd _ _ | tConstruct _ _ _ => state r NoNeedReduce stack rs ENone
        | tProj pr c => x <- rec_call r rs c ;; state r x.1 stack x.2 (EProj pr c)
        | tVar _ => reject err_var
        | tEvar _ _ => reject err_evar
        | tLetIn _ c ty b =>
          x <- rec_call r rs c ;;
          y <- rec_call r x.2 ty ;;
          match orfcr (needreduce_of_stack stack) (orfcr x.1 y.1) with
          | NoNeedReduce =>
            s <- alloc (TSub r [] c) ;; c_stack (push_let r c s) (lift_stack 1 stack) y.2 b
          | NeedReduce _ =>
            if is_need y.1 || (noccur_between 0 1 b && is_need x.1) then reject err_discard
            else c_stack r stack y.2 (subst10 c b)
          end
        | tSort _ => stack_need_ok stack rs
        | tPrim p =>
          match p with
          | (primArray; primArrayModel ar) =>
            rs <- fold_inert r rs ar.(array_value) ;;
            rs <- inert r rs ar.(array_default) ;;
            rs <- inert r rs ar.(array_type) ;;
            stack_need_ok stack rs
          | _ => stack_need_ok stack rs
          end
        end.
    End Steps.

    Definition step (rec : forall c, M (cres c)) (c : call) : M (cres c) :=
      match c as c0 return M (cres c0) with
      | CStack r stack rs t => stack_step rec r stack rs t
      | CNested nrb r decr stack rs body => nested_step rec nrb r decr stack rs body
      | CPrefix r needed c rs => prefix_step rec r needed c rs
      | CBeta r needed f args rs => beta_step rec r needed f args rs
      | CSpec r stack t => spec_step rec r stack t
      | CForce id => force_step rec id
      | CWhd r m t => whd_step rec r m t
      | CClean r m part => clean_step rec r m part
      | CLams r m acc t => lams_step rec r m acc t
      | CProds r m acc t => prods_step rec r m acc t
      | CRaw nb k needed c => raw_step rec nb k needed c
      | CRawBeta nb k needed f args => rawbeta_step rec nb k needed f args
      end.
  End Block.

  (** The recursion of the check, closed by doubling fuel. *)
  Definition run_rec (nfi : nat) (recpos : list nat) (trees : list wf_paths) : forall c, M (cres c) :=
    @dfuel call (fun c => M (cres c)) (step nfi recpos trees) fuel (fun _ => mfuel).

  (** [check_occur] of [inductive_of_mutfix]: the [k + 1] first abstractions
      of a body, reduced one checked step at a time, with no mention of the
      block; the type of the last one is a [Finite] inductive. *)
  Fixpoint occur_loop (rec : forall c, M (cres c)) (nb kk o : nat) (r : renv) (c : term) (cnt : nat)
    : M (inductive * term) :=
    match cnt with
    | 0 => reject err_nabs
    | S cnt =>
      c' <- rec (CWhd r (CMNoOcc o nb) c) ;;
      match c' with
      | tLambda _ a b =>
        if negb (noccur_between o nb a) then reject err_prefix_occ else
        if Nat.eqb o kk then
          ty <- rec (CWhd r (CMNoOcc o nb) a) ;;
          match fst (decompose_app ty) with
          | tInd ind _ =>
            mib <- lookup_mib ind.(inductive_mind) ;;
            match mib.(ind_finite) with Finite => ret (ind, b) | _ => reject err_notind end
          | _ => reject err_notind
          end
        else occur_loop rec nb kk (S o) (push_var r (LVal Not_subterm)) b cnt
      | _ => reject err_nabs
      end
    end.

  (** [is_allowed_fixpoint], and the elimination test of [ind_kelim]. *)
  Definition allowed_fixpoint (d : def term) (ind : inductive) : M unit :=
    mib <- lookup_mib ind.(inductive_mind) ;;
    idecl <- of_option err_ind_missing (nth_error mib.(ind_bodies) ind.(inductive_ind)) ;;
    let qs := quality_of idecl.(ind_sort) in
    let rel := d.(dname).(binder_relevance) in
    let qb := match rel with Irrelevant => QSProp | Relevant => QProp end in
    let squashed := match idecl.(ind_kelim), rel with IntoSProp, Relevant => true | _, _ => false end in
    if (elim_to qs QProp || elim_to qs qb) && negb squashed then ret tt else reject err_elim.

  Fixpoint check_bodies (rec : forall c, M (cres c)) (nb : nat)
    (l : list (def term * (inductive * term) * wf_paths)) : M unit :=
    match l with
    | [] => ret tt
    | (d, (_, body), tree) :: l =>
      let k := S d.(rarg) in
      let r0 := {| r_lets := repeat None (k + nb); r_depth := k + nb; r_min := k;
                   r_genv := [LVal (Subterm [] Large tree)] |} in
      rs <- rec (CStack r0 [] [NoNeedReduce] body) ;;
      x <- sep_first rs ;;
      match x with
      | (NeedReduce msg, _) => reject msg
      | (NoNeedReduce, []) => check_bodies rec nb l
      | (NoNeedReduce, _ :: _) => reject err_anomaly
      end
    end.

  Definition init_state : gstate := {| gs_slots := PEmpty; gs_next := 1%positive; gs_memo := [] |}.

  (** [check_fix] *)
  Definition check_fix_block (mfix : mfixpoint term) : guard_result :=
    let nb := #|mfix| in
    if Nat.eqb nb 0 then Reject err_anomaly else
    if negb (forallb (fun d => closedn n_ctx d.(dtype) && closedn (n_ctx + nb) d.(dbody)) mfix)
    then Reject err_scope else
    let rec0 := run_rec 0 [] [] in
    let m : M unit :=
      esc <- map_m (fun d => rec0 (CRaw nb 0 (S d.(rarg)) d.(dbody))) mfix ;;
      if existsb (fun b : bool => b) esc then reject err_prefix_occ else
      rd <- map_m (fun d =>
              x <- occur_loop rec0 nb d.(rarg) 0
                     {| r_lets := repeat None nb; r_depth := nb; r_min := 0; r_genv := [] |}
                     d.(dbody) (S d.(rarg)) ;;
              _ <- allowed_fixpoint d x.1 ;;
              ret x) mfix ;;
      trees <- map_m (fun x => tree_of x.1) rd ;;
      check_bodies (run_rec nb (map rarg mfix) trees) nb (combine (combine mfix rd) trees) in
    match m init_state with
    | GOk _ _ => Accept
    | GReject msg => Reject msg
    | GFuel => OutOfFuel
    end.
End Checker.
End FixGuard.

Definition check_guard_gen (lookup : kername -> option global_decl)
  (retro : Retroknowledge.t) (fuel : nat) (b : FixCoFix) (n : nat)
  (mfix : mfixpoint term) : guard_result :=
  match b with
  | Fix => FixGuard.check_fix_block lookup retro fuel n mfix
  | CoFix => check_cofix_block lookup retro fuel n mfix
  end.

(** ** Erasure of the data the check does not read

  [strip] removes binder names and universe instances, and collapses every
  predicative sort to one fixed level.  Binder relevance and the sort
  qualities [sProp]/[sSProp] are kept, because the check reads relevance
  and sort qualities ([is_allowed_fixpoint]). *)

Definition strip_sort (s : sort) : sort :=
  match s with
  | sType _ => Sort.type0
  | sProp => sProp
  | sSProp => sSProp
  end.

Definition strip_name (na : aname) : aname := map_binder_annot (fun _ => nAnon) na.

Definition strip_context_decl (f : term -> term) (d : context_decl) : context_decl :=
  {| decl_name := strip_name d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Definition strip_predicate (f : term -> term) (p : predicate term) : predicate term :=
  {| pparams := map f p.(pparams);
     puinst := [];
     pcontext := map (strip_context_decl f) p.(pcontext);
     preturn := f p.(preturn) |}.

Definition strip_branch (f : term -> term) (br : branch term) : branch term :=
  {| bcontext := map (strip_context_decl f) br.(bcontext);
     bbody := f br.(bbody) |}.

Definition strip_def (f : term -> term) (d : def term) : def term :=
  {| dname := strip_name d.(dname);
     dtype := f d.(dtype);
     dbody := f d.(dbody);
     rarg := d.(rarg) |}.

Fixpoint strip (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar i => tVar i
  | tEvar n l => tEvar n (map strip l)
  | tSort s => tSort (strip_sort s)
  | tProd na A B => tProd (strip_name na) (strip A) (strip B)
  | tLambda na A b => tLambda (strip_name na) (strip A) (strip b)
  | tLetIn na b B u => tLetIn (strip_name na) (strip b) (strip B) (strip u)
  | tApp u v => tApp (strip u) (strip v)
  | tConst k _ => tConst k []
  | tInd ind _ => tInd ind []
  | tConstruct ind c _ => tConstruct ind c []
  | tCase ci p c brs =>
    tCase ci (strip_predicate strip p) (strip c) (map (strip_branch strip) brs)
  | tProj p c => tProj p (strip c)
  | tFix mfix idx => tFix (map (strip_def strip) mfix) idx
  | tCoFix mfix idx => tCoFix (map (strip_def strip) mfix) idx
  | tPrim p => tPrim (mapu_prim (fun _ => Level.lzero) strip p)
  end.

Definition strip_mfix (m : mfixpoint term) : mfixpoint term := map (strip_def strip) m.
