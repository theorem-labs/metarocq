(** Regression tests: the executable guard check refuses fixpoint blocks whose
    [match] nodes carry branch contexts or predicate parameters that do not
    agree with the inductive declaration.

    PCUIC never renumbers the contexts stored in a branch ([bcontext]): [lift],
    [subst] and the reduction rules keep them as they are, and ι-reduction puts
    their [let] bodies into the branch body.  A free de Bruijn index in such a
    [let] body is therefore read at the site of the [match], where it can
    denote the block's own recursive function.  Typing excludes this ([type_Case]
    pins every context to the declaration), but the guard check runs on raw
    syntax, so the executable check [check_guard_impl] first tests case
    well-formedness ([wf_cases_mfix]) and only then runs the syntactic check
    [check_guard_gen].

    Each block below is one such counterexample, labelled here:
    - CE-A: [fix f (n : nat) := match O with O (b := f n) => b | S k => O end],
      where the [O] branch has a [let] in its context that [nat] does not
      declare; ι-reduction turns the block into [fix f n := f n].
    - CE-C: a block over [L := leaf | node (a : L) (b := a)] whose inner branch
      has the [let] body [node leaf] in place of [a]; the check would read
      [b] as a subterm, but ι-reduction gives [f (node leaf)].
    - CE-A': a [match] on [W (a b : nat) := w : let y := a in let z := b in W a b]
      with no predicate parameters; its branch context is the declared one,
      but without parameters its [let] bodies stay free and denote [f] and [n]
      at the site, so ι-reduction again gives [fix f n := f n].

    Two last sections test other refusals of the syntactic check: a relevant
    fixpoint whose recursive argument's inductive eliminates only into
    [SProp], and a recursive call on a value taken out of a coinductive.

    Gallina cannot write these terms, so they are built as PCUIC terms over an
    environment obtained by quoting the Gallina inductives.  Every assertion is
    an [Example] proved by [vm_compute; reflexivity]. *)
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Template Require Ast.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICProgram
     PCUICGuardChecker PCUICGuardClosure.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl.

Local Open Scope bs_scope.

(** ** The environment *)

Inductive L : Set :=
| leaf : L
| node : forall a : L, let b := a in L.

Inductive W (a b : nat) : Set :=
| w : let y := a in let z := b in W a b.

Inductive sP : SProp :=
| sp0 : sP
| spS : sP -> sP.

Inductive sEmpty : SProp := .

MetaRocq Quote Recursively Definition q_env := (L, W, sP, sEmpty).
MetaRocq Quote Definition q_nat := nat.
MetaRocq Quote Definition q_L := L.
MetaRocq Quote Definition q_W := W.
MetaRocq Quote Definition q_sP := sP.
MetaRocq Quote Definition q_sEmpty := sEmpty.

Definition Σ : global_env := trans_env_env (trans_global_env q_env.1).

Definition no_ind : inductive :=
  {| inductive_mind := (MPfile [], ""); inductive_ind := 0 |}.

(** The inductive named by a quoted [tInd]. *)
Definition ind_of (t : Ast.term) : inductive :=
  match t with Ast.tInd i _ => i | _ => no_ind end.

Definition i_nat := ind_of q_nat.
Definition i_L := ind_of q_L.
Definition i_W := ind_of q_W.
Definition i_sP := ind_of q_sP.
Definition i_sEmpty := ind_of q_sEmpty.

(** The quoted terms are the inductives, and [Σ] declares each of them. *)
Definition declared (ind : inductive) : bool :=
  match lookup_inductive Σ ind with Some _ => true | None => false end.

Example i_nat_found : declared i_nat = true.
Proof. vm_compute. reflexivity. Qed.
Example i_L_found : declared i_L = true.
Proof. vm_compute. reflexivity. Qed.
Example i_W_found : declared i_W = true.
Proof. vm_compute. reflexivity. Qed.
Example i_sP_found : declared i_sP = true.
Proof. vm_compute. reflexivity. Qed.
Example i_sEmpty_found : declared i_sEmpty = true.
Proof. vm_compute. reflexivity. Qed.

(** The contexts a [match] must carry, read from [Σ] through the same lookup
    as [wf_cases]. *)
Definition pctx (ind : inductive) : context :=
  match lookup_inductive Σ ind with
  | Some (mdecl, idecl) => ind_predicate_context ind mdecl idecl
  | None => []
  end.

Definition bctx (ind : inductive) (c : nat) : context :=
  match lookup_inductive Σ ind with
  | Some (mdecl, idecl) =>
    match nth_error idecl.(ind_ctors) c with
    | Some cdecl => cstr_branch_context ind mdecl cdecl
    | None => []
    end
  | None => []
  end.

(** The innermost declaration of [ctx] with its [let] body replaced. *)
Definition with_first_body (body : term) (ctx : context) : context :=
  match ctx with
  | d :: ctx' =>
    {| decl_name := d.(decl_name); decl_body := Some body; decl_type := d.(decl_type) |}
      :: ctx'
  | [] => []
  end.

(** ** Term fixtures *)

Definition nm (s : ident) : aname := {| binder_name := nNamed s; binder_relevance := Relevant |}.
Definition tNat := tInd i_nat [].
Definition tO := tConstruct i_nat 0 [].
Definition tL := tInd i_L [].
Definition tleaf := tConstruct i_L 0 [].
Definition tnode := tConstruct i_L 1 [].

(** [fix f (x : A) {struct x} : A := body], with [body] under [x]. *)
Definition block (A : term) (body : term) : mfixpoint term :=
  [{| dname := nm "f"; dtype := tProd (nm "x") A A; dbody := tLambda (nm "x") A body;
      rarg := 0 |}].

(** The executable check at the top level, in an empty local context. *)
Definition exec_check (m : mfixpoint term) : bool := check_guard_impl Fix (empty_ext Σ) [] m.

(** The syntactic check alone, on the stripped block, with the same fuel. *)
Definition syn_check (m : mfixpoint term) : guard_result :=
  check_guard_gen (lookup_env Σ) Σ.(retroknowledge) guard_fuel Fix 0 (strip_mfix m).

(** ** CE-A: a [let] in a branch context that [nat] does not declare

    [match O return nat with O (b := f n) => b | S k => O end] inside
    [fix f (n : nat)].  At the [match], the context is [n; f], so the [let]
    body [tApp (tRel 1) (tRel 0)] means [f n].  The [O] branch's declared
    context is empty; the one wrong change is the added [let]. *)

Definition ci_nat : case_info := {| ci_ind := i_nat; ci_npar := 0; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition p_nat : predicate term :=
  {| pparams := []; puinst := []; pcontext := pctx i_nat; preturn := tNat |}.

Definition ce_a_case (ctx_O : context) : term :=
  tCase ci_nat p_nat tO
    [ {| bcontext := ctx_O; bbody := tRel 0 |};
      {| bcontext := bctx i_nat 1; bbody := tO |} ].

Definition ce_a_bad_ctx : context := vdef (nm "b") (tApp (tRel 1) (tRel 0)) tNat :: bctx i_nat 0.

Definition t_a := ce_a_case ce_a_bad_ctx.
Definition ce_a := block tNat t_a.

Example ce_a_case_not_wf : wf_cases Σ t_a = false.
Proof. vm_compute. reflexivity. Qed.
Example ce_a_block_not_wf : wf_cases_mfix Σ ce_a = false.
Proof. vm_compute. reflexivity. Qed.
(** The syntactic check refuses this block by scope as well: the added [let]
    body is not closed in the branch context, which is an index outside the
    block's context. *)
Example ce_a_syntactic_rejects : syn_check ce_a = Reject FixGuard.err_scope.
Proof. vm_compute. reflexivity. Qed.
Example ce_a_refused : exec_check ce_a = false.
Proof. vm_compute. reflexivity. Qed.

(** ** CE-C: a wrong [let] body in a declared position

    [L := leaf | node (a : L) (b := a)], and the block
    [fix f (n : L) : L := match n with leaf => leaf
       | node k (b0 := k) => match node k with leaf => leaf
                               | node a (b := node leaf) => f b end end].
    The inner branch declares [b := a]; the one wrong change is the body
    [node leaf].  A check that took [b := a] from the declaration would see
    [f] applied to a subterm of [n]; ι-reduction uses [node leaf] and gives
    [f (node leaf)]. *)

Definition ci_L : case_info := {| ci_ind := i_L; ci_npar := 0; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition p_L : predicate term :=
  {| pparams := []; puinst := []; pcontext := pctx i_L; preturn := tL |}.

(** Inside the inner branch the context is [b; a; b0; k; n; f]. *)
Definition ce_c_body (inner_ctx : context) : term :=
  tCase ci_L p_L (tRel 0)
    [ {| bcontext := bctx i_L 0; bbody := tleaf |};
      {| bcontext := bctx i_L 1;
         bbody :=
           tCase ci_L p_L (tApp tnode (tRel 1))
             [ {| bcontext := bctx i_L 0; bbody := tleaf |};
               {| bcontext := inner_ctx; bbody := tApp (tRel 5) (tRel 0) |} ] |} ].

Definition ce_c_bad_ctx : context := with_first_body (tApp tnode tleaf) (bctx i_L 1).

Definition ce_c := block tL (ce_c_body ce_c_bad_ctx).

(** The syntactic check refuses this block on its own as well (the recursive
    call's argument is a [let]-bound variable, not a subterm), so only the
    refusal by case well-formedness is asserted for it. *)
Example ce_c_block_not_wf : wf_cases_mfix Σ ce_c = false.
Proof. vm_compute. reflexivity. Qed.
Example ce_c_refused : exec_check ce_c = false.
Proof. vm_compute. reflexivity. Qed.

(** ** CE-A': no predicate parameters for a two-parameter inductive

    [match w O O return nat with w (y := a) (z := b) => y z end] inside
    [fix f (n : nat)], with [pparams = []].  The branch context is exactly the
    declared one, whose [let] bodies refer to the parameters [a] and [b].
    Without parameters to substitute, they stay free: at the [match] they
    denote [f] and [n], so the branch body [y z] reduces to [f n].  The one
    wrong change is the empty [pparams] (the declaration has two). *)

Definition ci_W : case_info := {| ci_ind := i_W; ci_npar := 2; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition p_W (pars : list term) : predicate term :=
  {| pparams := pars; puinst := []; pcontext := pctx i_W; preturn := tNat |}.

Definition ce_a'_case (pars : list term) : term :=
  tCase ci_W (p_W pars) (mkApps (tConstruct i_W 0 []) [tO; tO])
    [ {| bcontext := bctx i_W 0; bbody := tApp (tRel 1) (tRel 0) |} ].

Definition t_a' := ce_a'_case [].
Definition ce_a' := block tNat t_a'.

Example ce_a'_case_not_wf : wf_cases Σ t_a' = false.
Proof. vm_compute. reflexivity. Qed.
Example ce_a'_block_not_wf : wf_cases_mfix Σ ce_a' = false.
Proof. vm_compute. reflexivity. Qed.
(** The syntactic check refuses this block by scope as well: without
    parameters, the declared [let] bodies are not closed in the branch
    context. *)
Example ce_a'_syntactic_rejects : syn_check ce_a' = Reject FixGuard.err_scope.
Proof. vm_compute. reflexivity. Qed.
Example ce_a'_refused : exec_check ce_a' = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Control: the same blocks with the declared contexts and parameters

    Each is case-well-formed, so the refusals above come from the one wrong
    change, not from the environment or the lookup. *)

Definition ce_a_ok := block tNat (ce_a_case (bctx i_nat 0)).
Definition ce_c_ok := block tL (ce_c_body (bctx i_L 1)).
Definition ce_a'_ok := block tNat (ce_a'_case [tO; tO]).

Example ce_a_ok_case_wf : wf_cases Σ (ce_a_case (bctx i_nat 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Example ce_a_ok_wf : wf_cases_mfix Σ ce_a_ok = true.
Proof. vm_compute. reflexivity. Qed.
Example ce_c_ok_wf : wf_cases_mfix Σ ce_c_ok = true.
Proof. vm_compute. reflexivity. Qed.
Example ce_a'_ok_case_wf : wf_cases Σ (ce_a'_case [tO; tO]) = true.
Proof. vm_compute. reflexivity. Qed.
Example ce_a'_ok_wf : wf_cases_mfix Σ ce_a'_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** With correct contexts, the constant blocks pass the whole check. *)
Example ce_a_ok_accepted : exec_check ce_a_ok = true.
Proof. vm_compute. reflexivity. Qed.
Example ce_a'_ok_accepted : exec_check ce_a'_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** ** A relevant fixpoint on an inductive that eliminates only into [SProp]

    [sP : SProp] has two constructors, so it can be eliminated only into
    [SProp].  [fix g (x : sP) {struct x} : nat := O] is a relevant fixpoint
    recursing on it; Rocq refuses to define it even with guard checking off,
    so it is written as a PCUIC term.  The syntactic check refuses it.  Its
    twin [fix g (x : sP) {struct x} : sP := x] is an irrelevant fixpoint and
    is accepted. *)

Definition rel_name (r : relevance) (s : ident) : aname :=
  {| binder_name := nNamed s; binder_relevance := r |}.
Definition tsP := tInd i_sP [].

Definition sp_block (r : relevance) (ret body : term) : mfixpoint term :=
  [{| dname := rel_name r "g"; dtype := tProd (rel_name Irrelevant "x") tsP ret;
      dbody := tLambda (rel_name Irrelevant "x") tsP body; rarg := 0 |}].

Definition sp_relevant := sp_block Relevant tNat tO.
Definition sp_irrelevant := sp_block Irrelevant tsP (tRel 0).

Example sp_relevant_wf : wf_cases_mfix Σ sp_relevant = true.
Proof. vm_compute. reflexivity. Qed.
Example sp_relevant_syntactic_rejects : syn_check sp_relevant = Reject FixGuard.err_elim.
Proof. vm_compute. reflexivity. Qed.
Example sp_relevant_refused : exec_check sp_relevant = false.
Proof. vm_compute. reflexivity. Qed.
Example sp_irrelevant_syntactic_accepts : syn_check sp_irrelevant = Accept.
Proof. vm_compute. reflexivity. Qed.
Example sp_irrelevant_accepted : exec_check sp_irrelevant = true.
Proof. vm_compute. reflexivity. Qed.

(** [sEmpty : SProp] has no constructor, so it eliminates into every sort;
    a relevant fixpoint recursing on it is still refused, because the
    kernel's test is on the inductive's sort, not on its eliminations. *)
Definition tsEmpty := tInd i_sEmpty [].
Definition se_block (r : relevance) (ret body : term) : mfixpoint term :=
  [{| dname := rel_name r "g"; dtype := tProd (rel_name Irrelevant "x") tsEmpty ret;
      dbody := tLambda (rel_name Irrelevant "x") tsEmpty body; rarg := 0 |}].

Definition se_relevant := se_block Relevant tNat tO.
Definition se_irrelevant := se_block Irrelevant tsEmpty (tRel 0).

Example sEmpty_eliminates_anywhere :
  option_map (fun p => p.2.(ind_kelim)) (lookup_inductive Σ i_sEmpty) = Some IntoAny.
Proof. vm_compute. reflexivity. Qed.
Example se_relevant_syntactic_rejects : syn_check se_relevant = Reject FixGuard.err_elim.
Proof. vm_compute. reflexivity. Qed.
Example se_relevant_refused : exec_check se_relevant = false.
Proof. vm_compute. reflexivity. Qed.
Example se_irrelevant_syntactic_accepts : syn_check se_irrelevant = Accept.
Proof. vm_compute. reflexivity. Qed.

(** ** A recursive call on a value taken out of a coinductive

    [T := C : Str T -> T] nests [T] in the coinductive [Str].  In
    [fix t_f (x : T) : nat := match x with C y => match y with SCons t _ => t_f t end end]
    the call's argument [t] comes out of a [match] on [y : Str T], a value
    of a coinductive type, so it is not a structural subterm of [x].
    The inner [match] returns [nat], which does not mention [y], so PCUIC's
    [type_Case] allows it and case well-formedness accepts the block: the
    syntactic check must refuse it on its own.

    Rocq refuses this fixpoint, so its term is elaborated with guard checking
    off only to quote it: no constant holding it is defined. *)

CoInductive Str (A : Type) := SCons : A -> Str A -> Str A.
(* [T] needs no induction principle for its nesting in [Str]. *)
Set Warnings "-register-all".
Inductive T := C : Str T -> T.
Set Warnings "register-all".

Unset Guard Checking.
MetaRocq Quote Recursively Definition q_tf :=
  (fix t_f (x : T) : nat :=
     match x with C y => match y with SCons t _ => t_f t end end).
Set Guard Checking.

Definition Σ_tf : global_env := trans_env_env (trans_global_env q_tf.1).

(** The fixpoint block of the quoted term. *)
Definition tf_block : mfixpoint term :=
  match trans (trans_global_env q_tf.1) q_tf.2 with
  | tFix mfix _ => mfix
  | _ => []
  end.

Example tf_block_one : #|tf_block| = 1.
Proof. vm_compute. reflexivity. Qed.
Example tf_block_wf : wf_cases_mfix Σ_tf tf_block = true.
Proof. vm_compute. reflexivity. Qed.
Example tf_syntactic_rejects :
  check_guard_gen (lookup_env Σ_tf) Σ_tf.(retroknowledge) guard_fuel Fix 0 (strip_mfix tf_block)
  = Reject FixGuard.err_illegal.
Proof. vm_compute. reflexivity. Qed.
Example tf_refused : check_guard_impl Fix (empty_ext Σ_tf) [] tf_block = false.
Proof. vm_compute. reflexivity. Qed.

(** ** A recursive call on a field projected out of a coinductive

    The same nesting with a negative coinductive record [PStr] and primitive
    projections: [TP := CP : PStr TP -> TP] and
    [fix tp_f (x : TP) : nat := match x with CP y => tp_f (pshd TP y) end].
    The call's argument is a field of [y : PStr TP], a value of a
    coinductive type, taken by a projection rather than a [match], so it is
    not a structural subterm of [x] either.  Case well-formedness does not
    refuse this block, so the check itself must.

    The controls have the same shapes on records declared with [Record] (so
    [BiFinite], not coinductive): [TR := CR : BoxR TR -> TR], where [BoxR]
    has primitive projections and [tr_g] calls itself on [bget TR y], and
    [TM := CM : BoxM TM -> TM], where [BoxM] has none and [tr_m] calls itself
    on the field taken by a [match] on [y].  Rocq accepts both.  A
    [BiFinite] record is not recursive, so it has no infinite values, and a
    subterm through it is a structural subterm. *)

Set Primitive Projections.
CoInductive PStr (A : Set) : Set := PSCons { pshd : A; pstl : PStr A }.
Record BoxR (A : Set) : Set := mkBR { bget : A }.
Unset Primitive Projections.
Record BoxM (A : Set) : Set := mkBM { bgm : A }.
Set Warnings "-register-all".
Inductive TP : Set := CP : PStr TP -> TP.
Inductive TR : Set := CR : BoxR TR -> TR.
Inductive TM : Set := CM : BoxM TM -> TM.
Set Warnings "register-all".

Unset Guard Checking.
MetaRocq Quote Recursively Definition q_tp :=
  (fix tp_f (x : TP) : nat := match x with CP y => tp_f (pshd TP y) end).
Set Guard Checking.
MetaRocq Quote Recursively Definition q_tr :=
  (fix tr_g (x : TR) : nat := match x with CR y => tr_g (bget TR y) end).
MetaRocq Quote Recursively Definition q_trm :=
  (fix tr_m (x : TM) : nat := match x with CM y => match y with mkBM t => tr_m t end end).

(** The fixpoint block of a quoted term. *)
Definition fix_block (p : Ast.Env.global_env * Ast.term) : mfixpoint term :=
  match trans (trans_global_env p.1) p.2 with
  | tFix mfix _ => mfix
  | _ => []
  end.

Definition Σ_tp : global_env := trans_env_env (trans_global_env q_tp.1).
Definition tp_block : mfixpoint term := fix_block q_tp.
Definition Σ_tr : global_env := trans_env_env (trans_global_env q_tr.1).
Definition tr_block : mfixpoint term := fix_block q_tr.
Definition Σ_trm : global_env := trans_env_env (trans_global_env q_trm.1).
Definition trm_block : mfixpoint term := fix_block q_trm.

Example tp_block_one : #|tp_block| = 1.
Proof. vm_compute. reflexivity. Qed.
Example tp_syntactic_rejects :
  check_guard_gen (lookup_env Σ_tp) Σ_tp.(retroknowledge) guard_fuel Fix 0 (strip_mfix tp_block)
  = Reject FixGuard.err_illegal.
Proof. vm_compute. reflexivity. Qed.
Example tp_refused : check_guard_impl Fix (empty_ext Σ_tp) [] tp_block = false.
Proof. vm_compute. reflexivity. Qed.

Example tr_block_one : #|tr_block| = 1.
Proof. vm_compute. reflexivity. Qed.
Example tr_syntactic_accepts :
  check_guard_gen (lookup_env Σ_tr) Σ_tr.(retroknowledge) guard_fuel Fix 0
    (strip_mfix tr_block) = Accept.
Proof. vm_compute. reflexivity. Qed.
Example trm_block_one : #|trm_block| = 1.
Proof. vm_compute. reflexivity. Qed.
Example trm_syntactic_accepts :
  check_guard_gen (lookup_env Σ_trm) Σ_trm.(retroknowledge) guard_fuel Fix 0
    (strip_mfix trm_block) = Accept.
Proof. vm_compute. reflexivity. Qed.
