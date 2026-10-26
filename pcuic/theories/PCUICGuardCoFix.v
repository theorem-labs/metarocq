(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases
     PCUICGuardResult PCUICGuardReduce PCUICRecArgs.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * The guard checker for cofixpoints

  A port of the cofixpoint guard checker of the Rocq kernel
  ([codomain_is_coind], [check_one_cofix] and [check_cofix],
  kernel/inductive.ml) to PCUIC, as a total executable function
  [check_cofix_block].  The kernel code it is compared with below is that
  of Rocq 9.2 with two fixes: the type of each function is reduced in the
  block's outer context, where it lives, and not under the block's own
  binders (rocq-prover/rocq#22386, fixed by #22388); and a function of the
  block in the body of a nested cofixpoint that is not the nested block's
  main function is refused ([RecCallInNonMainMutual], #22392).  The port
  does both.

  The port differs from that kernel code in these ways.  All but the last
  refuse more than the kernel; the last accepts more.

  - Every head reduction is one [head_step] at a time ([PCUICGuardReduce]),
    and every part that a step discards is analysed as if the step had kept
    it, at the position where the step happened and with the same "already
    guarded" flag.  This takes the place of the kernel's [check_erased],
    whose list of erased positions does not cover every reduction rule (an
    unread argument of a fixpoint applied to a constructor, a dropped field
    of a projection, the unread constructor argument of a match on a known
    constructor).  A body is accepted only if a reduction that kept every
    part it drops would be accepted too.
  - In particular, when a fixpoint or cofixpoint is unfolded and the body it
    unfolds to names no function of its block, the other functions of the
    block are discarded as the terms [tFix mfix k] or [tCoFix mfix k], and
    each is analysed as if it were kept: a [tFix] is stuck, so it is
    refused where a function of the block occurs in it, and a [tCoFix] is a
    nested cofixpoint whose main function is [k], so the rule for non-main
    functions applies to the others.  This refuses productive bodies that
    the kernel accepts, for example, with [CoInductive R := mkR { hd : nat;
    tl : R }] (primitive projections),
    [cofix g : R := mkR 0 (tl (cofix h : R := mkR 1 g with h' : R := mkR 2 h' for h))]:
    unfolding [h] discards [tCoFix mfix 1], whose main function is [h'] and
    whose non-main function [h] names [g].
  - The variables of the outer context are opaque, including its local
    definitions: a codomain that is a local definition of the outer context
    is refused, where the kernel unfolds it ([let T := S in cofix f : T := …]).
  - A function of the block in a parameter of a constructor is refused (the
    kernel skips the parameters).  A function of the block in a parameter of
    a [match] is refused, as in the kernel, where the parameters occur in
    the expanded return clause.
  - A constructor is read in the recursive-argument tree of its position
    only if it is a constructor of that tree's inductive; otherwise it is
    refused.  A kept constructor always is (typing); a discarded part,
    analysed at the position where it was dropped, may have another type.
  - The kernel's anomalies (too many arguments for a constructor, a
    constructor index outside its tree, a missing declaration) are [Reject];
    a de Bruijn index outside the block's context is [Reject]; existential
    variables are [Reject].
  - Recursion is bounded by doubling fuel ([nfuel]): a fuel of [k] allows
    [2 ^ k] nested steps.  Exhaustion is [OutOfFuel], which is never caught
    and never turned into [Reject].
  - Accepts more: every constant with a body unfolds, including one whose
    body the kernel keeps opaque ([Qed]), because PCUIC has no opacity and
    its reduction unfolds it.  So with [Lemma idS : Stream -> Stream] closed
    by [Qed], the port accepts [cofix f : Stream := Cons 0 (idS f)], which
    the kernel refuses ([idS f] has an opaque constant at its head).

  Positions in a body are counted as in PCUIC: at a point under [d] binders
  of the body, the functions of the block are [tRel d] ... [tRel (d + nb - 1)]
  ([nb] the size of the block), and the variables of the outer context (of
  length [nctx]) follow them. *)

Local Notation "x <-? m ;; f" := (rt_bind m (fun x => f))
  (at level 100, m at next level, right associativity).

Definition err_unguarded := "cofixpoint: a corecursive call is not guarded by a constructor (UnguardedRecursiveCall)".
Definition err_nested := "cofixpoint: a corecursive call has a corecursive call in its arguments (NestedRecursiveOccurrences)".
Definition err_nonrec := "cofixpoint: a corecursive call in a parameter or a non-recursive argument of a constructor (RecCallInNonRecArgOfConstructor)".
Definition err_typeabs := "cofixpoint: a corecursive call in the type of an abstraction (RecCallInTypeOfAbstraction)".
Definition err_typedef := "cofixpoint: a corecursive call in the type of a nested cofixpoint (RecCallInTypeOfDef)".
Definition err_nonmain := "cofixpoint: a corecursive call in a function of a nested cofixpoint that is not its main function (RecCallInNonMainMutual)".
Definition err_casepred := "cofixpoint: a corecursive call in the return clause or a parameter of a match (RecCallInCasePred)".
Definition err_casearg := "cofixpoint: a corecursive call in the scrutinee of a match (RecCallInCaseArg)".
Definition err_casefun := "cofixpoint: a corecursive call in an argument of a match (RecCallInCaseFun)".
Definition err_retpred := "cofixpoint: the return clause of a match is not a coinductive type (ReturnPredicateNotCoInductive)".
Definition err_notguarded := "cofixpoint: the body is not in guarded form (NotGuardedForm)".
Definition err_codomain := "cofixpoint: the codomain is not a coinductive type (CodomainNotInductiveType)".
Definition err_ill_typed := "cofixpoint: too many arguments applied to a constructor".
Definition err_ctor_tree := "cofixpoint: a constructor index is outside the recursive-argument tree".
Definition err_ind_missing := "cofixpoint: an inductive type is not declared".
Definition err_tree_index := "cofixpoint: an inductive index is outside its block".
Definition err_index := "cofixpoint: a cofixpoint index is out of range".
Definition err_lambda_args := "cofixpoint: an applied abstraction in weak-head normal form".
Definition err_evar := "cofixpoint: the guard checker does not handle existential variables".
Definition err_scope := "cofixpoint: a de Bruijn index escapes the block's context".
Definition err_ctor_type := "cofixpoint: a constructor of another type in a guarded position".

Definition gr_of_rt {X} (r : rt_answer X) (k : X -> guard_result) : guard_result :=
  match r with
  | RtOk x => k x
  | RtBad msg => Reject msg
  | RtFuel => OutOfFuel
  end.

Section CoFix.
  Context (lookup : kername -> option global_decl) (retro : Retroknowledge.t) (fuel : nat).

  (** ** Reduction of types

    The weak-head normal form of a type, by [head_step] with every variable
    opaque.  It is used on the types of the block's functions (in the outer
    context), on declarations, and on the return clause of a [match].  The
    parts these steps discard are not analysed: the types of the functions
    and the declarations mention no function of the block, and a return
    clause that mentions one is refused ([err_casepred]), so every part they
    drop mentions none either. *)
  Definition whd_red (t : term) : red_answer :=
    match whd_plain lookup retro fuel t with
    | WhdOk t' _ => RdWhnf t'
    | WhdBad msg => RdBad msg
    | WhdFuel => RdFuel
    end.

  Definition whd_rt (t : term) : rt_answer term := rt_of_red (whd_red t).

  (** [codomain_is_coind]: the inductive at the head of the codomain of [ty],
      which must be coinductive ([find_coinductive]).  Where the kernel
      catches [Not_found] (not an inductive, not coinductive, not declared),
      the answer is [err_codomain]; running out of fuel stays [RtFuel]. *)
  Definition codomain_is_coind (ty : term) : rt_answer inductive :=
    nfuel (fun (rec : term -> rt_answer inductive) (t : term) =>
      t' <-? whd_rt t ;;
      match t' with
      | tProd _ _ b => rec b
      | _ =>
        match fst (decompose_app t') with
        | tInd ind _ =>
          match lookup (inductive_mind ind) with
          | Some (InductiveDecl mib) =>
            match mib.(ind_finite), nth_error mib.(ind_bodies) (inductive_ind ind) with
            | CoFinite, Some _ => RtOk ind
            | _, _ => RtBad err_codomain
            end
          | _ => RtBad err_codomain
          end
        | _ => RtBad err_codomain
        end
      end) fuel (fun _ => RtFuel) ty.

  (** [lookup_subterms]: the recursive-argument tree of [ind]. *)
  Definition lookup_subterms (ind : inductive) : rt_answer wf_paths :=
    p <-? ind_block_recargs whd_red lookup retro fuel (inductive_mind ind) ;;
    rt_of_option err_tree_index (nth_error p.2 (inductive_ind ind)).

  (** [inter_wf_paths] *)
  Definition inter_wf_paths (t t' : wf_paths) : rt_answer wf_paths :=
    rt_inter recarg_eqb (fun r r' => if recarg_eqb r r' then Some r else None) Norec fuel t t'.

  (** The weak-head normal form of [t] with its leading abstractions peeled
      ([whd_decompose_lambda_decls]): their number and the rest. *)
  Definition whd_decompose_lambda (t : term) : rt_answer (nat * term) :=
    nfuel (fun (rec : nat * term -> rt_answer (nat * term)) (x : nat * term) =>
      t' <-? whd_rt x.2 ;;
      match t' with
      | tLambda _ _ b => rec (S x.1, b)
      | _ => RtOk (x.1, t')
      end) fuel (fun _ => RtFuel) (0, t).

  (** The same for products ([whd_decompose_prod]). *)
  Definition whd_decompose_prod (t : term) : rt_answer (nat * term) :=
    nfuel (fun (rec : nat * term -> rt_answer (nat * term)) (x : nat * term) =>
      t' <-? whd_rt x.2 ;;
      match t' with
      | tProd _ _ b => rec (S x.1, b)
      | _ => RtOk (x.1, t')
      end) fuel (fun _ => RtFuel) (0, t).

  (** [restrict_spec] on the spec [Subterm (∅, Strict, tree)], for the
      return clause [p] (closed by its context) of a [match]: [Some tree']
      for [Subterm (_, _, tree')], [None] for [Not_subterm]. *)
  Definition restrict_tree (tree : wf_paths) (p : term) : rt_answer (option wf_paths) :=
    x <-? whd_decompose_lambda p ;;
    let '(nabs, ar) := x in
    (* a return clause that does not depend on its context restricts nothing *)
    if noccur_between 0 nabs ar then RtOk (Some tree) else (
    y <-? whd_decompose_prod ar ;;
    let '(nprods, s) := y in
    match decompose_app s with
    | (tInd ind _, args) =>
      c <-? has_constant_parameters whd_red lookup retro fuel [] nabs nprods ind args ;;
      if c.1 then RtOk (Some tree) else (
      r <-? get_recargs_approx whd_red lookup retro fuel [] tree ind args ;;
      tree' <-? inter_wf_paths tree r.1 ;;
      RtOk (Some tree'))
    | _ => RtOk None
    end).

  (** ** The analysis of a body ([check_one_cofix]) *)

  Context (nctx nb : nat).

  (** No function of the block occurs in [t], at depth [d]. *)
  Definition noocc (d : nat) (t : term) : bool := noccur_between d nb t.

  (** The requests of the analysis: [CfCheck g d tree vlra t] is the kernel's
      [check_rec_call] on [t] at depth [d], with [g] the "already guarded"
      flag, [tree] the recursive-argument tree of the expected type and
      [vlra] its subtrees; [CfWhd] is the same request after the noccurrence
      test, while [t] is being reduced one step at a time. *)
  Inductive cf_call :=
  | CfCheck (g : bool) (d : nat) (tree : wf_paths) (vlra : list (list wf_paths)) (t : term)
  | CfWhd (g : bool) (d : nat) (tree : wf_paths) (vlra : list (list wf_paths)) (t : term).

  Section Step.
    Context (rec : cf_call -> guard_result).

    (** [process_args_of_constr]: the arguments of a constructor after its
        parameters, against the trees of the constructor's arguments. *)
    Fixpoint cf_ctor_args (d : nat) (args : list term) (lra : list wf_paths) : guard_result :=
      match args, lra with
      | [], _ => Accept
      | t :: args, rar :: lra =>
        gr_of_rt (is_norec_path fuel rar) (fun norec =>
          if norec then
            if noocc d t then cf_ctor_args d args lra else Reject err_nonrec
          else
            gr_of_rt (dest_subterms fuel rar) (fun vl =>
              gr_and (rec (CfCheck true d rar vl t)) (cf_ctor_args d args lra)))
      | _ :: _, [] => Reject err_ill_typed
      end.

    (** The analysis of a weak-head normal form [t]. *)
    Definition cf_whnf (g : bool) (d : nat) (tree : wf_paths) (vlra : list (list wf_paths))
      (t : term) : guard_result :=
      let '(hd, args) := decompose_app t in
      match hd with
      | tRel p =>
        if Nat.leb (d + nb + nctx) p then Reject err_scope
        else if Nat.leb d p && Nat.ltb p (d + nb) then
          (* a corecursive call: guarded, and no nested corecursive call *)
          if negb g then Reject err_unguarded
          else if forallb (noocc d) args then Accept
          else Reject err_nested
        else Reject err_notguarded
      | tConstruct ind k _ =>
        (* The tree is the one of the position.  Typing makes a kept constructor
           a constructor of the tree's inductive; a discarded part is analysed
           at the position where it was dropped, so its type can differ, and
           reading its arguments in another inductive's tree would be wrong. *)
        gr_of_rt (dest_recarg fuel tree) (fun r =>
          match r with
          | Mrec (RecArgInd ind') =>
            if negb (eqb ind' ind) then Reject err_ctor_type else
            match nth_error vlra k with
            | None => Reject err_ctor_tree
            | Some lra =>
              match lookup (inductive_mind ind) with
              | Some (InductiveDecl mib) =>
                if forallb (noocc d) (firstn mib.(ind_npars) args) then
                  cf_ctor_args d (skipn mib.(ind_npars) args) lra
                else Reject err_nonrec
              | _ => Reject err_ind_missing
              end
            end
          | _ => Reject err_ctor_type
          end)
      | tLambda _ A b =>
        match args with
        | [] => if noocc d A then rec (CfCheck g (S d) tree vlra b) else Reject err_typeabs
        | _ :: _ => Reject err_lambda_args
        end
      | tCoFix mfix i =>
        if negb (forallb (noocc d) args) then Reject err_unguarded
        else if negb (forallb (fun dd => noocc d dd.(dtype)) mfix) then Reject err_typedef
        else
          let nbi := #|mfix| in
          match nth_error mfix i with
          | None => Reject err_index
          | Some main =>
            let others := except_nth i mfix in
            if forallb (fun dd => noocc (d + nbi) dd.(dbody)) others then
              rec (CfCheck g (d + nbi) tree vlra main.(dbody))
            else Reject err_nonmain
          end
      | tCase ci p c brs =>
        let pexp := it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn) in
        gr_of_rt (restrict_tree tree pexp) (fun otree =>
          match otree with
          | None => Reject err_retpred
          | Some tree' =>
            if negb (forallb (noocc d) p.(pparams) && noocc d pexp) then Reject err_casepred
            else if negb (noocc d c) then Reject err_casearg
            else if negb (forallb (noocc d) args) then Reject err_casefun
            else
              gr_of_rt (dest_subterms fuel tree') (fun vlra' =>
                gr_list (fun br =>
                  rec (CfCheck g d tree' vlra'
                         (it_mkLambda_or_LetIn (inst_case_branch_context p br) br.(bbody))))
                  brs)
          end)
      | tEvar _ _ => Reject err_evar
      | tVar _ | tSort _ | tProd _ _ _ | tLetIn _ _ _ _ | tApp _ _ | tConst _ _ | tInd _ _
      | tFix _ _ | tProj _ _ | tPrim _ => Reject err_notguarded
      end.

    Definition cf_step (c : cf_call) : guard_result :=
      match c with
      | CfCheck g d tree vlra t =>
        if noocc d t then Accept else rec (CfWhd g d tree vlra t)
      | CfWhd g d tree vlra t =>
        match head_step lookup retro [] t with
        | Stuck => cf_whnf g d tree vlra t
        | Stepped t' parts =>
          (* Every discarded part is analysed where the step happened.  The
             result is [gr_and] of the parts and of the reduct, written so
             that, when the parts are accepted, the analysis of the reduct is
             a tail call: the extracted checker then follows a long chain of
             head steps in constant stack. *)
          match gr_list (fun part => rec (CfCheck g d tree vlra part)) parts with
          | Accept => rec (CfWhd g d tree vlra t')
          | OutOfFuel => OutOfFuel
          | Reject msg => gr_and (Reject msg) (rec (CfWhd g d tree vlra t'))
          end
        | StepBad msg => Reject msg
        end
      end.
  End Step.

  Definition cf_check : cf_call -> guard_result :=
    nfuel cf_step fuel (fun _ => OutOfFuel).

  (** [check_one_cofix] on the body [body] of a function whose codomain has
      the tree [tree]. *)
  Definition check_one_cofix (tree : wf_paths) (body : term) : guard_result :=
    gr_of_rt (dest_subterms fuel tree) (fun vlra => cf_check (CfCheck false 0 tree vlra body)).
End CoFix.

(** [check_cofix]: every function [dd] of the block [mfix], checked in an
    outer context of length [n].  Its type lives in the outer context and its
    body under the block's [#|mfix|] binders. *)
Definition check_cofix_block (lookup : kername -> option global_decl)
  (retro : Retroknowledge.t) (fuel : nat) (n : nat) (mfix : mfixpoint term) : guard_result :=
  let nb := #|mfix| in
  gr_list (fun dd =>
    if negb (closedn n dd.(dtype) && closedn (n + nb) dd.(dbody)) then Reject err_scope else
    gr_of_rt (codomain_is_coind lookup retro fuel dd.(dtype)) (fun ind =>
      gr_of_rt (lookup_subterms lookup retro fuel ind) (fun tree =>
        check_one_cofix lookup retro fuel n nb tree dd.(dbody)))) mfix.
