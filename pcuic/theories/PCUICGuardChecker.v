(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICClosed.
From MetaRocq.PCUIC Require Export PCUICGuardResult.

From Stdlib Require Import ssreflect ssrbool.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * An executable guard checker for PCUIC (v0)

  [check_guard_gen] is a total, purely syntactic function that decides a
  (deliberately very restrictive) sufficient condition for a fixpoint or
  cofixpoint block to be guarded.  No reduction is performed and the
  retroknowledge [retro] is not consulted; the environment [lookup] is read
  only for declarations of inductive types.  Whatever the rule is not sure
  of, it refuses: it never accepts a block that Rocq's kernel refuses.

  The rule, for a block [mfix] checked in a context of length [n]:

  - Fix: the recursive argument's type in [dtype] must be an inductive type
    of [lookup] that can be eliminated into the fixpoint's relevance (an
    [SProp] inductive with only [SProp] elimination refuses a relevant
    fixpoint, as the kernel's [FixpointOnNonEliminable] does).  The body of
    each definition [d] must be a prefix of [rarg d + 1] lambda abstractions
    (interleaved [let]s are allowed and do not count, as [rarg] counts
    assumptions only).  The innermost of those binders is the *recursive
    parameter*.  It may be matched on, but it is NOT itself a valid
    recursive-call argument.  In a branch of a [tCase] on an inductive (not
    coinductive) type whose scrutinee is the recursive parameter, or a
    variable already known to be a subterm, an
    assumption binder whose type is an application of an inductive of the
    scrutinee's mutual block is a *subterm variable* (the kernel's recursive
    constructor arguments); the other binders of the branch context, [let]s
    included, are not.  Every occurrence of a function of the block must then
    be of the form [mkApps (tRel j) args] with [#|args| > rarg] and
    [nth rarg args] a subterm variable.
  - CoFix: the body of each definition must be a (possibly empty) prefix of
    lambdas and [let]s followed by a constructor application; a function of
    the block may occur only as the head of a recursive argument of such a
    constructor application (one whose type in the constructor's declaration
    is an inductive of its own mutual block), or, recursively, under a nested
    one.  Parameters and non-recursive arguments must not mention the block,
    as the kernel's [RecCallInNonRecArgOfConstructor] requires.
  - In either case a de Bruijn index at or beyond [n + depth] is outside the
    block's context and is refused, as is a top-level [dtype] that is not
    closed at [n]; [tEvar] and [tVar] are refused, a missing declaration is
    refused, and every other occurrence of a function of the block is
    refused.

  [fuel] bounds the depth of the traversal: a fuel of [k] allows [2 ^ k]
  nested steps through the doubling combinator [gfuel], so the number
  [2 ^ k] is never built.  Exhaustion is reported as [OutOfFuel], which is
  never turned into [Reject].  When two parts are both checked, [gr_and]
  lets [OutOfFuel] win over [Reject]; a [Reject] that ends the walk of a
  term early (an escaping index, an illegal call) does not look at the rest
  of that term, so it can stand where the rest would have run out of fuel. *)

Definition gr_prim (f : term -> guard_result) (p : prim_val term) : guard_result :=
  match p with
  | (primArray; primArrayModel ar) =>
    gr_and (f ar.(array_type))
      (gr_and (f ar.(array_default)) (gr_list f ar.(array_value)))
  | _ => Accept
  end.

(** The traversal modes. *)
Inductive gmode :=
| MFixPrefix (k : nat)
  (** entering the binder prefix of a fixpoint body; [k] assumptions are
      still to be crossed before the recursive parameter *)
| MFixBody
  (** inside a fixpoint body: a function of the block may occur, applied to
      enough arguments and on a subterm variable *)
| MCoBody
  (** head position of a cofixpoint body *)
| MCoArg
  (** argument of a constructor application in head position *)
| MNoOcc
  (** no function of the block may occur at all *).

Section Checker.
  (** [lookup] is the environment, [nctx] is [#|Γ|], [nblock] is [#|mfix|]
      and [rargs] the recursive argument positions of the block. *)
  Context (lookup : kername -> option global_decl)
    (nctx : nat) (nblock : nat) (rargs : list nat).

  (** [Some k]: [tRel j] is the [k]-th function of the block. *)
  Definition block_index (nv j : nat) : option nat :=
    if Nat.ltb j nv then None
    else if Nat.ltb j (nv + nblock) then Some (nv + nblock - S j)
    else None.

  Definition rel_in_scope (nv j : nat) : bool := Nat.ltb j (nv + nblock + nctx).

  (** What the traversal knows about a bound variable:
      [GRoot] is the recursive parameter (matchable, not a call argument),
      [GStrict] a branch variable of a match on a [GRoot]/[GStrict] variable
      (a strict subterm), and [GNot] anything else. *)
  Inductive gspec := GNot | GRoot | GStrict.

  Definition spec_of (subs : list gspec) (t : term) : gspec :=
    match t with
    | tRel m => nth m subs GNot
    | _ => GNot
    end.

  (** A valid recursive-call argument: a strict subterm only. *)
  Definition is_subterm_var (subs : list gspec) (t : term) : bool :=
    match spec_of subs t with GStrict => true | _ => false end.

  (** A scrutinee whose branch variables are strict subterms. *)
  Definition is_matchable_var (subs : list gspec) (t : term) : bool :=
    match spec_of subs t with GNot => false | _ => true end.

  (** A branch binder's type is a recursive position when it is an
      application of an inductive of the scrutinee's mutual block [mind].
      [bcontext] is the declaration's [cstr_branch_context] (case
      well-formedness), where the block's inductives appear as [tInd]. *)
  Definition is_rec_arg_type (mind : kername) (ty : term) : bool :=
    match fst (decompose_app ty) with
    | tInd ind' _ => eqb (inductive_mind ind') mind
    | _ => false
    end.

  (** The specs of a branch context's binders, innermost first, as the
      context list is: recursive assumptions get [sub]; non-recursive
      assumptions and [let]s get [GNot]. *)
  Definition branch_specs (mind : kername) (sub : gspec) (ctx : context) : list gspec :=
    map (fun d => match d.(decl_body) with
                  | Some _ => GNot
                  | None => if is_rec_arg_type mind d.(decl_type) then sub else GNot
                  end) ctx.

  (** Only a match on an inductive ([Finite]) type gives subterms: the
      arguments of a coinductive constructor are not smaller. *)
  Definition is_finite_ind (mind : kername) : bool :=
    match lookup mind with
    | Some (InductiveDecl mib) =>
      match mib.(ind_finite) with Finite => true | _ => false end
    | _ => false
    end.

  (** The declaration of constructor [c] of [ind]. *)
  Definition lookup_ctor (ind : inductive) (c : nat)
    : option (mutual_inductive_body * constructor_body) :=
    match lookup (inductive_mind ind) with
    | Some (InductiveDecl mib) =>
      match nth_error mib.(ind_bodies) (inductive_ind ind) with
      | Some idecl => option_map (fun cd => (mib, cd)) (nth_error idecl.(ind_ctors) c)
      | None => None
      end
    | _ => None
    end.

  (** For the assumptions of a constructor's [cstr_args], outermost first:
      [true] at a recursive position.  [cstr_args] lives under the block's
      arities and the parameter context; [i] counts the declarations before
      the current one, so the arities are the indices
      [i + npctx <= j < i + npctx + nind]. *)
  Fixpoint cstr_rec_positions (npctx nind i : nat) (ds : context) : list bool :=
    match ds with
    | [] => []
    | d :: ds =>
      let rest := cstr_rec_positions npctx nind (S i) ds in
      match d.(decl_body) with
      | Some _ => rest
      | None =>
        let r := match fst (decompose_app d.(decl_type)) with
                 | tRel j => Nat.leb (i + npctx) j && Nat.ltb j (i + npctx + nind)
                 | _ => false
                 end in
        r :: rest
      end
    end.

  (** The argument modes of a constructor application: [true] (a function
      of the block may head it) only at a recursive position; parameters and
      every other position get [false]. *)
  Definition cstr_arg_modes (mib : mutual_inductive_body) (cd : constructor_body) : list bool :=
    repeat false mib.(ind_npars) ++
    cstr_rec_positions #|mib.(ind_params)| #|mib.(ind_bodies)| 0 (List.rev cd.(cstr_args)).

  Fixpoint gr_modes (f : bool -> term -> guard_result) (ms : list bool) (l : list term)
    : guard_result :=
    match l with
    | [] => Accept
    | a :: l =>
      match ms with
      | [] => gr_and (f false a) (gr_modes f [] l)
      | m :: ms => gr_and (f m a) (gr_modes f ms l)
      end
    end.

  Definition err_evar := "the guard checker does not handle existential variables".
  Definition err_var := "the guard checker does not handle section variables".
  Definition err_scope := "a de Bruijn index escapes the block's context".
  Definition err_occ := "illegal occurrence of a function of the block".
  Definition err_nargs := "a recursive call is not applied to its recursive argument".
  Definition err_nonsub := "a recursive call is not on a structural subterm".
  Definition err_prefix := "the body of a fixpoint is not a lambda abstraction".
  Definition err_ctor := "a constructor is not declared in the environment".

  (** One step of the traversal; [rec] checks the immediate subterms. *)
  Definition gstep (rec : gmode -> list gspec -> term -> guard_result)
    (md : gmode) (subs : list gspec) (t : term) : guard_result :=
    let nv := #|subs| in
    match md with
    | MFixPrefix k =>
      match t with
      | tLambda _ A b =>
        gr_and (rec MNoOcc subs A)
          (match k with
           | 0 => rec MFixBody (GRoot :: subs) b
           | S k => rec (MFixPrefix k) (GNot :: subs) b
           end)
      | tLetIn _ b B u =>
        gr_and (rec MNoOcc subs b)
          (gr_and (rec MNoOcc subs B)
             (rec (MFixPrefix k) (GNot :: subs) u))
      | _ => Reject err_prefix
      end
    | MCoBody =>
      match t with
      | tLambda _ A b =>
        gr_and (rec MNoOcc subs A) (rec MCoBody (GNot :: subs) b)
      | tLetIn _ b B u =>
        gr_and (rec MNoOcc subs b)
          (gr_and (rec MNoOcc subs B) (rec MCoBody (GNot :: subs) u))
      | _ =>
        let '(hd, args) := decompose_app t in
        match hd with
        | tConstruct ind c _ =>
          match lookup_ctor ind c with
          | Some (mib, cd) =>
            gr_modes (fun m => rec (if m then MCoArg else MNoOcc) subs)
              (cstr_arg_modes mib cd) args
          | None => Reject err_ctor
          end
        | _ => rec MNoOcc subs t
        end
      end
    | MCoArg =>
      let '(hd, args) := decompose_app t in
      match hd with
      | tRel j =>
        if negb (rel_in_scope nv j) then Reject err_scope
        else match block_index nv j with
             | Some _ => gr_list (rec MNoOcc subs) args
             | None => rec MCoBody subs t
             end
      | _ => rec MCoBody subs t
      end
    | MFixBody | MNoOcc =>
      let '(hd, args) := decompose_app t in
      let rest := gr_list (rec md subs) args in
      match hd with
      | tRel j =>
        if negb (rel_in_scope nv j) then Reject err_scope
        else match block_index nv j with
             | None => rest
             | Some k =>
               match md with
               | MFixBody =>
                 let ra := nth k rargs 0 in
                 if Nat.leb #|args| ra then Reject err_nargs
                 else if is_subterm_var subs (nth ra args (tRel 0)) then rest
                 else Reject err_nonsub
               | _ => Reject err_occ
               end
             end
      | tEvar _ _ => Reject err_evar
      | tVar _ => Reject err_var
      | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => rest
      | tProd _ A B =>
        gr_and (rec md subs A)
          (gr_and (rec md (GNot :: subs) B) rest)
      | tLambda _ A b =>
        gr_and (rec md subs A)
          (gr_and (rec md (GNot :: subs) b) rest)
      | tLetIn _ b B u =>
        gr_and (rec md subs b)
          (gr_and (rec md subs B)
             (gr_and (rec md (GNot :: subs) u) rest))
      | tApp _ _ => rest (* unreachable: [decompose_app] peels applications *)
      | tCase ci p c brs =>
        let mind := inductive_mind ci.(ci_ind) in
        let sub := if is_matchable_var subs c && is_finite_ind mind then GStrict else GNot in
        gr_and (gr_list (rec md subs) p.(pparams))
          (gr_and (rec md (List.app (repeat GNot #|p.(pcontext)|) subs) p.(preturn))
             (gr_and (rec md subs c)
                (gr_and
                   (gr_list (fun br =>
                      rec md (List.app (branch_specs mind sub br.(bcontext)) subs) br.(bbody)) brs)
                   rest)))
      | tProj _ c => gr_and (rec md subs c) rest
      | tFix mfix _ | tCoFix mfix _ =>
        gr_and (gr_list (fun dd => rec md subs dd.(dtype)) mfix)
          (gr_and
             (gr_list (fun dd =>
                rec md (List.app (repeat GNot #|mfix|) subs) dd.(dbody)) mfix)
             rest)
      | tPrim p => gr_and (gr_prim (rec md subs) p) rest
      end
    end.

  (** Doubling fuel without materialising [2 ^ n]:
      [gfuel n k] is [gstep] iterated [2 ^ n] times around [k].  The inner
      continuation is kept eta-expanded so that strict (extracted) evaluation
      unfolds only the levels a check actually reaches. *)
  Fixpoint gfuel (n : nat) (k : gmode -> list gspec -> term -> guard_result)
    : gmode -> list gspec -> term -> guard_result :=
    match n with
    | 0 => fun md subs t => gstep k md subs t
    | S n => fun md subs t => gfuel n (fun md' subs' t' => gfuel n k md' subs' t') md subs t
    end.

  (** The inductive of a fixpoint's recursive argument, read from [dtype]
      exactly as [wf_fixpoint]'s [check_one_fix] reads it. *)
  Definition fix_rarg_ind (d : def term) : option inductive :=
    let '(ctx, _) := decompose_prod_assum [] d.(dtype) in
    match nth_error (List.rev (smash_context [] ctx)) d.(rarg) with
    | Some argd =>
      match fst (decompose_app argd.(decl_type)) with
      | tInd ind _ => Some ind
      | _ => None
      end
    | None => None
    end.

  Definition err_notind := "the recursive argument of a fixpoint is not of a declared inductive type".
  Definition err_elim := "the recursive argument's inductive type cannot be eliminated into the fixpoint's sort".

  (** The kernel's [is_allowed_fixpoint], as far as relevance shows it: a
      relevant fixpoint cannot recurse on an inductive whose only allowed
      elimination is into [SProp]. *)
  Definition fix_eliminable (d : def term) : guard_result :=
    match fix_rarg_ind d with
    | Some ind =>
      match lookup (inductive_mind ind) with
      | Some (InductiveDecl mib) =>
        match nth_error mib.(ind_bodies) (inductive_ind ind) with
        | Some idecl =>
          match idecl.(ind_kelim), d.(dname).(binder_relevance) with
          | IntoSProp, Relevant => Reject err_elim
          | _, _ => Accept
          end
        | None => Reject err_notind
        end
      | _ => Reject err_notind
      end
    | None => Reject err_notind
    end.

End Checker.

Definition check_guard_gen (lookup : kername -> option global_decl)
  (retro : Retroknowledge.t) (fuel : nat) (b : FixCoFix) (n : nat)
  (mfix : mfixpoint term) : guard_result :=
  let rargs := map rarg mfix in
  let chk := gfuel lookup n #|mfix| rargs fuel (fun _ _ _ => OutOfFuel) in
  let scoped dd r := if closedn n dd.(dtype) then r else Reject err_scope in
  match b with
  | Fix =>
    gr_list (fun dd =>
      scoped dd (gr_and (fix_eliminable lookup dd) (chk (MFixPrefix dd.(rarg)) [] dd.(dbody)))) mfix
  | CoFix =>
    gr_list (fun dd => scoped dd (chk MCoBody [] dd.(dbody))) mfix
  end.

(** ** Erasure of the data the check does not read

  [strip] removes binder names and universe instances, and collapses every
  predicative sort to one fixed level.  Binder relevance and the sort
  qualities [sProp]/[sSProp] are kept, because the check reads relevance
  ([fix_eliminable]) and a reducing checker reads sort qualities. *)

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
