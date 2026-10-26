(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICClosed.

From Stdlib Require Import ssreflect ssrbool.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * An executable guard checker for PCUIC (v0)

  [check_guard_gen] is a total, purely syntactic function that decides a
  (deliberately very restrictive) sufficient condition for a fixpoint or
  cofixpoint block to be guarded.  It is the "v0 rule" of the GuardLane
  design: no reduction at all is performed, so the environment [lookup] and
  the retroknowledge [retro] are not consulted; they are part of the
  signature because the ported checker (S4) replaces the body of this file
  with the full release-7 rule, which does reduce.

  The rule, for a block [mfix] checked in a context of length [n]:

  - Fix: the body of each definition [d] must be a prefix of [rarg d + 1]
    lambda abstractions (interleaved [let]s are allowed and do not count,
    as [rarg] counts assumptions only).  The innermost of those binders is
    the *recursive parameter*; it, and every binder introduced by a branch
    of a [tCase] whose scrutinee is a recursive-parameter variable (or a
    variable already known to be such a branch variable) is a *subterm
    variable*.  Every occurrence of a function of the block must then be of
    the form [mkApps (tRel j) args] with [#|args| > rarg] and
    [nth rarg args] a subterm variable.  Nothing is reduced.
  - CoFix: the body of each definition must be a (possibly empty) prefix of
    lambdas and [let]s followed by a constructor application; a function of
    the block may occur only as the head of an argument of such a
    constructor application, or, recursively, under a nested one.
  - In either case a de Bruijn index at or beyond [n + depth] is outside the
    block's context and is refused (gate 8, N4), as is a top-level [dtype]
    that is not closed at [n]; [tEvar] and [tVar] are
    refused, and every other occurrence of a function of the block is
    refused.

  [fuel] bounds the depth of the traversal: a fuel of [k] allows [2 ^ k]
  nested steps (REPORT §2a.2), through the doubling combinator [gfuel], so
  the number [2 ^ k] is never built.  Exhaustion is reported as [OutOfFuel], which
  is never turned into [Reject] and never masked by one (REPORT §2a.3). *)

Inductive FixCoFix : Type := Fix | CoFix.

Inductive guard_result :=
| Accept
| Reject (msg : string)
| OutOfFuel.

(** [OutOfFuel] dominates, so that a refusal never hides an exhaustion. *)
Definition gr_and (r1 r2 : guard_result) : guard_result :=
  match r1, r2 with
  | OutOfFuel, _ => OutOfFuel
  | _, OutOfFuel => OutOfFuel
  | Reject m, _ => Reject m
  | Accept, r => r
  end.

Fixpoint gr_list {A} (f : A -> guard_result) (l : list A) : guard_result :=
  match l with
  | [] => Accept
  | a :: l => gr_and (f a) (gr_list f l)
  end.

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
  (** [nctx] is [#|Γ|], [nblock] is [#|mfix|] and [rargs] the recursive
      argument positions of the block. *)
  Context (nctx : nat) (nblock : nat) (rargs : list nat).

  (** [Some k]: [tRel j] is the [k]-th function of the block. *)
  Definition block_index (nv j : nat) : option nat :=
    if Nat.ltb j nv then None
    else if Nat.ltb j (nv + nblock) then Some (nv + nblock - S j)
    else None.

  Definition rel_in_scope (nv j : nat) : bool := Nat.ltb j (nv + nblock + nctx).

  Definition is_subterm_var (subs : list bool) (t : term) : bool :=
    match t with
    | tRel m => nth m subs false
    | _ => false
    end.

  Definition err_evar := "the guard checker does not handle existential variables".
  Definition err_var := "the guard checker does not handle section variables".
  Definition err_scope := "a de Bruijn index escapes the block's context".
  Definition err_occ := "illegal occurrence of a function of the block".
  Definition err_nargs := "a recursive call is not applied to its recursive argument".
  Definition err_nonsub := "a recursive call is not on a structural subterm".
  Definition err_prefix := "the body of a fixpoint is not a lambda abstraction".

  (** One step of the traversal; [rec] checks the immediate subterms. *)
  Definition gstep (rec : gmode -> list bool -> term -> guard_result)
    (md : gmode) (subs : list bool) (t : term) : guard_result :=
    let nv := #|subs| in
    match md with
    | MFixPrefix k =>
      match t with
      | tLambda _ A b =>
        gr_and (rec MNoOcc subs A)
          (match k with
           | 0 => rec MFixBody (true :: subs) b
           | S k => rec (MFixPrefix k) (false :: subs) b
           end)
      | tLetIn _ b B u =>
        gr_and (rec MNoOcc subs b)
          (gr_and (rec MNoOcc subs B)
             (rec (MFixPrefix k) (false :: subs) u))
      | _ => Reject err_prefix
      end
    | MCoBody =>
      match t with
      | tLambda _ A b =>
        gr_and (rec MNoOcc subs A) (rec MCoBody (false :: subs) b)
      | tLetIn _ b B u =>
        gr_and (rec MNoOcc subs b)
          (gr_and (rec MNoOcc subs B) (rec MCoBody (false :: subs) u))
      | _ =>
        let '(hd, args) := decompose_app t in
        match hd with
        | tConstruct _ _ _ => gr_list (rec MCoArg subs) args
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
          (gr_and (rec md (false :: subs) B) rest)
      | tLambda _ A b =>
        gr_and (rec md subs A)
          (gr_and (rec md (false :: subs) b) rest)
      | tLetIn _ b B u =>
        gr_and (rec md subs b)
          (gr_and (rec md subs B)
             (gr_and (rec md (false :: subs) u) rest))
      | tApp _ _ => rest (* unreachable: [decompose_app] peels applications *)
      | tCase _ p c brs =>
        let sub := is_subterm_var subs c in
        gr_and (gr_list (rec md subs) p.(pparams))
          (gr_and (rec md (List.app (repeat false #|p.(pcontext)|) subs) p.(preturn))
             (gr_and (rec md subs c)
                (gr_and
                   (gr_list (fun br =>
                      rec md (List.app (repeat sub #|br.(bcontext)|) subs) br.(bbody)) brs)
                   rest)))
      | tProj _ c => gr_and (rec md subs c) rest
      | tFix mfix _ | tCoFix mfix _ =>
        gr_and (gr_list (fun dd => rec md subs dd.(dtype)) mfix)
          (gr_and
             (gr_list (fun dd =>
                rec md (List.app (repeat false #|mfix|) subs) dd.(dbody)) mfix)
             rest)
      | tPrim p => gr_and (gr_prim (rec md subs) p) rest
      end
    end.

  (** Doubling fuel without materialising [2 ^ n] (REPORT §2a.2):
      [gfuel n k] is [gstep] iterated [2 ^ n] times around [k].  The inner
      continuation is kept eta-expanded so that strict (extracted) evaluation
      unfolds only the levels a check actually reaches. *)
  Fixpoint gfuel (n : nat) (k : gmode -> list bool -> term -> guard_result)
    : gmode -> list bool -> term -> guard_result :=
    match n with
    | 0 => fun md subs t => gstep k md subs t
    | S n => fun md subs t => gfuel n (fun md' subs' t' => gfuel n k md' subs' t') md subs t
    end.

End Checker.

Definition check_guard_gen (lookup : kername -> option global_decl)
  (retro : Retroknowledge.t) (fuel : nat) (b : FixCoFix) (n : nat)
  (mfix : mfixpoint term) : guard_result :=
  let rargs := map rarg mfix in
  let chk := gfuel n #|mfix| rargs fuel (fun _ _ _ => OutOfFuel) in
  let scoped dd r := if closedn n dd.(dtype) then r else Reject err_scope in
  match b with
  | Fix =>
    gr_list (fun dd => scoped dd (chk (MFixPrefix dd.(rarg)) [] dd.(dbody))) mfix
  | CoFix =>
    gr_list (fun dd => scoped dd (chk MCoBody [] dd.(dbody))) mfix
  end.

(** v0 never consults the environment. *)
Lemma check_guard_gen_lookup_ext (l l' : kername -> option global_decl) r f b n m :
  (forall k, l k = l' k) ->
  check_guard_gen l r f b n m = check_guard_gen l' r f b n m.
Proof. reflexivity. Qed.

(** ** Erasure of the data the check does not read

  [strip] removes binder names and universe instances, and collapses every
  predicative sort to one fixed level.  Binder relevance and the sort
  qualities [sProp]/[sSProp] are kept, because the ported checker reads them
  (gate-1 N3). *)

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
