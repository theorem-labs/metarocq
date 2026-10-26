(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * Weak-head reduction that reports the subterms it discards

  [head_step] performs one weak-head reduction step of a PCUIC term, following
  the head-reduction rules of [red1] ([red_beta], [red_zeta], [red_rel],
  [red_delta], [red_iota], [red_proj], [red_fix], [red_cofix_case],
  [red_cofix_proj]) and the congruences that bring a redex to the head
  (the function of an application, the scrutinee of a match, the argument of
  a projection, the recursive argument of a fixpoint application).

  Each step returns, next to its reduct, the list of the subterms of the
  redex that do not occur in the reduct (the discarded parts), so that a
  caller (the guard checker) can check them before they disappear:

  | redex                                   | discarded parts                     |
  |-----------------------------------------|-------------------------------------|
  | β [(λ x : A. b) a]                      | [A]; [a] if [x] does not occur in [b] |
  | ζ [let x := v : T in b]                 | [T]; [v] if [x] does not occur in [b] |
  | δ local [let] or constant               | none                                |
  | ι [match C pars args with brs]          | [pparams], [preturn], [pars], every other branch body |
  | π [(C pars f_1 ... f_n).j]              | every other element of [pars f_1 ... f_n] |
  | fix / cofix unfolding of [mfix], index [i] | if [dbody] of [i] names no function of [mfix]: every [dtype], every other [dbody]; otherwise none |

  A congruence step reports the discarded parts of the inner step.

  The selected branch of a match is NOT substituted: the reduct is
  [mkApps (it_mkLambda_or_LetIn ctx body) args], a β-redex (with [let]s for
  the [let]s of the branch context), so every constructor argument then goes
  through a β step, which reports it when the branch does not use it.

  [lctx] gives the bodies of the variables bound inside the term being
  checked, innermost first: [nth_error lctx i = Some (Some b)] means [tRel i]
  is a local [let] whose body [b] lives in the context of position [i] (the
  reduct is [lift0 (S i) b]); any other [tRel] is an opaque variable.

  The retroknowledge [retro] is part of the signature for the guard checker;
  PCUIC has no primitive-operation reduction, so it is not consulted. *)

Inductive step_result :=
| Stuck
| Stepped (t' : term) (discarded : list term)
| StepBad (msg : string).

Definition err_const_missing := "head_step: unknown constant".
Definition err_not_const := "head_step: a constant name denotes an inductive declaration".
Definition err_case_ind := "head_step: the constructor of the scrutinee is not of the matched inductive".
Definition err_case_branch := "head_step: the match has no branch for the constructor".
Definition err_case_arity := "head_step: the constructor has the wrong number of arguments for its branch".
Definition err_proj_ctor := "head_step: the projected constructor is not the record's constructor".
Definition err_proj_arg := "head_step: the projected field is out of range".
Definition err_fix_index := "head_step: the fixpoint index is out of range".
Definition err_cofix_index := "head_step: the cofixpoint index is out of range".
Definition err_internal := "head_step: the recursive argument of a fixpoint was not found".

(** [l] without its [i]-th element. *)
Fixpoint except_nth {A} (i : nat) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l, 0 => l
  | x :: l, S i => x :: except_nth i l
  end.

(** [head_ctor t = Some (ind, k, u, args)] iff
    [t = mkApps (tConstruct ind k u) args] (no reduction). *)
Definition head_ctor (t : term) : option (inductive * nat * Instance.t * list term) :=
  let '(hd, args) := decompose_app t in
  match hd with
  | tConstruct ind k u => Some (ind, k, u, args)
  | _ => None
  end.

(** [head_cofix t = Some (mfix, idx, args)] iff
    [t = mkApps (tCoFix mfix idx) args] (no reduction). *)
Definition head_cofix (t : term) : option (mfixpoint term * nat * list term) :=
  let '(hd, args) := decompose_app t in
  match hd with
  | tCoFix mfix idx => Some (mfix, idx, args)
  | _ => None
  end.

(** The parts that the unfolding of definition [i] of [mfix], with body
    [body], discards.  The body lives under the [#|mfix|] binders of the
    block; if it names none of them, the reduct contains no copy of the block,
    so every type and every other body is discarded.  Otherwise the
    substituted block carries all of them and nothing is discarded. *)
Definition block_discarded (mfix : mfixpoint term) (i : nat) (body : term) : list term :=
  if noccur_between 0 #|mfix| body then map dtype mfix ++ map dbody (except_nth i mfix)
  else [].

(** Cofixpoint contraction ([unfold_cofix]) with its discarded parts. *)
Definition contract_cofix (mfix : mfixpoint term) (idx : nat) : option (term * list term) :=
  match nth_error mfix idx with
  | Some d => Some (subst0 (cofix_subst mfix) d.(dbody), block_discarded mfix idx d.(dbody))
  | None => None
  end.

(** ι: [tCase ci p (mkApps (tConstruct ind k u) cargs) brs] applied to [args].
    The side conditions of [red_iota] are checked; bad data gives [StepBad]. *)
Definition iota_step (ci : case_info) (p : predicate term) (brs : list (branch term))
  (ind : inductive) (k : nat) (cargs args : list term) : step_result :=
  if negb (eq_inductive ind ci.(ci_ind)) then StepBad err_case_ind else
  match nth_error brs k with
  | None => StepBad err_case_branch
  | Some br =>
    if negb (Nat.eqb #|cargs| (ci.(ci_npar) + context_assumptions br.(bcontext)))
    then StepBad err_case_arity
    else
      let f := it_mkLambda_or_LetIn (inst_case_branch_context p br) br.(bbody) in
      Stepped (mkApps (mkApps f (skipn ci.(ci_npar) cargs)) args)
        (p.(pparams) ++ p.(preturn) :: firstn ci.(ci_npar) cargs ++ map bbody (except_nth k brs))
  end.

(** π: [tProj pr (mkApps (tConstruct ind k u) cargs)] applied to [args]. *)
Definition proj_step (pr : projection) (ind : inductive) (k : nat) (cargs args : list term)
  : step_result :=
  if negb (eq_inductive ind pr.(proj_ind)) || negb (Nat.eqb k 0) then StepBad err_proj_ctor else
  let n := pr.(proj_npars) + pr.(proj_arg) in
  match nth_error cargs n with
  | Some x => Stepped (mkApps x args) (except_nth n cargs)
  | None => StepBad err_proj_arg
  end.

(** Apply [f] to the reduct of a step. *)
Definition map_stepped (f : term -> term) (r : step_result) : step_result :=
  match r with
  | Stepped t' d => Stepped (f t') d
  | r => r
  end.

(** One weak-head step.  The inner [go] peels the application spine of [t]
    ([args] is the spine, outermost last) and inspects the head; the inner
    [at_arg] walks the spine of [t] again to step the recursive argument of a
    fixpoint, [depth] counting from the outermost argument, so that every
    recursive call is on a subterm of [t]. *)
Fixpoint head_step (lookup : kername -> option global_decl) (retro : Retroknowledge.t)
  (lctx : list (option term)) (t : term) {struct t} : step_result :=
  let fix go (u : term) (args : list term) {struct u} : step_result :=
    match u with
    | tApp f a => go f (a :: args)
    | tLambda _ A b =>
      match args with
      | [] => Stuck
      | a :: rest =>
        Stepped (mkApps (subst10 a b) rest) (A :: if noccur_between 0 1 b then [a] else [])
      end
    | tLetIn _ v T b =>
      Stepped (mkApps (subst10 v b) args) (T :: if noccur_between 0 1 b then [v] else [])
    | tRel i =>
      match nth_error lctx i with
      | Some (Some b) => Stepped (mkApps (lift0 (S i) b) args) []
      | _ => Stuck
      end
    | tConst c ui =>
      match lookup c with
      | Some (ConstantDecl cb) =>
        match cb.(cst_body) with
        | Some b => Stepped (mkApps (subst_instance ui b) args) []
        | None => Stuck
        end
      | Some (InductiveDecl _) => StepBad err_not_const
      | None => StepBad err_const_missing
      end
    | tCase ci p c brs =>
      match head_ctor c with
      | Some (ind, k, _, cargs) => iota_step ci p brs ind k cargs args
      | None =>
        match head_cofix c with
        | Some (mfix, idx, cargs) =>
          match contract_cofix mfix idx with
          | Some (fn, d) => Stepped (mkApps (tCase ci p (mkApps fn cargs) brs) args) d
          | None => StepBad err_cofix_index
          end
        | None => map_stepped (fun c' => mkApps (tCase ci p c' brs) args) (head_step lookup retro lctx c)
        end
      end
    | tProj pr c =>
      match head_ctor c with
      | Some (ind, k, _, cargs) => proj_step pr ind k cargs args
      | None =>
        match head_cofix c with
        | Some (mfix, idx, cargs) =>
          match contract_cofix mfix idx with
          | Some (fn, d) => Stepped (mkApps (tProj pr (mkApps fn cargs)) args) d
          | None => StepBad err_cofix_index
          end
        | None => map_stepped (fun c' => mkApps (tProj pr c') args) (head_step lookup retro lctx c)
        end
      end
    | tFix mfix i =>
      match nth_error mfix i with
      | None => StepBad err_fix_index
      | Some d =>
        match nth_error args d.(rarg) with
        | None => Stuck
        | Some x =>
          match head_ctor x with
          | Some _ =>
            (* [subst0 (fix_subst mfix) d.(dbody)] is the body [unfold_fix] returns. *)
            Stepped (mkApps (subst0 (fix_subst mfix) d.(dbody)) args) (block_discarded mfix i d.(dbody))
          | None =>
            (fix at_arg (v : term) (depth : nat) {struct v} : step_result :=
               match v with
               | tApp f a =>
                 match depth with
                 | 0 => map_stepped (tApp f) (head_step lookup retro lctx a)
                 | S depth => map_stepped (fun f' => tApp f' a) (at_arg f depth)
                 end
               | _ => StepBad err_internal
               end) t (#|args| - S d.(rarg))
          end
        end
      end
    | tVar _ | tEvar _ _ | tSort _ | tProd _ _ _ | tInd _ _ | tConstruct _ _ _
    | tCoFix _ _ | tPrim _ => Stuck
    end
  in go t [].

(** * Iterated head steps with doubling fuel *)

Inductive whd_result :=
| WhdOk (t : term) (discarded : list term)
| WhdBad (msg : string)
| WhdFuel.

Section Whd.
  Context (lookup : kername -> option global_decl) (retro : Retroknowledge.t)
    (lctx : list (option term)).

  (** One [head_step], then the continuation [k] on the reduct; [acc] holds
      the discarded parts of the steps so far, in order. *)
  Definition whd_step (k : list term -> term -> whd_result) (acc : list term) (t : term)
    : whd_result :=
    match head_step lookup retro lctx t with
    | Stuck => WhdOk t acc
    | Stepped t' d => k (List.app acc d) t'
    | StepBad m => WhdBad m
    end.

  (** [whd_fuel n k] is [whd_step] iterated [2 ^ n] times around [k], built
      by doubling as [gfuel] in [PCUICGuardChecker], so [2 ^ n] is never
      materialised; the inner continuation stays eta-expanded. *)
  Fixpoint whd_fuel (n : nat) (k : list term -> term -> whd_result)
    : list term -> term -> whd_result :=
    match n with
    | 0 => fun acc t => whd_step k acc t
    | S n => fun acc t => whd_fuel n (fun acc' t' => whd_fuel n k acc' t') acc t
    end.
End Whd.

(** [whd_steps lookup retro lctx fuel t] calls [head_step] at most [2 ^ fuel]
    times.  It returns [WhdOk t' d] when a call returns [Stuck] on [t'], with
    [d] the discarded parts of all the steps in order; [WhdBad] as soon as a
    step is bad; [WhdFuel] when all [2 ^ fuel] calls stepped. *)
Definition whd_steps (lookup : kername -> option global_decl) (retro : Retroknowledge.t)
  (lctx : list (option term)) (fuel : nat) (t : term) : whd_result :=
  whd_fuel lookup retro lctx fuel (fun _ _ => WhdFuel) [] t.

(** [whd_steps] with every [tRel] opaque. *)
Definition whd_plain (lookup : kername -> option global_decl) (retro : Retroknowledge.t)
  (fuel : nat) (t : term) : whd_result :=
  whd_steps lookup retro [] fuel t.

(** * Head inspection *)

Inductive whd_ctor_result :=
| CtorApp (ind : inductive) (k : nat) (u : Instance.t) (args : list term) (discarded : list term)
  (** the weak-head normal form is [mkApps (tConstruct ind k u) args] *)
| CtorOther (t : term) (discarded : list term)
  (** the weak-head normal form [t] is not a constructor application *)
| CtorBad (msg : string)
| CtorFuel.

(** [whd_head_ctor] reduces only the head of [t] ([whd_steps]; the
    arguments of the head are never reduced) and inspects the head of the
    result with [decompose_app].  [discarded] holds the discarded parts of
    all the steps taken. *)
Definition whd_head_ctor (lookup : kername -> option global_decl) (retro : Retroknowledge.t)
  (lctx : list (option term)) (fuel : nat) (t : term) : whd_ctor_result :=
  match whd_steps lookup retro lctx fuel t with
  | WhdOk t' d =>
    match head_ctor t' with
    | Some (ind, k, u, args) => CtorApp ind k u args d
    | None => CtorOther t' d
    end
  | WhdBad m => CtorBad m
  | WhdFuel => CtorFuel
  end.
